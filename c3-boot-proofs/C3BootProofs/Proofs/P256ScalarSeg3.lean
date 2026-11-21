import C3BootProofs.Proofs.P256ScalarDecode

/-! # P-256's `Scalar::mul`, segments 12 to 15

Each theorem steps 40 instructions. `scripts/gen-p256-scalar.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g12 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v4 v7 v12 v17 v18 v19 v171 v300 v306 v392 v397 v410 v424 v431 v438 v444 v447 v449 v451 v454 v459 v462 v465 v470 v474 v476 v477 v478 v479 : Word}
    (s : St Mi B n 0x64A (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
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
    (q5 : reg n (5 : Fin 32) = v454)
    (q6 : reg n (6 : Fin 32) = v12)
    (q7 : reg n (7 : Fin 32) = v459)
    (q8 : reg n (8 : Fin 32) = v462)
    (q9 : reg n (9 : Fin 32) = v449)
    (q10 : reg n a0 = v474)
    (q11 : reg n a1 = v470)
    (q12 : reg n a2 = v478)
    (q13 : reg n a3 = v477)
    (q14 : reg n a4 = v479)
    (q15 : reg n a5 = v476)
    (q16 : reg n a6 = v18)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v451)
    (q19 : reg n (19 : Fin 32) = v465)
    (q20 : reg n (20 : Fin 32) = v397)
    (q21 : reg n (21 : Fin 32) = v438)
    (q22 : reg n (22 : Fin 32) = v444)
    (q23 : reg n (23 : Fin 32) = v431)
    (q24 : reg n (24 : Fin 32) = v410)
    (q25 : reg n (25 : Fin 32) = v424)
    (q26 : reg n (26 : Fin 32) = v306)
    (q27 : reg n (27 : Fin 32) = v392)
    (q28 : reg n (28 : Fin 32) = v447)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v480 v481 v482 v483 v484 v485 v486 v487 v488 v489 v490 v491 v492 v493 v494 v495 v496 v497 v498 v499 v500 v501 v502 v503 v504 v505 v506 v507 v508 v509 v510 v511 v512 v513 v514 v515 v516 v517 v518 v519 : Word),
      Steps n n' ∧
      St M' B n' 0x6D4 (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v300 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v454 ∧
      reg n' (6 : Fin 32) = v513 ∧
      reg n' (7 : Fin 32) = v506 ∧
      reg n' (8 : Fin 32) = v462 ∧
      reg n' (9 : Fin 32) = v449 ∧
      reg n' a0 = v474 ∧
      reg n' a1 = v518 ∧
      reg n' a2 = v505 ∧
      reg n' a3 = v511 ∧
      reg n' a4 = v512 ∧
      reg n' a5 = v515 ∧
      reg n' a6 = v519 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v451 ∧
      reg n' (19 : Fin 32) = v465 ∧
      reg n' (20 : Fin 32) = v488 ∧
      reg n' (21 : Fin 32) = v516 ∧
      reg n' (22 : Fin 32) = v444 ∧
      reg n' (23 : Fin 32) = v510 ∧
      reg n' (24 : Fin 32) = v509 ∧
      reg n' (25 : Fin 32) = v480 ∧
      reg n' (26 : Fin 32) = v306 ∧
      reg n' (27 : Fin 32) = v392 ∧
      reg n' (28 : Fin 32) = v500 ∧
      reg n' (29 : Fin 32) = v494 ∧
      reg n' (30 : Fin 32) = v19 ∧
      reg n' (31 : Fin 32) = v517 ∧
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
      aluEval .add v478 v477 = v480 ∧
      aluEval .add v470 v479 = v481 ∧
      aluEval .sltu v480 v478 = v482 ∧
      aluEval .sub v438 v171 = v483 ∧
      aluEval .mulhu v171 v18 = v484 ∧
      aluEval .add v481 v482 = v485 ∧
      aluEval .sltu v483 v438 = v486 ∧
      aluEval .add v486 v476 = v487 ∧
      aluEval .add v483 v485 = v488 ∧
      aluEval .sltu v488 v483 = v489 ∧
      aluEval .add v171 v171 = v490 ∧
      aluEval .add v487 v489 = v491 ∧
      aluEval .sub v444 v490 = v492 ∧
      aluEval .sltu v492 v444 = v493 ∧
      aluEval .add v492 v491 = v494 ∧
      aluEval .add v493 v484 = v495 ∧
      aluEval .sltu v494 v492 = v496 ∧
      aluEval .add v496 v495 = v497 ∧
      aluEval .sub v449 v171 = v498 ∧
      aluEval .sltu v498 v449 = v499 ∧
      aluEval .add v498 v497 = v500 ∧
      aluEval .add v499 v476 = v501 ∧
      aluEval .sltu v500 v498 = v502 ∧
      aluEval .sltu v459 v451 = v503 ∧
      aluEval .add v502 v501 = v504 ∧
      aluEval .add v503 v454 = v505 ∧
      aluEval .add v459 v504 = v506 ∧
      (0xFC632000 : Word) = v507 ∧
      (0xF3B9D000 : Word) = v508 ∧
      aluEval .add v507 0x551 = v509 ∧
      aluEval .add v508 0xFFFFFAC2 = v510 ∧
      aluEval .mulhu v465 v509 = v511 ∧
      aluEval .mul v465 v510 = v512 ∧
      aluEval .sltu v506 v504 = v513 ∧
      (0xA717A000 : Word) = v514 ∧
      aluEval .mulhu v465 v510 = v515 ∧
      aluEval .add v514 0xFFFFFE84 = v516 ∧
      aluEval .add v171 v505 = v517 ∧
      aluEval .mul v465 v516 = v518 ∧
      aluEval .sltu v517 v505 = v519 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n480, v480, d480, hv480, u480⟩ := s.aluG hc psm_at_64a (off' := 0x64E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv480
  obtain ⟨n481, v481, d481, hv481, u481⟩ := u480.aluG hc psm_at_64e (off' := 0x650) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv481
  obtain ⟨n482, v482, d482, hv482, u482⟩ := u481.aluG hc psm_at_650 (off' := 0x654) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv482
  obtain ⟨n483, v483, d483, hv483, u483⟩ := u482.aluG hc psm_at_654 (off' := 0x658) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv483
  obtain ⟨n484, v484, d484, hv484, u484⟩ := u483.aluG hc psm_at_658 (off' := 0x65C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv484
  obtain ⟨n485, v485, d485, hv485, u485⟩ := u484.aluG hc psm_at_65c (off' := 0x65E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv485
  obtain ⟨n486, v486, d486, hv486, u486⟩ := u485.aluG hc psm_at_65e (off' := 0x662) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv486
  obtain ⟨n487, v487, d487, hv487, u487⟩ := u486.aluG hc psm_at_662 (off' := 0x664) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv487
  obtain ⟨n488, v488, d488, hv488, u488⟩ := u487.aluG hc psm_at_664 (off' := 0x668) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv488
  obtain ⟨n489, v489, d489, hv489, u489⟩ := u488.aluG hc psm_at_668 (off' := 0x66C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv489
  obtain ⟨n490, v490, d490, hv490, u490⟩ := u489.aluG hc psm_at_66c (off' := 0x670) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv490
  obtain ⟨n491, v491, d491, hv491, u491⟩ := u490.aluG hc psm_at_670 (off' := 0x672) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv491
  obtain ⟨n492, v492, d492, hv492, u492⟩ := u491.aluG hc psm_at_672 (off' := 0x676) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv492
  obtain ⟨n493, v493, d493, hv493, u493⟩ := u492.aluG hc psm_at_676 (off' := 0x67A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv493
  obtain ⟨n494, v494, d494, hv494, u494⟩ := u493.aluG hc psm_at_67a (off' := 0x67E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv494
  obtain ⟨n495, v495, d495, hv495, u495⟩ := u494.aluG hc psm_at_67e (off' := 0x680) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv495
  obtain ⟨n496, v496, d496, hv496, u496⟩ := u495.aluG hc psm_at_680 (off' := 0x684) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv496
  obtain ⟨n497, v497, d497, hv497, u497⟩ := u496.aluG hc psm_at_684 (off' := 0x686) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv497
  obtain ⟨n498, v498, d498, hv498, u498⟩ := u497.aluG hc psm_at_686 (off' := 0x68A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv498
  obtain ⟨n499, v499, d499, hv499, u499⟩ := u498.aluG hc psm_at_68a (off' := 0x68E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv499
  obtain ⟨n500, v500, d500, hv500, u500⟩ := u499.aluG hc psm_at_68e (off' := 0x692) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv500
  obtain ⟨n501, v501, d501, hv501, u501⟩ := u500.aluG hc psm_at_692 (off' := 0x694) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv501
  obtain ⟨n502, v502, d502, hv502, u502⟩ := u501.aluG hc psm_at_694 (off' := 0x698) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv502
  obtain ⟨n503, v503, d503, hv503, u503⟩ := u502.aluG hc psm_at_698 (off' := 0x69C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv503
  obtain ⟨n504, v504, d504, hv504, u504⟩ := u503.aluG hc psm_at_69c (off' := 0x69E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv504
  obtain ⟨n505, v505, d505, hv505, u505⟩ := u504.aluG hc psm_at_69e (off' := 0x6A0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv505
  obtain ⟨n506, v506, d506, hv506, u506⟩ := u505.aluG hc psm_at_6a0 (off' := 0x6A2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv506
  obtain ⟨n507, v507, d507, hv507, u507⟩ := u506.luiG hc psm_at_6a2 (off' := 0x6A6) (by decide)
  obtain ⟨n508, v508, d508, hv508, u508⟩ := u507.luiG hc psm_at_6a6 (off' := 0x6AA) (by decide)
  obtain ⟨n509, v509, d509, hv509, u509⟩ := u508.aluImmG hc psm_at_6aa (off' := 0x6AE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv509
  obtain ⟨n510, v510, d510, hv510, u510⟩ := u509.aluImmG hc psm_at_6ae (off' := 0x6B2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv510
  obtain ⟨n511, v511, d511, hv511, u511⟩ := u510.aluG hc psm_at_6b2 (off' := 0x6B6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv511
  obtain ⟨n512, v512, d512, hv512, u512⟩ := u511.aluG hc psm_at_6b6 (off' := 0x6BA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv512
  obtain ⟨n513, v513, d513, hv513, u513⟩ := u512.aluG hc psm_at_6ba (off' := 0x6BE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv513
  obtain ⟨n514, v514, d514, hv514, u514⟩ := u513.luiG hc psm_at_6be (off' := 0x6C2) (by decide)
  obtain ⟨n515, v515, d515, hv515, u515⟩ := u514.aluG hc psm_at_6c2 (off' := 0x6C6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv515
  obtain ⟨n516, v516, d516, hv516, u516⟩ := u515.aluImmG hc psm_at_6c6 (off' := 0x6CA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv516
  obtain ⟨n517, v517, d517, hv517, u517⟩ := u516.aluG hc psm_at_6ca (off' := 0x6CC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv517
  obtain ⟨n518, v518, d518, hv518, u518⟩ := u517.aluG hc psm_at_6cc (off' := 0x6D0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv518
  obtain ⟨n519, v519, d519, hv519, u519⟩ := u518.aluG hc psm_at_6d0 (off' := 0x6D4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv519
  have qo1 : reg n519 ra = v300 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n519 sp = F := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n519 (3 : Fin 32) = G3 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n519 (4 : Fin 32) = G4 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n519 (5 : Fin 32) = v454 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n519 (6 : Fin 32) = v513 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n519 (7 : Fin 32) = v506 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n519 (8 : Fin 32) = v462 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n519 (9 : Fin 32) = v449 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n519 a0 = v474 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n519 a1 = v518 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n519 a2 = v505 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n519 a3 = v511 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n519 a4 = v512 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n519 a5 = v515 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n519 a6 = v519 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n519 a7 = v17 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n519 (18 : Fin 32) = v451 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n519 (19 : Fin 32) = v465 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n519 (20 : Fin 32) = v488 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n519 (21 : Fin 32) = v516 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n519 (22 : Fin 32) = v444 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n519 (23 : Fin 32) = v510 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n519 (24 : Fin 32) = v509 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n519 (25 : Fin 32) = v480 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n519 (26 : Fin 32) = v306 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n519 (27 : Fin 32) = v392 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n519 (28 : Fin 32) = v500 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n519 (29 : Fin 32) = v494 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n519 (30 : Fin 32) = v19 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n519 (31 : Fin 32) = v517 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
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
  exact ⟨n519, Mi, v480, v481, v482, v483, v484, v485, v486, v487, v488, v489, v490, v491, v492, v493, v494, v495, v496, v497, v498, v499, v500, v501, v502, v503, v504, v505, v506, v507, v508, v509, v510, v511, v512, v513, v514, v515, v516, v517, v518, v519, (.cons d480 (.cons d481 (.cons d482 (.cons d483 (.cons d484 (.cons d485 (.cons d486 (.cons d487 (.cons d488 (.cons d489 (.cons d490 (.cons d491 (.cons d492 (.cons d493 (.cons d494 (.cons d495 (.cons d496 (.cons d497 (.cons d498 (.cons d499 (.cons d500 (.cons d501 (.cons d502 (.cons d503 (.cons d504 (.cons d505 (.cons d506 (.cons d507 (.cons d508 (.cons d509 (.cons d510 (.cons d511 (.cons d512 (.cons d513 (.cons d514 (.cons d515 (.cons d516 (.cons d517 (.cons d518 (.single d519)))))))))))))))))))))))))))))))))))))))), u519.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv480, hv481, hv482, hv483, hv484, hv485, hv486, hv487, hv488, hv489, hv490, hv491, hv492, hv493, hv494, hv495, hv496, hv497, hv498, hv499, hv500, hv501, hv502, hv503, hv504, hv505, hv506, hv507, hv508, hv509, hv510, hv511, hv512, hv513, hv514, hv515, hv516, hv517, hv518, hv519⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g13 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v7 v17 v19 v300 v306 v392 v444 v449 v451 v454 v462 v465 v474 v480 v488 v494 v500 v505 v506 v509 v510 v511 v512 v513 v515 v516 v517 v518 v519 : Word}
    (s : St Mi B n 0x6D4 (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
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
    (q5 : reg n (5 : Fin 32) = v454)
    (q6 : reg n (6 : Fin 32) = v513)
    (q7 : reg n (7 : Fin 32) = v506)
    (q8 : reg n (8 : Fin 32) = v462)
    (q9 : reg n (9 : Fin 32) = v449)
    (q10 : reg n a0 = v474)
    (q11 : reg n a1 = v518)
    (q12 : reg n a2 = v505)
    (q13 : reg n a3 = v511)
    (q14 : reg n a4 = v512)
    (q15 : reg n a5 = v515)
    (q16 : reg n a6 = v519)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v451)
    (q19 : reg n (19 : Fin 32) = v465)
    (q20 : reg n (20 : Fin 32) = v488)
    (q21 : reg n (21 : Fin 32) = v516)
    (q22 : reg n (22 : Fin 32) = v444)
    (q23 : reg n (23 : Fin 32) = v510)
    (q24 : reg n (24 : Fin 32) = v509)
    (q25 : reg n (25 : Fin 32) = v480)
    (q26 : reg n (26 : Fin 32) = v306)
    (q27 : reg n (27 : Fin 32) = v392)
    (q28 : reg n (28 : Fin 32) = v500)
    (q29 : reg n (29 : Fin 32) = v494)
    (q30 : reg n (30 : Fin 32) = v19)
    (q31 : reg n (31 : Fin 32) = v517)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v520 v521 v522 v523 v524 v525 v526 v527 v528 v529 v530 v531 v532 v533 v534 v535 v536 v537 v538 v539 v540 v541 v542 v543 v544 v546 v547 v548 v549 v550 v551 v552 v553 v554 v555 v556 v557 v558 v559 : Word),
      Steps n n' ∧
      St M' B n' 0x756 (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v300 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v554 ∧
      reg n' (6 : Fin 32) = v525 ∧
      reg n' (7 : Fin 32) = v506 ∧
      reg n' (8 : Fin 32) = v542 ∧
      reg n' (9 : Fin 32) = v559 ∧
      reg n' a0 = v474 ∧
      reg n' a1 = v553 ∧
      reg n' a2 = v535 ∧
      reg n' a3 = v546 ∧
      reg n' a4 = v555 ∧
      reg n' a5 = v556 ∧
      reg n' a6 = v541 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v538 ∧
      reg n' (19 : Fin 32) = v465 ∧
      reg n' (20 : Fin 32) = v488 ∧
      reg n' (21 : Fin 32) = v516 ∧
      reg n' (22 : Fin 32) = v522 ∧
      reg n' (23 : Fin 32) = v510 ∧
      reg n' (24 : Fin 32) = v509 ∧
      reg n' (25 : Fin 32) = v480 ∧
      reg n' (26 : Fin 32) = v549 ∧
      reg n' (27 : Fin 32) = v392 ∧
      reg n' (28 : Fin 32) = v500 ∧
      reg n' (29 : Fin 32) = v494 ∧
      reg n' (30 : Fin 32) = v558 ∧
      reg n' (31 : Fin 32) = v534 ∧
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
      (0xBCE70000 : Word) = v520 ∧
      aluEval .mulhu v465 v516 = v521 ∧
      aluEval .add v520 0xFFFFFAAD = v522 ∧
      aluEval .add v512 v511 = v523 ∧
      aluEval .mul v465 v522 = v524 ∧
      aluEval .add v513 v517 = v525 ∧
      aluEval .sltu v523 v511 = v526 ∧
      aluEval .add v526 v515 = v527 ∧
      aluEval .mulhu v465 v522 = v528 ∧
      aluEval .sltu v525 v517 = v529 ∧
      aluEval .add v518 v527 = v530 ∧
      aluEval .sltu v530 v527 = v531 ∧
      aluEval .mul v474 v509 = v532 ∧
      aluEval .add v531 v521 = v533 ∧
      aluEval .mulhu v465 v17 = v534 ∧
      aluEval .add v524 v533 = v535 ∧
      aluEval .mul v474 v510 = v536 ∧
      aluEval .sltu v535 v533 = v537 ∧
      aluEval .mulhu v474 v509 = v538 ∧
      aluEval .add v537 v528 = v539 ∧
      aluEval .mulhu v474 v510 = v540 ∧
      aluEval .add v519 v529 = v541 ∧
      aluEval .sub v539 v465 = v542 ∧
      aluEval .sltu v542 v539 = v543 ∧
      aluEval .add v532 v523 = v544 ∧
      aluEval .add v543 v534 = v546 ∧
      aluEval .sltu v544 v523 = v547 ∧
      aluEval .add v536 v530 = v548 ∧
      aluEval .mul v474 v516 = v549 ∧
      aluEval .add v547 v538 = v550 ∧
      aluEval .sltu v548 v530 = v551 ∧
      aluEval .add v540 v551 = v552 ∧
      aluEval .mulhu v474 v516 = v553 ∧
      aluEval .add v548 v550 = v554 ∧
      aluEval .mul v474 v522 = v555 ∧
      aluEval .sub v546 v465 = v556 ∧
      aluEval .sltu v554 v548 = v557 ∧
      aluEval .add v552 v557 = v558 ∧
      aluEval .mulhu v474 v522 = v559 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n520, v520, d520, hv520, u520⟩ := s.luiG hc psm_at_6d4 (off' := 0x6D8) (by decide)
  obtain ⟨n521, v521, d521, hv521, u521⟩ := u520.aluG hc psm_at_6d8 (off' := 0x6DC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv521
  obtain ⟨n522, v522, d522, hv522, u522⟩ := u521.aluImmG hc psm_at_6dc (off' := 0x6E0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv522
  obtain ⟨n523, v523, d523, hv523, u523⟩ := u522.aluG hc psm_at_6e0 (off' := 0x6E2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv523
  obtain ⟨n524, v524, d524, hv524, u524⟩ := u523.aluG hc psm_at_6e2 (off' := 0x6E6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv524
  obtain ⟨n525, v525, d525, hv525, u525⟩ := u524.aluG hc psm_at_6e6 (off' := 0x6E8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv525
  obtain ⟨n526, v526, d526, hv526, u526⟩ := u525.aluG hc psm_at_6e8 (off' := 0x6EC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv526
  obtain ⟨n527, v527, d527, hv527, u527⟩ := u526.aluG hc psm_at_6ec (off' := 0x6EE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv527
  obtain ⟨n528, v528, d528, hv528, u528⟩ := u527.aluG hc psm_at_6ee (off' := 0x6F2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv528
  obtain ⟨n529, v529, d529, hv529, u529⟩ := u528.aluG hc psm_at_6f2 (off' := 0x6F6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv529
  obtain ⟨n530, v530, d530, hv530, u530⟩ := u529.aluG hc psm_at_6f6 (off' := 0x6F8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv530
  obtain ⟨n531, v531, d531, hv531, u531⟩ := u530.aluG hc psm_at_6f8 (off' := 0x6FC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv531
  obtain ⟨n532, v532, d532, hv532, u532⟩ := u531.aluG hc psm_at_6fc (off' := 0x700) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv532
  obtain ⟨n533, v533, d533, hv533, u533⟩ := u532.aluG hc psm_at_700 (off' := 0x702) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv533
  obtain ⟨n534, v534, d534, hv534, u534⟩ := u533.aluG hc psm_at_702 (off' := 0x706) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv534
  obtain ⟨n535, v535, d535, hv535, u535⟩ := u534.aluG hc psm_at_706 (off' := 0x708) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv535
  obtain ⟨n536, v536, d536, hv536, u536⟩ := u535.aluG hc psm_at_708 (off' := 0x70C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv536
  obtain ⟨n537, v537, d537, hv537, u537⟩ := u536.aluG hc psm_at_70c (off' := 0x710) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv537
  obtain ⟨n538, v538, d538, hv538, u538⟩ := u537.aluG hc psm_at_710 (off' := 0x714) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv538
  obtain ⟨n539, v539, d539, hv539, u539⟩ := u538.aluG hc psm_at_714 (off' := 0x716) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv539
  obtain ⟨n540, v540, d540, hv540, u540⟩ := u539.aluG hc psm_at_716 (off' := 0x71A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv540
  obtain ⟨n541, v541, d541, hv541, u541⟩ := u540.aluG hc psm_at_71a (off' := 0x71C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv541
  obtain ⟨n542, v542, d542, hv542, u542⟩ := u541.aluG hc psm_at_71c (off' := 0x720) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv542
  obtain ⟨n543, v543, d543, hv543, u543⟩ := u542.aluG hc psm_at_720 (off' := 0x724) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv543
  obtain ⟨n544, v544, d544, hv544, u544⟩ := u543.aluG hc psm_at_724 (off' := 0x726) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv544
  obtain ⟨n545, d545, u545⟩ := u544.swG hc psm_at_726 (off' := 0x728) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 28) (by decide)) (a := F + 0x1C) (v := v544)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M545, hM545⟩ : ∃ M', memStore32 Mi (F + 0x1C) v544 = M' := ⟨_, rfl⟩
  rw [hM545] at u545
  have hc545 : CodeIn M545 B p256ScalarMulCode := by rw [← hM545]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr545 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M545 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM545, memStore32_get_sep (frm_sep' hx1 (by decide)), fr x hx1 hx2 hx3]
  obtain ⟨n546, v546, d546, hv546, u546⟩ := u545.aluG hc545 psm_at_728 (off' := 0x72A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv546
  obtain ⟨n547, v547, d547, hv547, u547⟩ := u546.aluG hc545 psm_at_72a (off' := 0x72E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv547
  obtain ⟨n548, v548, d548, hv548, u548⟩ := u547.aluG hc545 psm_at_72e (off' := 0x730) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv548
  obtain ⟨n549, v549, d549, hv549, u549⟩ := u548.aluG hc545 psm_at_730 (off' := 0x734) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv549
  obtain ⟨n550, v550, d550, hv550, u550⟩ := u549.aluG hc545 psm_at_734 (off' := 0x736) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv550
  obtain ⟨n551, v551, d551, hv551, u551⟩ := u550.aluG hc545 psm_at_736 (off' := 0x73A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv551
  obtain ⟨n552, v552, d552, hv552, u552⟩ := u551.aluG hc545 psm_at_73a (off' := 0x73C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv552
  obtain ⟨n553, v553, d553, hv553, u553⟩ := u552.aluG hc545 psm_at_73c (off' := 0x740) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv553
  obtain ⟨n554, v554, d554, hv554, u554⟩ := u553.aluG hc545 psm_at_740 (off' := 0x744) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv554
  obtain ⟨n555, v555, d555, hv555, u555⟩ := u554.aluG hc545 psm_at_744 (off' := 0x748) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv555
  obtain ⟨n556, v556, d556, hv556, u556⟩ := u555.aluG hc545 psm_at_748 (off' := 0x74C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv556
  obtain ⟨n557, v557, d557, hv557, u557⟩ := u556.aluG hc545 psm_at_74c (off' := 0x750) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv557
  obtain ⟨n558, v558, d558, hv558, u558⟩ := u557.aluG hc545 psm_at_750 (off' := 0x752) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv558
  obtain ⟨n559, v559, d559, hv559, u559⟩ := u558.aluG hc545 psm_at_752 (off' := 0x756) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv559
  have qo1 : reg n559 ra = v300 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n559 sp = F := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n559 (3 : Fin 32) = G3 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n559 (4 : Fin 32) = G4 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n559 (5 : Fin 32) = v554 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n559 (6 : Fin 32) = v525 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n559 (7 : Fin 32) = v506 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n559 (8 : Fin 32) = v542 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n559 (9 : Fin 32) = v559 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n559 a0 = v474 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n559 a1 = v553 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n559 a2 = v535 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n559 a3 = v546 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n559 a4 = v555 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n559 a5 = v556 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n559 a6 = v541 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n559 a7 = v17 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n559 (18 : Fin 32) = v538 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n559 (19 : Fin 32) = v465 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n559 (20 : Fin 32) = v488 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n559 (21 : Fin 32) = v516 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n559 (22 : Fin 32) = v522 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n559 (23 : Fin 32) = v510 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n559 (24 : Fin 32) = v509 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n559 (25 : Fin 32) = v480 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n559 (26 : Fin 32) = v549 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n559 (27 : Fin 32) = v392 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n559 (28 : Fin 32) = v500 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n559 (29 : Fin 32) = v494 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n559 (30 : Fin 32) = v558 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n559 (31 : Fin 32) = v534 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so1C : memLoad32 M545 (F + 0x1C) = v544 := by
    rw [← hM545, memLoad32_store32_same]
  have so20 : memLoad32 M545 (F + 0x20) = v7 := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x20) 4 from sep_offsets F (c := 28) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), sl20]
  have so24 : memLoad32 M545 (F + 0x24) = v0 := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x24) 4 from sep_offsets F (c := 28) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), sl24]
  have so28 : memLoad32 M545 (F + 0x28) = outp := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x28) 4 from sep_offsets F (c := 28) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), sl28]
  have so2C : memLoad32 M545 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x2C) 4 from sep_offsets F (c := 28) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), sl2C]
  have so30 : memLoad32 M545 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x30) 4 from sep_offsets F (c := 28) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), sl30]
  have so34 : memLoad32 M545 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x34) 4 from sep_offsets F (c := 28) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), sl34]
  have so38 : memLoad32 M545 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x38) 4 from sep_offsets F (c := 28) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), sl38]
  have so3C : memLoad32 M545 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x3C) 4 from sep_offsets F (c := 28) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), sl3C]
  have so40 : memLoad32 M545 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x40) 4 from sep_offsets F (c := 28) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), sl40]
  have so44 : memLoad32 M545 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x44) 4 from sep_offsets F (c := 28) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), sl44]
  have so48 : memLoad32 M545 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x48) 4 from sep_offsets F (c := 28) (n := 4) (d := 72) (k := 4) (by decide) (by decide) (by decide)), sl48]
  have so4C : memLoad32 M545 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x4C) 4 from sep_offsets F (c := 28) (n := 4) (d := 76) (k := 4) (by decide) (by decide) (by decide)), sl4C]
  have so50 : memLoad32 M545 (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x50) 4 from sep_offsets F (c := 28) (n := 4) (d := 80) (k := 4) (by decide) (by decide) (by decide)), sl50]
  have so54 : memLoad32 M545 (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x54) 4 from sep_offsets F (c := 28) (n := 4) (d := 84) (k := 4) (by decide) (by decide) (by decide)), sl54]
  have so58 : memLoad32 M545 (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x58) 4 from sep_offsets F (c := 28) (n := 4) (d := 88) (k := 4) (by decide) (by decide) (by decide)), sl58]
  have so5C : memLoad32 M545 (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x5C) 4 from sep_offsets F (c := 28) (n := 4) (d := 92) (k := 4) (by decide) (by decide) (by decide)), sl5C]
  have so60 : memLoad32 M545 (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x60) 4 from sep_offsets F (c := 28) (n := 4) (d := 96) (k := 4) (by decide) (by decide) (by decide)), sl60]
  have so64 : memLoad32 M545 (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x64) 4 from sep_offsets F (c := 28) (n := 4) (d := 100) (k := 4) (by decide) (by decide) (by decide)), sl64]
  have so68 : memLoad32 M545 (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x68) 4 from sep_offsets F (c := 28) (n := 4) (d := 104) (k := 4) (by decide) (by decide) (by decide)), sl68]
  have so6C : memLoad32 M545 (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x6C) 4 from sep_offsets F (c := 28) (n := 4) (d := 108) (k := 4) (by decide) (by decide) (by decide)), sl6C]
  have so70 : memLoad32 M545 (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x70) 4 from sep_offsets F (c := 28) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), sl70]
  have so74 : memLoad32 M545 (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x74) 4 from sep_offsets F (c := 28) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), sl74]
  have so78 : memLoad32 M545 (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x78) 4 from sep_offsets F (c := 28) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), sl78]
  have so7C : memLoad32 M545 (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x7C) 4 from sep_offsets F (c := 28) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), sl7C]
  have so80 : memLoad32 M545 (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x80) 4 from sep_offsets F (c := 28) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), sl80]
  have so84 : memLoad32 M545 (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x84) 4 from sep_offsets F (c := 28) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), sl84]
  have so88 : memLoad32 M545 (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x88) 4 from sep_offsets F (c := 28) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88]
  have so8C : memLoad32 M545 (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x8C) 4 from sep_offsets F (c := 28) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), sl8C]
  have so90 : memLoad32 M545 (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x90) 4 from sep_offsets F (c := 28) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), sl90]
  have so94 : memLoad32 M545 (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x94) 4 from sep_offsets F (c := 28) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), sl94]
  have so98 : memLoad32 M545 (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x98) 4 from sep_offsets F (c := 28) (n := 4) (d := 152) (k := 4) (by decide) (by decide) (by decide)), sl98]
  have so9C : memLoad32 M545 (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [← hM545, memLoad32_store32_sep (show Sep (F + 0x1C) 4 (F + 0x9C) 4 from sep_offsets F (c := 28) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), sl9C]
  exact ⟨n559, M545, v520, v521, v522, v523, v524, v525, v526, v527, v528, v529, v530, v531, v532, v533, v534, v535, v536, v537, v538, v539, v540, v541, v542, v543, v544, v546, v547, v548, v549, v550, v551, v552, v553, v554, v555, v556, v557, v558, v559, (.cons d520 (.cons d521 (.cons d522 (.cons d523 (.cons d524 (.cons d525 (.cons d526 (.cons d527 (.cons d528 (.cons d529 (.cons d530 (.cons d531 (.cons d532 (.cons d533 (.cons d534 (.cons d535 (.cons d536 (.cons d537 (.cons d538 (.cons d539 (.cons d540 (.cons d541 (.cons d542 (.cons d543 (.cons d544 (.cons d545 (.cons d546 (.cons d547 (.cons d548 (.cons d549 (.cons d550 (.cons d551 (.cons d552 (.cons d553 (.cons d554 (.cons d555 (.cons d556 (.cons d557 (.cons d558 (.single d559)))))))))))))))))))))))))))))))))))))))), u559.self, hc545, fr545, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv520, hv521, hv522, hv523, hv524, hv525, hv526, hv527, hv528, hv529, hv530, hv531, hv532, hv533, hv534, hv535, hv536, hv537, hv538, hv539, hv540, hv541, hv542, hv543, hv544, hv546, hv547, hv548, hv549, hv550, hv551, hv552, hv553, hv554, hv555, hv556, hv557, hv558, hv559⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g14 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v7 v17 v300 v392 v465 v474 v480 v488 v494 v500 v506 v509 v510 v516 v522 v525 v534 v535 v538 v541 v542 v544 v546 v549 v553 v554 v555 v556 v558 v559 : Word}
    (s : St Mi B n 0x756 (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
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
    (q5 : reg n (5 : Fin 32) = v554)
    (q6 : reg n (6 : Fin 32) = v525)
    (q7 : reg n (7 : Fin 32) = v506)
    (q8 : reg n (8 : Fin 32) = v542)
    (q9 : reg n (9 : Fin 32) = v559)
    (q10 : reg n a0 = v474)
    (q11 : reg n a1 = v553)
    (q12 : reg n a2 = v535)
    (q13 : reg n a3 = v546)
    (q14 : reg n a4 = v555)
    (q15 : reg n a5 = v556)
    (q16 : reg n a6 = v541)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v538)
    (q19 : reg n (19 : Fin 32) = v465)
    (q20 : reg n (20 : Fin 32) = v488)
    (q21 : reg n (21 : Fin 32) = v516)
    (q22 : reg n (22 : Fin 32) = v522)
    (q23 : reg n (23 : Fin 32) = v510)
    (q24 : reg n (24 : Fin 32) = v509)
    (q25 : reg n (25 : Fin 32) = v480)
    (q26 : reg n (26 : Fin 32) = v549)
    (q27 : reg n (27 : Fin 32) = v392)
    (q28 : reg n (28 : Fin 32) = v500)
    (q29 : reg n (29 : Fin 32) = v494)
    (q30 : reg n (30 : Fin 32) = v558)
    (q31 : reg n (31 : Fin 32) = v534)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v560 v561 v562 v563 v564 v565 v566 v567 v568 v569 v570 v571 v572 v573 v574 v575 v576 v577 v578 v579 v580 v581 v582 v583 v584 v585 v586 v587 v588 v589 v590 v591 v593 v594 v595 v596 v597 v598 v599 : Word),
      Steps n n' ∧
      St M' B n' 0x7D6 (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v572 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v554 ∧
      reg n' (6 : Fin 32) = v525 ∧
      reg n' (7 : Fin 32) = v506 ∧
      reg n' (8 : Fin 32) = v594 ∧
      reg n' (9 : Fin 32) = v597 ∧
      reg n' a0 = v474 ∧
      reg n' a1 = v596 ∧
      reg n' a2 = v598 ∧
      reg n' a3 = v599 ∧
      reg n' a4 = v586 ∧
      reg n' a5 = v595 ∧
      reg n' a6 = v541 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v590 ∧
      reg n' (19 : Fin 32) = v465 ∧
      reg n' (20 : Fin 32) = v488 ∧
      reg n' (21 : Fin 32) = v516 ∧
      reg n' (22 : Fin 32) = v522 ∧
      reg n' (23 : Fin 32) = v510 ∧
      reg n' (24 : Fin 32) = v509 ∧
      reg n' (25 : Fin 32) = v480 ∧
      reg n' (26 : Fin 32) = v578 ∧
      reg n' (27 : Fin 32) = v582 ∧
      reg n' (28 : Fin 32) = v500 ∧
      reg n' (29 : Fin 32) = v494 ∧
      reg n' (30 : Fin 32) = v566 ∧
      reg n' (31 : Fin 32) = v534 ∧
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
      aluEval .sltu v556 v546 = v560 ∧
      aluEval .add v549 v535 = v561 ∧
      aluEval .add v534 v560 = v562 ∧
      aluEval .sltu v561 v535 = v563 ∧
      aluEval .add v553 v563 = v564 ∧
      aluEval .mulhu v474 v17 = v565 ∧
      aluEval .add v558 v561 = v566 ∧
      aluEval .add v555 v542 = v567 ∧
      aluEval .sltu v566 v561 = v568 ∧
      aluEval .sltu v567 v542 = v569 ∧
      aluEval .add v564 v568 = v570 ∧
      aluEval .add v569 v559 = v571 ∧
      aluEval .add v567 v570 = v572 ∧
      aluEval .sub v556 v474 = v573 ∧
      aluEval .sltu v572 v567 = v574 ∧
      aluEval .sltu v573 v556 = v575 ∧
      aluEval .add v574 v571 = v576 ∧
      aluEval .add v575 v565 = v577 ∧
      aluEval .add v573 v576 = v578 ∧
      aluEval .mul v480 v509 = v579 ∧
      aluEval .sltu v578 v573 = v580 ∧
      aluEval .sub v562 v474 = v581 ∧
      aluEval .mulhu v480 v509 = v582 ∧
      aluEval .mul v480 v510 = v583 ∧
      aluEval .add v577 v580 = v584 ∧
      aluEval .sltu v581 v562 = v585 ∧
      aluEval .add v584 v581 = v586 ∧
      aluEval .mulhu v480 v510 = v587 ∧
      aluEval .add v565 v585 = v588 ∧
      aluEval .sltu v586 v581 = v589 ∧
      aluEval .add v588 v589 = v590 ∧
      aluEval .add v579 v554 = v591 ∧
      aluEval .sltu v591 v554 = v593 ∧
      aluEval .mul v480 v516 = v594 ∧
      aluEval .add v593 v582 = v595 ∧
      aluEval .add v583 v566 = v596 ∧
      aluEval .sltu v596 v566 = v597 ∧
      aluEval .mulhu v480 v516 = v598 ∧
      aluEval .add v587 v597 = v599 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n560, v560, d560, hv560, u560⟩ := s.aluG hc psm_at_756 (off' := 0x75A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv560
  obtain ⟨n561, v561, d561, hv561, u561⟩ := u560.aluG hc psm_at_75a (off' := 0x75C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv561
  obtain ⟨n562, v562, d562, hv562, u562⟩ := u561.aluG hc psm_at_75c (off' := 0x760) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv562
  obtain ⟨n563, v563, d563, hv563, u563⟩ := u562.aluG hc psm_at_760 (off' := 0x764) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv563
  obtain ⟨n564, v564, d564, hv564, u564⟩ := u563.aluG hc psm_at_764 (off' := 0x766) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv564
  obtain ⟨n565, v565, d565, hv565, u565⟩ := u564.aluG hc psm_at_766 (off' := 0x76A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv565
  obtain ⟨n566, v566, d566, hv566, u566⟩ := u565.aluG hc psm_at_76a (off' := 0x76C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv566
  obtain ⟨n567, v567, d567, hv567, u567⟩ := u566.aluG hc psm_at_76c (off' := 0x76E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv567
  obtain ⟨n568, v568, d568, hv568, u568⟩ := u567.aluG hc psm_at_76e (off' := 0x772) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv568
  obtain ⟨n569, v569, d569, hv569, u569⟩ := u568.aluG hc psm_at_772 (off' := 0x776) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv569
  obtain ⟨n570, v570, d570, hv570, u570⟩ := u569.aluG hc psm_at_776 (off' := 0x778) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv570
  obtain ⟨n571, v571, d571, hv571, u571⟩ := u570.aluG hc psm_at_778 (off' := 0x77A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv571
  obtain ⟨n572, v572, d572, hv572, u572⟩ := u571.aluG hc psm_at_77a (off' := 0x77E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv572
  obtain ⟨n573, v573, d573, hv573, u573⟩ := u572.aluG hc psm_at_77e (off' := 0x782) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv573
  obtain ⟨n574, v574, d574, hv574, u574⟩ := u573.aluG hc psm_at_782 (off' := 0x786) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv574
  obtain ⟨n575, v575, d575, hv575, u575⟩ := u574.aluG hc psm_at_786 (off' := 0x78A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv575
  obtain ⟨n576, v576, d576, hv576, u576⟩ := u575.aluG hc psm_at_78a (off' := 0x78C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv576
  obtain ⟨n577, v577, d577, hv577, u577⟩ := u576.aluG hc psm_at_78c (off' := 0x78E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv577
  obtain ⟨n578, v578, d578, hv578, u578⟩ := u577.aluG hc psm_at_78e (off' := 0x792) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv578
  obtain ⟨n579, v579, d579, hv579, u579⟩ := u578.aluG hc psm_at_792 (off' := 0x796) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv579
  obtain ⟨n580, v580, d580, hv580, u580⟩ := u579.aluG hc psm_at_796 (off' := 0x79A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv580
  obtain ⟨n581, v581, d581, hv581, u581⟩ := u580.aluG hc psm_at_79a (off' := 0x79E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv581
  obtain ⟨n582, v582, d582, hv582, u582⟩ := u581.aluG hc psm_at_79e (off' := 0x7A2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv582
  obtain ⟨n583, v583, d583, hv583, u583⟩ := u582.aluG hc psm_at_7a2 (off' := 0x7A6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv583
  obtain ⟨n584, v584, d584, hv584, u584⟩ := u583.aluG hc psm_at_7a6 (off' := 0x7A8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv584
  obtain ⟨n585, v585, d585, hv585, u585⟩ := u584.aluG hc psm_at_7a8 (off' := 0x7AC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv585
  obtain ⟨n586, v586, d586, hv586, u586⟩ := u585.aluG hc psm_at_7ac (off' := 0x7AE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv586
  obtain ⟨n587, v587, d587, hv587, u587⟩ := u586.aluG hc psm_at_7ae (off' := 0x7B2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv587
  obtain ⟨n588, v588, d588, hv588, u588⟩ := u587.aluG hc psm_at_7b2 (off' := 0x7B4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv588
  obtain ⟨n589, v589, d589, hv589, u589⟩ := u588.aluG hc psm_at_7b4 (off' := 0x7B8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv589
  obtain ⟨n590, v590, d590, hv590, u590⟩ := u589.aluG hc psm_at_7b8 (off' := 0x7BC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv590
  obtain ⟨n591, v591, d591, hv591, u591⟩ := u590.aluG hc psm_at_7bc (off' := 0x7BE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv591
  obtain ⟨n592, d592, u592⟩ := u591.swG hc psm_at_7be (off' := 0x7C0) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 24) (by decide)) (a := F + 0x18) (v := v591)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M592, hM592⟩ : ∃ M', memStore32 Mi (F + 0x18) v591 = M' := ⟨_, rfl⟩
  rw [hM592] at u592
  have hc592 : CodeIn M592 B p256ScalarMulCode := by rw [← hM592]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr592 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M592 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM592, memStore32_get_sep (frm_sep' hx1 (by decide)), fr x hx1 hx2 hx3]
  obtain ⟨n593, v593, d593, hv593, u593⟩ := u592.aluG hc592 psm_at_7c0 (off' := 0x7C4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv593
  obtain ⟨n594, v594, d594, hv594, u594⟩ := u593.aluG hc592 psm_at_7c4 (off' := 0x7C8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv594
  obtain ⟨n595, v595, d595, hv595, u595⟩ := u594.aluG hc592 psm_at_7c8 (off' := 0x7CA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv595
  obtain ⟨n596, v596, d596, hv596, u596⟩ := u595.aluG hc592 psm_at_7ca (off' := 0x7CC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv596
  obtain ⟨n597, v597, d597, hv597, u597⟩ := u596.aluG hc592 psm_at_7cc (off' := 0x7D0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv597
  obtain ⟨n598, v598, d598, hv598, u598⟩ := u597.aluG hc592 psm_at_7d0 (off' := 0x7D4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv598
  obtain ⟨n599, v599, d599, hv599, u599⟩ := u598.aluG hc592 psm_at_7d4 (off' := 0x7D6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv599
  have qo1 : reg n599 ra = v572 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n599 sp = F := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n599 (3 : Fin 32) = G3 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n599 (4 : Fin 32) = G4 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n599 (5 : Fin 32) = v554 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n599 (6 : Fin 32) = v525 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n599 (7 : Fin 32) = v506 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n599 (8 : Fin 32) = v594 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n599 (9 : Fin 32) = v597 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n599 a0 = v474 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n599 a1 = v596 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n599 a2 = v598 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n599 a3 = v599 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n599 a4 = v586 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n599 a5 = v595 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n599 a6 = v541 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n599 a7 = v17 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n599 (18 : Fin 32) = v590 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n599 (19 : Fin 32) = v465 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n599 (20 : Fin 32) = v488 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n599 (21 : Fin 32) = v516 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n599 (22 : Fin 32) = v522 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n599 (23 : Fin 32) = v510 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n599 (24 : Fin 32) = v509 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n599 (25 : Fin 32) = v480 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n599 (26 : Fin 32) = v578 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n599 (27 : Fin 32) = v582 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n599 (28 : Fin 32) = v500 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n599 (29 : Fin 32) = v494 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n599 (30 : Fin 32) = v566 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n599 (31 : Fin 32) = v534 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so18 : memLoad32 M592 (F + 0x18) = v591 := by
    rw [← hM592, memLoad32_store32_same]
  have so1C : memLoad32 M592 (F + 0x1C) = v544 := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x1C) 4 from sep_offsets F (c := 24) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), sl1C]
  have so20 : memLoad32 M592 (F + 0x20) = v7 := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x20) 4 from sep_offsets F (c := 24) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), sl20]
  have so24 : memLoad32 M592 (F + 0x24) = v0 := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x24) 4 from sep_offsets F (c := 24) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), sl24]
  have so28 : memLoad32 M592 (F + 0x28) = outp := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x28) 4 from sep_offsets F (c := 24) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), sl28]
  have so2C : memLoad32 M592 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x2C) 4 from sep_offsets F (c := 24) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), sl2C]
  have so30 : memLoad32 M592 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x30) 4 from sep_offsets F (c := 24) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), sl30]
  have so34 : memLoad32 M592 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x34) 4 from sep_offsets F (c := 24) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), sl34]
  have so38 : memLoad32 M592 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x38) 4 from sep_offsets F (c := 24) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), sl38]
  have so3C : memLoad32 M592 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x3C) 4 from sep_offsets F (c := 24) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), sl3C]
  have so40 : memLoad32 M592 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x40) 4 from sep_offsets F (c := 24) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), sl40]
  have so44 : memLoad32 M592 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x44) 4 from sep_offsets F (c := 24) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), sl44]
  have so48 : memLoad32 M592 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x48) 4 from sep_offsets F (c := 24) (n := 4) (d := 72) (k := 4) (by decide) (by decide) (by decide)), sl48]
  have so4C : memLoad32 M592 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x4C) 4 from sep_offsets F (c := 24) (n := 4) (d := 76) (k := 4) (by decide) (by decide) (by decide)), sl4C]
  have so50 : memLoad32 M592 (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x50) 4 from sep_offsets F (c := 24) (n := 4) (d := 80) (k := 4) (by decide) (by decide) (by decide)), sl50]
  have so54 : memLoad32 M592 (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x54) 4 from sep_offsets F (c := 24) (n := 4) (d := 84) (k := 4) (by decide) (by decide) (by decide)), sl54]
  have so58 : memLoad32 M592 (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x58) 4 from sep_offsets F (c := 24) (n := 4) (d := 88) (k := 4) (by decide) (by decide) (by decide)), sl58]
  have so5C : memLoad32 M592 (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x5C) 4 from sep_offsets F (c := 24) (n := 4) (d := 92) (k := 4) (by decide) (by decide) (by decide)), sl5C]
  have so60 : memLoad32 M592 (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x60) 4 from sep_offsets F (c := 24) (n := 4) (d := 96) (k := 4) (by decide) (by decide) (by decide)), sl60]
  have so64 : memLoad32 M592 (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x64) 4 from sep_offsets F (c := 24) (n := 4) (d := 100) (k := 4) (by decide) (by decide) (by decide)), sl64]
  have so68 : memLoad32 M592 (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x68) 4 from sep_offsets F (c := 24) (n := 4) (d := 104) (k := 4) (by decide) (by decide) (by decide)), sl68]
  have so6C : memLoad32 M592 (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x6C) 4 from sep_offsets F (c := 24) (n := 4) (d := 108) (k := 4) (by decide) (by decide) (by decide)), sl6C]
  have so70 : memLoad32 M592 (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x70) 4 from sep_offsets F (c := 24) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), sl70]
  have so74 : memLoad32 M592 (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x74) 4 from sep_offsets F (c := 24) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), sl74]
  have so78 : memLoad32 M592 (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x78) 4 from sep_offsets F (c := 24) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), sl78]
  have so7C : memLoad32 M592 (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x7C) 4 from sep_offsets F (c := 24) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), sl7C]
  have so80 : memLoad32 M592 (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x80) 4 from sep_offsets F (c := 24) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), sl80]
  have so84 : memLoad32 M592 (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x84) 4 from sep_offsets F (c := 24) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), sl84]
  have so88 : memLoad32 M592 (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x88) 4 from sep_offsets F (c := 24) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88]
  have so8C : memLoad32 M592 (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x8C) 4 from sep_offsets F (c := 24) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), sl8C]
  have so90 : memLoad32 M592 (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x90) 4 from sep_offsets F (c := 24) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), sl90]
  have so94 : memLoad32 M592 (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x94) 4 from sep_offsets F (c := 24) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), sl94]
  have so98 : memLoad32 M592 (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x98) 4 from sep_offsets F (c := 24) (n := 4) (d := 152) (k := 4) (by decide) (by decide) (by decide)), sl98]
  have so9C : memLoad32 M592 (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [← hM592, memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x9C) 4 from sep_offsets F (c := 24) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), sl9C]
  exact ⟨n599, M592, v560, v561, v562, v563, v564, v565, v566, v567, v568, v569, v570, v571, v572, v573, v574, v575, v576, v577, v578, v579, v580, v581, v582, v583, v584, v585, v586, v587, v588, v589, v590, v591, v593, v594, v595, v596, v597, v598, v599, (.cons d560 (.cons d561 (.cons d562 (.cons d563 (.cons d564 (.cons d565 (.cons d566 (.cons d567 (.cons d568 (.cons d569 (.cons d570 (.cons d571 (.cons d572 (.cons d573 (.cons d574 (.cons d575 (.cons d576 (.cons d577 (.cons d578 (.cons d579 (.cons d580 (.cons d581 (.cons d582 (.cons d583 (.cons d584 (.cons d585 (.cons d586 (.cons d587 (.cons d588 (.cons d589 (.cons d590 (.cons d591 (.cons d592 (.cons d593 (.cons d594 (.cons d595 (.cons d596 (.cons d597 (.cons d598 (.single d599)))))))))))))))))))))))))))))))))))))))), u599.self, hc592, fr592, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so18, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv560, hv561, hv562, hv563, hv564, hv565, hv566, hv567, hv568, hv569, hv570, hv571, hv572, hv573, hv574, hv575, hv576, hv577, hv578, hv579, hv580, hv581, hv582, hv583, hv584, hv585, hv586, hv587, hv588, hv589, hv590, hv591, hv593, hv594, hv595, hv596, hv597, hv598, hv599⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g15 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v7 v17 v465 v474 v480 v488 v494 v500 v506 v509 v510 v516 v522 v525 v534 v541 v544 v554 v566 v572 v578 v582 v586 v590 v591 v594 v595 v596 v597 v598 v599 : Word}
    (s : St Mi B n 0x7D6 (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
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
    (q5 : reg n (5 : Fin 32) = v554)
    (q6 : reg n (6 : Fin 32) = v525)
    (q7 : reg n (7 : Fin 32) = v506)
    (q8 : reg n (8 : Fin 32) = v594)
    (q9 : reg n (9 : Fin 32) = v597)
    (q10 : reg n a0 = v474)
    (q11 : reg n a1 = v596)
    (q12 : reg n a2 = v598)
    (q13 : reg n a3 = v599)
    (q14 : reg n a4 = v586)
    (q15 : reg n a5 = v595)
    (q16 : reg n a6 = v541)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v590)
    (q19 : reg n (19 : Fin 32) = v465)
    (q20 : reg n (20 : Fin 32) = v488)
    (q21 : reg n (21 : Fin 32) = v516)
    (q22 : reg n (22 : Fin 32) = v522)
    (q23 : reg n (23 : Fin 32) = v510)
    (q24 : reg n (24 : Fin 32) = v509)
    (q25 : reg n (25 : Fin 32) = v480)
    (q26 : reg n (26 : Fin 32) = v578)
    (q27 : reg n (27 : Fin 32) = v582)
    (q28 : reg n (28 : Fin 32) = v500)
    (q29 : reg n (29 : Fin 32) = v494)
    (q30 : reg n (30 : Fin 32) = v566)
    (q31 : reg n (31 : Fin 32) = v534)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v600 v601 v602 v603 v604 v605 v606 v607 v608 v609 v610 v611 v612 v613 v614 v615 v616 v617 v618 v619 v620 v621 v622 v623 v624 v625 v626 v627 v628 v629 v630 v631 v632 v633 v634 v635 v636 v638 v639 : Word),
      Steps n n' ∧
      St M' B n' 0x85A (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v572 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v603 ∧
      reg n' (6 : Fin 32) = v525 ∧
      reg n' (7 : Fin 32) = v506 ∧
      reg n' (8 : Fin 32) = v635 ∧
      reg n' (9 : Fin 32) = v629 ∧
      reg n' a0 = v633 ∧
      reg n' a1 = v618 ∧
      reg n' a2 = v632 ∧
      reg n' a3 = v638 ∧
      reg n' a4 = v623 ∧
      reg n' a5 = v636 ∧
      reg n' a6 = v541 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v628 ∧
      reg n' (19 : Fin 32) = v465 ∧
      reg n' (20 : Fin 32) = v488 ∧
      reg n' (21 : Fin 32) = v516 ∧
      reg n' (22 : Fin 32) = v522 ∧
      reg n' (23 : Fin 32) = v510 ∧
      reg n' (24 : Fin 32) = v509 ∧
      reg n' (25 : Fin 32) = v630 ∧
      reg n' (26 : Fin 32) = v634 ∧
      reg n' (27 : Fin 32) = v639 ∧
      reg n' (28 : Fin 32) = v500 ∧
      reg n' (29 : Fin 32) = v494 ∧
      reg n' (30 : Fin 32) = v615 ∧
      reg n' (31 : Fin 32) = v608 ∧
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
      aluEval .add v596 v595 = v600 ∧
      aluEval .sltu v600 v596 = v601 ∧
      aluEval .mul v480 v522 = v602 ∧
      aluEval .sub v534 v474 = v603 ∧
      aluEval .add v601 v599 = v604 ∧
      aluEval .add v594 v572 = v605 ∧
      aluEval .mulhu v480 v522 = v606 ∧
      aluEval .sltu v605 v572 = v607 ∧
      aluEval .add v605 v604 = v608 ∧
      aluEval .add v598 v607 = v609 ∧
      aluEval .sltu v608 v605 = v610 ∧
      aluEval .sub v590 v465 = v611 ∧
      aluEval .add v610 v609 = v612 ∧
      aluEval .add v602 v578 = v613 ∧
      aluEval .mulhu v480 v17 = v614 ∧
      aluEval .sltu v611 v590 = v615 ∧
      aluEval .sltu v613 v578 = v616 ∧
      aluEval .add v616 v606 = v617 ∧
      aluEval .add v612 v613 = v618 ∧
      aluEval .sltu v618 v613 = v619 ∧
      aluEval .sub v586 v480 = v620 ∧
      aluEval .add v619 v617 = v621 ∧
      aluEval .sltu v620 v586 = v622 ∧
      aluEval .add v620 v621 = v623 ∧
      aluEval .mul v488 v509 = v624 ∧
      aluEval .add v622 v614 = v625 ∧
      aluEval .sltu v623 v620 = v626 ∧
      aluEval .sub v611 v480 = v627 ∧
      aluEval .mulhu v488 v509 = v628 ∧
      aluEval .sltu v627 v611 = v629 ∧
      aluEval .mul v488 v510 = v630 ∧
      aluEval .add v626 v625 = v631 ∧
      aluEval .add v614 v629 = v632 ∧
      aluEval .add v631 v627 = v633 ∧
      aluEval .mulhu v488 v510 = v634 ∧
      aluEval .sltu v633 v627 = v635 ∧
      aluEval .add v624 v600 = v636 ∧
      aluEval .sltu v636 v600 = v638 ∧
      aluEval .mul v488 v516 = v639 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n600, v600, d600, hv600, u600⟩ := s.aluG hc psm_at_7d6 (off' := 0x7DA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv600
  obtain ⟨n601, v601, d601, hv601, u601⟩ := u600.aluG hc psm_at_7da (off' := 0x7DE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv601
  obtain ⟨n602, v602, d602, hv602, u602⟩ := u601.aluG hc psm_at_7de (off' := 0x7E2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv602
  obtain ⟨n603, v603, d603, hv603, u603⟩ := u602.aluG hc psm_at_7e2 (off' := 0x7E6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv603
  obtain ⟨n604, v604, d604, hv604, u604⟩ := u603.aluG hc psm_at_7e6 (off' := 0x7E8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv604
  obtain ⟨n605, v605, d605, hv605, u605⟩ := u604.aluG hc psm_at_7e8 (off' := 0x7EA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv605
  obtain ⟨n606, v606, d606, hv606, u606⟩ := u605.aluG hc psm_at_7ea (off' := 0x7EE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv606
  obtain ⟨n607, v607, d607, hv607, u607⟩ := u606.aluG hc psm_at_7ee (off' := 0x7F2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv607
  obtain ⟨n608, v608, d608, hv608, u608⟩ := u607.aluG hc psm_at_7f2 (off' := 0x7F6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv608
  obtain ⟨n609, v609, d609, hv609, u609⟩ := u608.aluG hc psm_at_7f6 (off' := 0x7F8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv609
  obtain ⟨n610, v610, d610, hv610, u610⟩ := u609.aluG hc psm_at_7f8 (off' := 0x7FC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv610
  obtain ⟨n611, v611, d611, hv611, u611⟩ := u610.aluG hc psm_at_7fc (off' := 0x800) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv611
  obtain ⟨n612, v612, d612, hv612, u612⟩ := u611.aluG hc psm_at_800 (off' := 0x802) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv612
  obtain ⟨n613, v613, d613, hv613, u613⟩ := u612.aluG hc psm_at_802 (off' := 0x804) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv613
  obtain ⟨n614, v614, d614, hv614, u614⟩ := u613.aluG hc psm_at_804 (off' := 0x808) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv614
  obtain ⟨n615, v615, d615, hv615, u615⟩ := u614.aluG hc psm_at_808 (off' := 0x80C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv615
  obtain ⟨n616, v616, d616, hv616, u616⟩ := u615.aluG hc psm_at_80c (off' := 0x810) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv616
  obtain ⟨n617, v617, d617, hv617, u617⟩ := u616.aluG hc psm_at_810 (off' := 0x812) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv617
  obtain ⟨n618, v618, d618, hv618, u618⟩ := u617.aluG hc psm_at_812 (off' := 0x814) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv618
  obtain ⟨n619, v619, d619, hv619, u619⟩ := u618.aluG hc psm_at_814 (off' := 0x818) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv619
  obtain ⟨n620, v620, d620, hv620, u620⟩ := u619.aluG hc psm_at_818 (off' := 0x81C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv620
  obtain ⟨n621, v621, d621, hv621, u621⟩ := u620.aluG hc psm_at_81c (off' := 0x81E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv621
  obtain ⟨n622, v622, d622, hv622, u622⟩ := u621.aluG hc psm_at_81e (off' := 0x822) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv622
  obtain ⟨n623, v623, d623, hv623, u623⟩ := u622.aluG hc psm_at_822 (off' := 0x826) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv623
  obtain ⟨n624, v624, d624, hv624, u624⟩ := u623.aluG hc psm_at_826 (off' := 0x82A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv624
  obtain ⟨n625, v625, d625, hv625, u625⟩ := u624.aluG hc psm_at_82a (off' := 0x82C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv625
  obtain ⟨n626, v626, d626, hv626, u626⟩ := u625.aluG hc psm_at_82c (off' := 0x830) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv626
  obtain ⟨n627, v627, d627, hv627, u627⟩ := u626.aluG hc psm_at_830 (off' := 0x834) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv627
  obtain ⟨n628, v628, d628, hv628, u628⟩ := u627.aluG hc psm_at_834 (off' := 0x838) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv628
  obtain ⟨n629, v629, d629, hv629, u629⟩ := u628.aluG hc psm_at_838 (off' := 0x83C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv629
  obtain ⟨n630, v630, d630, hv630, u630⟩ := u629.aluG hc psm_at_83c (off' := 0x840) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv630
  obtain ⟨n631, v631, d631, hv631, u631⟩ := u630.aluG hc psm_at_840 (off' := 0x842) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv631
  obtain ⟨n632, v632, d632, hv632, u632⟩ := u631.aluG hc psm_at_842 (off' := 0x844) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv632
  obtain ⟨n633, v633, d633, hv633, u633⟩ := u632.aluG hc psm_at_844 (off' := 0x846) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv633
  obtain ⟨n634, v634, d634, hv634, u634⟩ := u633.aluG hc psm_at_846 (off' := 0x84A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv634
  obtain ⟨n635, v635, d635, hv635, u635⟩ := u634.aluG hc psm_at_84a (off' := 0x84E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv635
  obtain ⟨n636, v636, d636, hv636, u636⟩ := u635.aluG hc psm_at_84e (off' := 0x850) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv636
  obtain ⟨n637, d637, u637⟩ := u636.swG hc psm_at_850 (off' := 0x852) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 20) (by decide)) (a := F + 0x14) (v := v636)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M637, hM637⟩ : ∃ M', memStore32 Mi (F + 0x14) v636 = M' := ⟨_, rfl⟩
  rw [hM637] at u637
  have hc637 : CodeIn M637 B p256ScalarMulCode := by rw [← hM637]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr637 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M637 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM637, memStore32_get_sep (frm_sep' hx1 (by decide)), fr x hx1 hx2 hx3]
  obtain ⟨n638, v638, d638, hv638, u638⟩ := u637.aluG hc637 psm_at_852 (off' := 0x856) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv638
  obtain ⟨n639, v639, d639, hv639, u639⟩ := u638.aluG hc637 psm_at_856 (off' := 0x85A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv639
  have qo1 : reg n639 ra = v572 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n639 sp = F := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n639 (3 : Fin 32) = G3 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n639 (4 : Fin 32) = G4 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n639 (5 : Fin 32) = v603 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n639 (6 : Fin 32) = v525 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n639 (7 : Fin 32) = v506 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n639 (8 : Fin 32) = v635 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n639 (9 : Fin 32) = v629 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n639 a0 = v633 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n639 a1 = v618 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n639 a2 = v632 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n639 a3 = v638 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n639 a4 = v623 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n639 a5 = v636 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n639 a6 = v541 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n639 a7 = v17 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n639 (18 : Fin 32) = v628 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n639 (19 : Fin 32) = v465 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n639 (20 : Fin 32) = v488 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n639 (21 : Fin 32) = v516 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n639 (22 : Fin 32) = v522 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n639 (23 : Fin 32) = v510 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n639 (24 : Fin 32) = v509 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n639 (25 : Fin 32) = v630 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n639 (26 : Fin 32) = v634 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n639 (27 : Fin 32) = v639 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n639 (28 : Fin 32) = v500 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n639 (29 : Fin 32) = v494 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n639 (30 : Fin 32) = v615 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n639 (31 : Fin 32) = v608 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so14 : memLoad32 M637 (F + 0x14) = v636 := by
    rw [← hM637, memLoad32_store32_same]
  have so18 : memLoad32 M637 (F + 0x18) = v591 := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x18) 4 from sep_offsets F (c := 20) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), sl18]
  have so1C : memLoad32 M637 (F + 0x1C) = v544 := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x1C) 4 from sep_offsets F (c := 20) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), sl1C]
  have so20 : memLoad32 M637 (F + 0x20) = v7 := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x20) 4 from sep_offsets F (c := 20) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), sl20]
  have so24 : memLoad32 M637 (F + 0x24) = v0 := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x24) 4 from sep_offsets F (c := 20) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), sl24]
  have so28 : memLoad32 M637 (F + 0x28) = outp := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x28) 4 from sep_offsets F (c := 20) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), sl28]
  have so2C : memLoad32 M637 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x2C) 4 from sep_offsets F (c := 20) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), sl2C]
  have so30 : memLoad32 M637 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x30) 4 from sep_offsets F (c := 20) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), sl30]
  have so34 : memLoad32 M637 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x34) 4 from sep_offsets F (c := 20) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), sl34]
  have so38 : memLoad32 M637 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x38) 4 from sep_offsets F (c := 20) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), sl38]
  have so3C : memLoad32 M637 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x3C) 4 from sep_offsets F (c := 20) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), sl3C]
  have so40 : memLoad32 M637 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x40) 4 from sep_offsets F (c := 20) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), sl40]
  have so44 : memLoad32 M637 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x44) 4 from sep_offsets F (c := 20) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), sl44]
  have so48 : memLoad32 M637 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x48) 4 from sep_offsets F (c := 20) (n := 4) (d := 72) (k := 4) (by decide) (by decide) (by decide)), sl48]
  have so4C : memLoad32 M637 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x4C) 4 from sep_offsets F (c := 20) (n := 4) (d := 76) (k := 4) (by decide) (by decide) (by decide)), sl4C]
  have so50 : memLoad32 M637 (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x50) 4 from sep_offsets F (c := 20) (n := 4) (d := 80) (k := 4) (by decide) (by decide) (by decide)), sl50]
  have so54 : memLoad32 M637 (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x54) 4 from sep_offsets F (c := 20) (n := 4) (d := 84) (k := 4) (by decide) (by decide) (by decide)), sl54]
  have so58 : memLoad32 M637 (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x58) 4 from sep_offsets F (c := 20) (n := 4) (d := 88) (k := 4) (by decide) (by decide) (by decide)), sl58]
  have so5C : memLoad32 M637 (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x5C) 4 from sep_offsets F (c := 20) (n := 4) (d := 92) (k := 4) (by decide) (by decide) (by decide)), sl5C]
  have so60 : memLoad32 M637 (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x60) 4 from sep_offsets F (c := 20) (n := 4) (d := 96) (k := 4) (by decide) (by decide) (by decide)), sl60]
  have so64 : memLoad32 M637 (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x64) 4 from sep_offsets F (c := 20) (n := 4) (d := 100) (k := 4) (by decide) (by decide) (by decide)), sl64]
  have so68 : memLoad32 M637 (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x68) 4 from sep_offsets F (c := 20) (n := 4) (d := 104) (k := 4) (by decide) (by decide) (by decide)), sl68]
  have so6C : memLoad32 M637 (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x6C) 4 from sep_offsets F (c := 20) (n := 4) (d := 108) (k := 4) (by decide) (by decide) (by decide)), sl6C]
  have so70 : memLoad32 M637 (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x70) 4 from sep_offsets F (c := 20) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), sl70]
  have so74 : memLoad32 M637 (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x74) 4 from sep_offsets F (c := 20) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), sl74]
  have so78 : memLoad32 M637 (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x78) 4 from sep_offsets F (c := 20) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), sl78]
  have so7C : memLoad32 M637 (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x7C) 4 from sep_offsets F (c := 20) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), sl7C]
  have so80 : memLoad32 M637 (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x80) 4 from sep_offsets F (c := 20) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), sl80]
  have so84 : memLoad32 M637 (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x84) 4 from sep_offsets F (c := 20) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), sl84]
  have so88 : memLoad32 M637 (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x88) 4 from sep_offsets F (c := 20) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88]
  have so8C : memLoad32 M637 (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x8C) 4 from sep_offsets F (c := 20) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), sl8C]
  have so90 : memLoad32 M637 (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x90) 4 from sep_offsets F (c := 20) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), sl90]
  have so94 : memLoad32 M637 (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x94) 4 from sep_offsets F (c := 20) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), sl94]
  have so98 : memLoad32 M637 (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x98) 4 from sep_offsets F (c := 20) (n := 4) (d := 152) (k := 4) (by decide) (by decide) (by decide)), sl98]
  have so9C : memLoad32 M637 (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [← hM637, memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x9C) 4 from sep_offsets F (c := 20) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), sl9C]
  exact ⟨n639, M637, v600, v601, v602, v603, v604, v605, v606, v607, v608, v609, v610, v611, v612, v613, v614, v615, v616, v617, v618, v619, v620, v621, v622, v623, v624, v625, v626, v627, v628, v629, v630, v631, v632, v633, v634, v635, v636, v638, v639, (.cons d600 (.cons d601 (.cons d602 (.cons d603 (.cons d604 (.cons d605 (.cons d606 (.cons d607 (.cons d608 (.cons d609 (.cons d610 (.cons d611 (.cons d612 (.cons d613 (.cons d614 (.cons d615 (.cons d616 (.cons d617 (.cons d618 (.cons d619 (.cons d620 (.cons d621 (.cons d622 (.cons d623 (.cons d624 (.cons d625 (.cons d626 (.cons d627 (.cons d628 (.cons d629 (.cons d630 (.cons d631 (.cons d632 (.cons d633 (.cons d634 (.cons d635 (.cons d636 (.cons d637 (.cons d638 (.single d639)))))))))))))))))))))))))))))))))))))))), u639.self, hc637, fr637, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so14, so18, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv600, hv601, hv602, hv603, hv604, hv605, hv606, hv607, hv608, hv609, hv610, hv611, hv612, hv613, hv614, hv615, hv616, hv617, hv618, hv619, hv620, hv621, hv622, hv623, hv624, hv625, hv626, hv627, hv628, hv629, hv630, hv631, hv632, hv633, hv634, hv635, hv636, hv638, hv639⟩

end C3.RV32
