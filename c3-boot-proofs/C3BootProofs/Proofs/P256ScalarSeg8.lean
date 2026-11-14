import C3BootProofs.Proofs.P256ScalarDecode

/-! # P-256's `Scalar::mul`, segments 22 to 23

Each theorem steps 40 instructions. `scripts/gen-p256-scalar.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g22 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v494 v506 v509 v510 v516 v522 v525 v603 v615 v693 v751 v755 v761 v774 v786 v834 v840 v846 v852 v858 v864 v871 v873 v875 v876 v878 v879 : Word}
    (s : St Mi B n 0xB02 (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v603)
    (q6 : reg n (6 : Fin 32) = v525)
    (q7 : reg n (7 : Fin 32) = v506)
    (q8 : reg n (8 : Fin 32) = v786)
    (q9 : reg n (9 : Fin 32) = v774)
    (q10 : reg n a0 = v879)
    (q11 : reg n a1 = v871)
    (q12 : reg n a2 = v873)
    (q14 : reg n a4 = v878)
    (q15 : reg n a5 = v751)
    (q16 : reg n a6 = v875)
    (q17 : reg n a7 = v693)
    (q18 : reg n (18 : Fin 32) = v858)
    (q19 : reg n (19 : Fin 32) = v876)
    (q20 : reg n (20 : Fin 32) = v852)
    (q21 : reg n (21 : Fin 32) = v516)
    (q22 : reg n (22 : Fin 32) = v522)
    (q23 : reg n (23 : Fin 32) = v510)
    (q24 : reg n (24 : Fin 32) = v509)
    (q25 : reg n (25 : Fin 32) = v834)
    (q26 : reg n (26 : Fin 32) = v846)
    (q27 : reg n (27 : Fin 32) = v864)
    (q28 : reg n (28 : Fin 32) = v761)
    (q29 : reg n (29 : Fin 32) = v494)
    (q30 : reg n (30 : Fin 32) = v615)
    (q31 : reg n (31 : Fin 32) = v755)
    (sl14 : memLoad32 Mi (F + 0x14) = v840)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v880 v881 v882 v883 v884 v885 v886 v887 v889 v890 v891 v892 v893 v894 v895 v896 v897 v898 v899 v900 v901 v902 v903 v904 v905 v906 v907 v913 : Word),
      Steps n n' ∧
      St M' B n' 0xB64 (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v603 ∧
      reg n' (6 : Fin 32) = v525 ∧
      reg n' (7 : Fin 32) = v506 ∧
      reg n' (8 : Fin 32) = v901 ∧
      reg n' (9 : Fin 32) = outp ∧
      reg n' a0 = v879 ∧
      reg n' a1 = v913 ∧
      reg n' a2 = v885 ∧
      reg n' a3 = v907 ∧
      reg n' a4 = v891 ∧
      reg n' a5 = v896 ∧
      reg n' a6 = v875 ∧
      reg n' a7 = v693 ∧
      reg n' (18 : Fin 32) = v906 ∧
      reg n' (19 : Fin 32) = v876 ∧
      reg n' (20 : Fin 32) = v899 ∧
      reg n' (21 : Fin 32) = v516 ∧
      reg n' (22 : Fin 32) = v522 ∧
      reg n' (23 : Fin 32) = v510 ∧
      reg n' (24 : Fin 32) = v509 ∧
      reg n' (25 : Fin 32) = v882 ∧
      reg n' (26 : Fin 32) = v894 ∧
      reg n' (27 : Fin 32) = v864 ∧
      reg n' (28 : Fin 32) = v761 ∧
      reg n' (29 : Fin 32) = v494 ∧
      reg n' (30 : Fin 32) = v615 ∧
      reg n' (31 : Fin 32) = v755 ∧
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
      memLoad32 M' (outp + 0x0) = v875 ∧
      memLoad32 M' (outp + 0x4) = v879 ∧
      memLoad32 M' (outp + 0x8) = v885 ∧
      memLoad32 M' (outp + 0xC) = v891 ∧
      memLoad32 M' (outp + 0x10) = v896 ∧
      memLoad32 M' (outp + 0x14) = v901 ∧
      aluEval .sltu v876 v873 = v880 ∧
      aluEval .sltu v879 v876 = v881 ∧
      aluEval .add v834 v878 = v882 ∧
      aluEval .add v880 v881 = v883 ∧
      aluEval .and v871 v522 = v884 ∧
      aluEval .add v883 v882 = v885 ∧
      aluEval .sltu v882 v878 = v886 ∧
      aluEval .sltu v885 v882 = v887 ∧
      aluEval .add v840 v884 = v889 ∧
      aluEval .add v886 v887 = v890 ∧
      aluEval .add v890 v889 = v891 ∧
      aluEval .sltu v889 v884 = v892 ∧
      aluEval .sltu v891 v889 = v893 ∧
      aluEval .add v846 v871 = v894 ∧
      aluEval .add v893 v892 = v895 ∧
      aluEval .add v895 v894 = v896 ∧
      aluEval .sltu v894 v871 = v897 ∧
      aluEval .sltu v896 v894 = v898 ∧
      aluEval .add v852 v871 = v899 ∧
      aluEval .add v898 v897 = v900 ∧
      aluEval .add v900 v899 = v901 ∧
      aluEval .sltu v899 v871 = v902 ∧
      aluEval .sltu v901 v899 = v903 ∧
      aluEval .add v903 v902 = v904 ∧
      aluEval .add v871 v864 = v905 ∧
      aluEval .add v858 v904 = v906 ∧
      aluEval .sltu v906 v904 = v907 ∧
      aluEval .add v905 v907 = v913 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n880, v880, d880, hv880, u880⟩ := s.aluG hc psm_at_b02 (off' := 0xB06) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv880
  obtain ⟨n881, v881, d881, hv881, u881⟩ := u880.aluG hc psm_at_b06 (off' := 0xB0A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv881
  obtain ⟨n882, v882, d882, hv882, u882⟩ := u881.aluG hc psm_at_b0a (off' := 0xB0C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv882
  obtain ⟨n883, v883, d883, hv883, u883⟩ := u882.aluG hc psm_at_b0c (off' := 0xB0E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv883
  obtain ⟨n884, v884, d884, hv884, u884⟩ := u883.aluG hc psm_at_b0e (off' := 0xB12) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv884
  obtain ⟨n885, v885, d885, hv885, u885⟩ := u884.aluG hc psm_at_b12 (off' := 0xB14) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv885
  obtain ⟨n886, v886, d886, hv886, u886⟩ := u885.aluG hc psm_at_b14 (off' := 0xB18) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv886
  obtain ⟨n887, v887, d887, hv887, u887⟩ := u886.aluG hc psm_at_b18 (off' := 0xB1C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv887
  obtain ⟨n888, d888, u888⟩ := u887.lwE hc psm_at_b1c (off' := 0xB1E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 20) (by decide)) (v := v840)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl14])
  obtain ⟨n889, v889, d889, hv889, u889⟩ := u888.aluG hc psm_at_b1e (off' := 0xB20) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv889
  obtain ⟨n890, v890, d890, hv890, u890⟩ := u889.aluG hc psm_at_b20 (off' := 0xB22) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv890
  obtain ⟨n891, v891, d891, hv891, u891⟩ := u890.aluG hc psm_at_b22 (off' := 0xB24) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv891
  obtain ⟨n892, v892, d892, hv892, u892⟩ := u891.aluG hc psm_at_b24 (off' := 0xB28) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv892
  obtain ⟨n893, v893, d893, hv893, u893⟩ := u892.aluG hc psm_at_b28 (off' := 0xB2C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv893
  obtain ⟨n894, v894, d894, hv894, u894⟩ := u893.aluG hc psm_at_b2c (off' := 0xB2E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv894
  obtain ⟨n895, v895, d895, hv895, u895⟩ := u894.aluG hc psm_at_b2e (off' := 0xB30) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv895
  obtain ⟨n896, v896, d896, hv896, u896⟩ := u895.aluG hc psm_at_b30 (off' := 0xB32) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv896
  obtain ⟨n897, v897, d897, hv897, u897⟩ := u896.aluG hc psm_at_b32 (off' := 0xB36) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv897
  obtain ⟨n898, v898, d898, hv898, u898⟩ := u897.aluG hc psm_at_b36 (off' := 0xB3A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv898
  obtain ⟨n899, v899, d899, hv899, u899⟩ := u898.aluG hc psm_at_b3a (off' := 0xB3C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv899
  obtain ⟨n900, v900, d900, hv900, u900⟩ := u899.aluG hc psm_at_b3c (off' := 0xB3E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv900
  obtain ⟨n901, v901, d901, hv901, u901⟩ := u900.aluG hc psm_at_b3e (off' := 0xB40) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv901
  obtain ⟨n902, v902, d902, hv902, u902⟩ := u901.aluG hc psm_at_b40 (off' := 0xB44) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv902
  obtain ⟨n903, v903, d903, hv903, u903⟩ := u902.aluG hc psm_at_b44 (off' := 0xB48) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv903
  obtain ⟨n904, v904, d904, hv904, u904⟩ := u903.aluG hc psm_at_b48 (off' := 0xB4A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv904
  obtain ⟨n905, v905, d905, hv905, u905⟩ := u904.aluG hc psm_at_b4a (off' := 0xB4C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv905
  obtain ⟨n906, v906, d906, hv906, u906⟩ := u905.aluG hc psm_at_b4c (off' := 0xB4E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv906
  obtain ⟨n907, v907, d907, hv907, u907⟩ := u906.aluG hc psm_at_b4e (off' := 0xB52) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv907
  obtain ⟨n908, d908, u908⟩ := u907.lwE hc psm_at_b52 (off' := 0xB54) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 40) (by decide)) (v := outp)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl28])
  obtain ⟨n909, d909, u909⟩ := u908.swG hc psm_at_b54 (off' := 0xB58) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hO (k := 0) (by decide)) (a := outp + 0x0) (v := v875)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M909, hM909⟩ : ∃ M', memStore32 Mi (outp + 0x0) v875 = M' := ⟨_, rfl⟩
  rw [hM909] at u909
  have hc909 : CodeIn M909 B p256ScalarMulCode := by rw [← hM909]; exact hc.store32 (frm_sep' sOC (by decide))
  have fr909 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M909 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM909, memStore32_get_sep (frm_sep' hx3 (by decide)), fr x hx1 hx2 hx3]
  obtain ⟨n910, d910, u910⟩ := u909.swG hc909 psm_at_b58 (off' := 0xB5A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hO (k := 4) (by decide)) (a := outp + 0x4) (v := v879)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M910, hM910⟩ : ∃ M', memStore32 M909 (outp + 0x4) v879 = M' := ⟨_, rfl⟩
  rw [hM910] at u910
  have hc910 : CodeIn M910 B p256ScalarMulCode := by rw [← hM910]; exact hc909.store32 (frm_sep' sOC (by decide))
  have fr910 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M910 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM910, memStore32_get_sep (frm_sep' hx3 (by decide)), fr909 x hx1 hx2 hx3]
  obtain ⟨n911, d911, u911⟩ := u910.swG hc910 psm_at_b5a (off' := 0xB5C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hO (k := 8) (by decide)) (a := outp + 0x8) (v := v885)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M911, hM911⟩ : ∃ M', memStore32 M910 (outp + 0x8) v885 = M' := ⟨_, rfl⟩
  rw [hM911] at u911
  have hc911 : CodeIn M911 B p256ScalarMulCode := by rw [← hM911]; exact hc910.store32 (frm_sep' sOC (by decide))
  have fr911 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M911 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM911, memStore32_get_sep (frm_sep' hx3 (by decide)), fr910 x hx1 hx2 hx3]
  obtain ⟨n912, d912, u912⟩ := u911.swG hc911 psm_at_b5c (off' := 0xB5E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hO (k := 12) (by decide)) (a := outp + 0xC) (v := v891)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M912, hM912⟩ : ∃ M', memStore32 M911 (outp + 0xC) v891 = M' := ⟨_, rfl⟩
  rw [hM912] at u912
  have hc912 : CodeIn M912 B p256ScalarMulCode := by rw [← hM912]; exact hc911.store32 (frm_sep' sOC (by decide))
  have fr912 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M912 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM912, memStore32_get_sep (frm_sep' hx3 (by decide)), fr911 x hx1 hx2 hx3]
  obtain ⟨n913, v913, d913, hv913, u913⟩ := u912.aluG hc912 psm_at_b5e (off' := 0xB60) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv913
  obtain ⟨n914, d914, u914⟩ := u913.swG hc912 psm_at_b60 (off' := 0xB62) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hO (k := 16) (by decide)) (a := outp + 0x10) (v := v896)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M914, hM914⟩ : ∃ M', memStore32 M912 (outp + 0x10) v896 = M' := ⟨_, rfl⟩
  rw [hM914] at u914
  have hc914 : CodeIn M914 B p256ScalarMulCode := by rw [← hM914]; exact hc912.store32 (frm_sep' sOC (by decide))
  have fr914 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M914 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM914, memStore32_get_sep (frm_sep' hx3 (by decide)), fr912 x hx1 hx2 hx3]
  obtain ⟨n915, d915, u915⟩ := u914.swG hc914 psm_at_b62 (off' := 0xB64) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hO (k := 20) (by decide)) (a := outp + 0x14) (v := v901)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M915, hM915⟩ : ∃ M', memStore32 M914 (outp + 0x14) v901 = M' := ⟨_, rfl⟩
  rw [hM915] at u915
  have hc915 : CodeIn M915 B p256ScalarMulCode := by rw [← hM915]; exact hc914.store32 (frm_sep' sOC (by decide))
  have fr915 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M915 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM915, memStore32_get_sep (frm_sep' hx3 (by decide)), fr914 x hx1 hx2 hx3]
  have qo2 : reg n915 sp = F := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n915 (3 : Fin 32) = G3 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n915 (4 : Fin 32) = G4 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n915 (5 : Fin 32) = v603 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n915 (6 : Fin 32) = v525 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n915 (7 : Fin 32) = v506 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n915 (8 : Fin 32) = v901 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n915 (9 : Fin 32) = outp := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n915 a0 = v879 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n915 a1 = v913 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n915 a2 = v885 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n915 a3 = v907 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n915 a4 = v891 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n915 a5 = v896 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n915 a6 = v875 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n915 a7 = v693 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n915 (18 : Fin 32) = v906 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n915 (19 : Fin 32) = v876 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n915 (20 : Fin 32) = v899 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n915 (21 : Fin 32) = v516 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n915 (22 : Fin 32) = v522 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n915 (23 : Fin 32) = v510 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n915 (24 : Fin 32) = v509 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n915 (25 : Fin 32) = v882 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n915 (26 : Fin 32) = v894 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n915 (27 : Fin 32) = v864 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n915 (28 : Fin 32) = v761 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n915 (29 : Fin 32) = v494 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n915 (30 : Fin 32) = v615 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n915 (31 : Fin 32) = v755 := by rw [u915.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so28 : memLoad32 M915 (F + 0x28) = outp := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x28) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x28) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x28) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x28) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x28) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x28) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), sl28]
  have so2C : memLoad32 M915 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x2C) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x2C) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x2C) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x2C) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x2C) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x2C) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), sl2C]
  have so30 : memLoad32 M915 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x30) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x30) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x30) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x30) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x30) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x30) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), sl30]
  have so34 : memLoad32 M915 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x34) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x34) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x34) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x34) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x34) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x34) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), sl34]
  have so38 : memLoad32 M915 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x38) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x38) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x38) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x38) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x38) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x38) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), sl38]
  have so3C : memLoad32 M915 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x3C) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x3C) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x3C) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x3C) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x3C) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x3C) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), sl3C]
  have so40 : memLoad32 M915 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x40) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x40) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x40) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x40) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x40) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x40) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), sl40]
  have so44 : memLoad32 M915 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x44) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x44) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x44) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x44) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x44) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x44) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), sl44]
  have so48 : memLoad32 M915 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x48) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x48) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x48) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x48) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x48) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x48) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), sl48]
  have so4C : memLoad32 M915 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x4C) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x4C) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x4C) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x4C) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x4C) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x4C) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), sl4C]
  have so50 : memLoad32 M915 (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x50) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 80) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x50) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 80) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x50) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 80) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x50) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 80) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x50) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 80) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x50) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 80) (l := 4) (by decide)), sl50]
  have so54 : memLoad32 M915 (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x54) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 84) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x54) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 84) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x54) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 84) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x54) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 84) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x54) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 84) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x54) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 84) (l := 4) (by decide)), sl54]
  have so58 : memLoad32 M915 (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x58) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 88) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x58) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 88) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x58) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 88) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x58) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 88) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x58) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 88) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x58) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 88) (l := 4) (by decide)), sl58]
  have so5C : memLoad32 M915 (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x5C) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 92) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x5C) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 92) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x5C) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 92) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x5C) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 92) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x5C) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 92) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x5C) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 92) (l := 4) (by decide)), sl5C]
  have so60 : memLoad32 M915 (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x60) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 96) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x60) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 96) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x60) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 96) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x60) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 96) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x60) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 96) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x60) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 96) (l := 4) (by decide)), sl60]
  have so64 : memLoad32 M915 (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x64) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 100) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x64) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 100) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x64) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 100) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x64) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 100) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x64) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 100) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x64) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 100) (l := 4) (by decide)), sl64]
  have so68 : memLoad32 M915 (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x68) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 104) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x68) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 104) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x68) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 104) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x68) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 104) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x68) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 104) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x68) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 104) (l := 4) (by decide)), sl68]
  have so6C : memLoad32 M915 (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x6C) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 108) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x6C) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 108) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x6C) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 108) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x6C) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 108) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x6C) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 108) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x6C) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 108) (l := 4) (by decide)), sl6C]
  have so70 : memLoad32 M915 (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x70) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 112) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x70) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 112) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x70) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 112) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x70) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 112) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x70) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 112) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x70) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 112) (l := 4) (by decide)), sl70]
  have so74 : memLoad32 M915 (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x74) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 116) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x74) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 116) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x74) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 116) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x74) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 116) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x74) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 116) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x74) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 116) (l := 4) (by decide)), sl74]
  have so78 : memLoad32 M915 (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x78) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 120) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x78) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 120) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x78) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 120) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x78) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 120) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x78) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 120) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x78) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 120) (l := 4) (by decide)), sl78]
  have so7C : memLoad32 M915 (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x7C) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 124) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x7C) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 124) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x7C) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 124) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x7C) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 124) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x7C) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 124) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x7C) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 124) (l := 4) (by decide)), sl7C]
  have so80 : memLoad32 M915 (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x80) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 128) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x80) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 128) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x80) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 128) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x80) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 128) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x80) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 128) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x80) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 128) (l := 4) (by decide)), sl80]
  have so84 : memLoad32 M915 (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x84) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 132) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x84) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 132) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x84) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 132) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x84) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 132) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x84) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 132) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x84) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 132) (l := 4) (by decide)), sl84]
  have so88 : memLoad32 M915 (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x88) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 136) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x88) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 136) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x88) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 136) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x88) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 136) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x88) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 136) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x88) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 136) (l := 4) (by decide)), sl88]
  have so8C : memLoad32 M915 (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x8C) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 140) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x8C) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 140) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x8C) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 140) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x8C) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 140) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x8C) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 140) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x8C) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 140) (l := 4) (by decide)), sl8C]
  have so90 : memLoad32 M915 (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x90) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 144) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x90) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 144) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x90) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 144) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x90) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 144) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x90) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 144) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x90) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 144) (l := 4) (by decide)), sl90]
  have so94 : memLoad32 M915 (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x94) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 148) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x94) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 148) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x94) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 148) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x94) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 148) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x94) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 148) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x94) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 148) (l := 4) (by decide)), sl94]
  have so98 : memLoad32 M915 (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x98) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 152) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x98) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 152) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x98) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 152) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x98) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 152) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x98) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 152) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x98) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 152) (l := 4) (by decide)), sl98]
  have so9C : memLoad32 M915 (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (F + 0x9C) 4 from (sOF.sub (c := 20) (l := 4) (by decide)).subR (c := 156) (l := 4) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (F + 0x9C) 4 from (sOF.sub (c := 16) (l := 4) (by decide)).subR (c := 156) (l := 4) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (F + 0x9C) 4 from (sOF.sub (c := 12) (l := 4) (by decide)).subR (c := 156) (l := 4) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (F + 0x9C) 4 from (sOF.sub (c := 8) (l := 4) (by decide)).subR (c := 156) (l := 4) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (F + 0x9C) 4 from (sOF.sub (c := 4) (l := 4) (by decide)).subR (c := 156) (l := 4) (by decide)), ← hM909, memLoad32_store32_sep (show Sep (outp + 0x0) 4 (F + 0x9C) 4 from (sOF.sub (c := 0) (l := 4) (by decide)).subR (c := 156) (l := 4) (by decide)), sl9C]
  have sooutp0 : memLoad32 M915 (outp + 0x0) = v875 := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (outp + 0x0) 4 from sep_offsets outp (c := 20) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (outp + 0x0) 4 from sep_offsets outp (c := 16) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (outp + 0x0) 4 from sep_offsets outp (c := 12) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (outp + 0x0) 4 from sep_offsets outp (c := 8) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM910, memLoad32_store32_sep (show Sep (outp + 0x4) 4 (outp + 0x0) 4 from sep_offsets outp (c := 4) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM909, memLoad32_store32_same]
  have sooutp4 : memLoad32 M915 (outp + 0x4) = v879 := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (outp + 0x4) 4 from sep_offsets outp (c := 20) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (outp + 0x4) 4 from sep_offsets outp (c := 16) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (outp + 0x4) 4 from sep_offsets outp (c := 12) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM911, memLoad32_store32_sep (show Sep (outp + 0x8) 4 (outp + 0x4) 4 from sep_offsets outp (c := 8) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM910, memLoad32_store32_same]
  have sooutp8 : memLoad32 M915 (outp + 0x8) = v885 := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (outp + 0x8) 4 from sep_offsets outp (c := 20) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (outp + 0x8) 4 from sep_offsets outp (c := 16) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM912, memLoad32_store32_sep (show Sep (outp + 0xC) 4 (outp + 0x8) 4 from sep_offsets outp (c := 12) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM911, memLoad32_store32_same]
  have sooutpC : memLoad32 M915 (outp + 0xC) = v891 := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (outp + 0xC) 4 from sep_offsets outp (c := 20) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM914, memLoad32_store32_sep (show Sep (outp + 0x10) 4 (outp + 0xC) 4 from sep_offsets outp (c := 16) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM912, memLoad32_store32_same]
  have sooutp10 : memLoad32 M915 (outp + 0x10) = v896 := by
    rw [← hM915, memLoad32_store32_sep (show Sep (outp + 0x14) 4 (outp + 0x10) 4 from sep_offsets outp (c := 20) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM914, memLoad32_store32_same]
  have sooutp14 : memLoad32 M915 (outp + 0x14) = v901 := by
    rw [← hM915, memLoad32_store32_same]
  exact ⟨n915, M915, v880, v881, v882, v883, v884, v885, v886, v887, v889, v890, v891, v892, v893, v894, v895, v896, v897, v898, v899, v900, v901, v902, v903, v904, v905, v906, v907, v913, (.cons d880 (.cons d881 (.cons d882 (.cons d883 (.cons d884 (.cons d885 (.cons d886 (.cons d887 (.cons d888 (.cons d889 (.cons d890 (.cons d891 (.cons d892 (.cons d893 (.cons d894 (.cons d895 (.cons d896 (.cons d897 (.cons d898 (.cons d899 (.cons d900 (.cons d901 (.cons d902 (.cons d903 (.cons d904 (.cons d905 (.cons d906 (.cons d907 (.cons d908 (.cons d909 (.cons d910 (.cons d911 (.cons d912 (.cons d913 (.cons d914 (.single d915)))))))))))))))))))))))))))))))))))), u915.self, hc915, fr915, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, sooutp0, sooutp4, sooutp8, sooutpC, sooutp10, sooutp14, hv880, hv881, hv882, hv883, hv884, hv885, hv886, hv887, hv889, hv890, hv891, hv892, hv893, hv894, hv895, hv896, hv897, hv898, hv899, hv900, hv901, hv902, hv903, hv904, hv905, hv906, hv907, hv913⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g23 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v494 v506 v509 v510 v516 v522 v525 v603 v615 v693 v755 v761 v864 v875 v876 v879 v882 v885 v891 v894 v896 v899 v901 v906 v907 v913 : Word}
    (s : St Mi B n 0xB64 (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v603)
    (q6 : reg n (6 : Fin 32) = v525)
    (q7 : reg n (7 : Fin 32) = v506)
    (q8 : reg n (8 : Fin 32) = v901)
    (q9 : reg n (9 : Fin 32) = outp)
    (q10 : reg n a0 = v879)
    (q11 : reg n a1 = v913)
    (q12 : reg n a2 = v885)
    (q13 : reg n a3 = v907)
    (q14 : reg n a4 = v891)
    (q15 : reg n a5 = v896)
    (q16 : reg n a6 = v875)
    (q17 : reg n a7 = v693)
    (q18 : reg n (18 : Fin 32) = v906)
    (q19 : reg n (19 : Fin 32) = v876)
    (q20 : reg n (20 : Fin 32) = v899)
    (q21 : reg n (21 : Fin 32) = v516)
    (q22 : reg n (22 : Fin 32) = v522)
    (q23 : reg n (23 : Fin 32) = v510)
    (q24 : reg n (24 : Fin 32) = v509)
    (q25 : reg n (25 : Fin 32) = v882)
    (q26 : reg n (26 : Fin 32) = v894)
    (q27 : reg n (27 : Fin 32) = v864)
    (q28 : reg n (28 : Fin 32) = v761)
    (q29 : reg n (29 : Fin 32) = v494)
    (q30 : reg n (30 : Fin 32) = v615)
    (q31 : reg n (31 : Fin 32) = v755)
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
    (sloutp0 : memLoad32 Mi (outp + 0x0) = v875)
    (sloutp4 : memLoad32 Mi (outp + 0x4) = v879)
    (sloutp8 : memLoad32 Mi (outp + 0x8) = v885)
    (sloutpC : memLoad32 Mi (outp + 0xC) = v891)
    (sloutp10 : memLoad32 Mi (outp + 0x10) = v896)
    (sloutp14 : memLoad32 Mi (outp + 0x14) = v901)
    : ∃ (n' : Machine) (M' : Word → BitVec 8),
      Steps n n' ∧
      St M' B n' 0xB6A (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v603 ∧
      reg n' (6 : Fin 32) = v525 ∧
      reg n' (7 : Fin 32) = v506 ∧
      reg n' (8 : Fin 32) = v901 ∧
      reg n' (9 : Fin 32) = outp ∧
      reg n' a0 = v879 ∧
      reg n' a1 = v913 ∧
      reg n' a2 = v885 ∧
      reg n' a3 = v907 ∧
      reg n' a4 = v891 ∧
      reg n' a5 = v896 ∧
      reg n' a6 = v875 ∧
      reg n' a7 = v693 ∧
      reg n' (18 : Fin 32) = v906 ∧
      reg n' (19 : Fin 32) = v876 ∧
      reg n' (20 : Fin 32) = v899 ∧
      reg n' (21 : Fin 32) = v516 ∧
      reg n' (22 : Fin 32) = v522 ∧
      reg n' (23 : Fin 32) = v510 ∧
      reg n' (24 : Fin 32) = v509 ∧
      reg n' (25 : Fin 32) = v882 ∧
      reg n' (26 : Fin 32) = v894 ∧
      reg n' (27 : Fin 32) = v864 ∧
      reg n' (28 : Fin 32) = v761 ∧
      reg n' (29 : Fin 32) = v494 ∧
      reg n' (30 : Fin 32) = v615 ∧
      reg n' (31 : Fin 32) = v755 ∧
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
      memLoad32 M' (outp + 0x0) = v875 ∧
      memLoad32 M' (outp + 0x4) = v879 ∧
      memLoad32 M' (outp + 0x8) = v885 ∧
      memLoad32 M' (outp + 0xC) = v891 ∧
      memLoad32 M' (outp + 0x10) = v896 ∧
      memLoad32 M' (outp + 0x14) = v901 ∧
      memLoad32 M' (outp + 0x18) = v906 ∧
      memLoad32 M' (outp + 0x1C) = v913 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n916, d916, u916⟩ := s.swG hc psm_at_b64 (off' := 0xB68) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hO (k := 24) (by decide)) (a := outp + 0x18) (v := v906)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M916, hM916⟩ : ∃ M', memStore32 Mi (outp + 0x18) v906 = M' := ⟨_, rfl⟩
  rw [hM916] at u916
  have hc916 : CodeIn M916 B p256ScalarMulCode := by rw [← hM916]; exact hc.store32 (frm_sep' sOC (by decide))
  have fr916 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M916 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM916, memStore32_get_sep (frm_sep' hx3 (by decide)), fr x hx1 hx2 hx3]
  obtain ⟨n917, d917, u917⟩ := u916.swG hc916 psm_at_b68 (off' := 0xB6A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hO (k := 28) (by decide)) (a := outp + 0x1C) (v := v913)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M917, hM917⟩ : ∃ M', memStore32 M916 (outp + 0x1C) v913 = M' := ⟨_, rfl⟩
  rw [hM917] at u917
  have hc917 : CodeIn M917 B p256ScalarMulCode := by rw [← hM917]; exact hc916.store32 (frm_sep' sOC (by decide))
  have fr917 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M917 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM917, memStore32_get_sep (frm_sep' hx3 (by decide)), fr916 x hx1 hx2 hx3]
  have qo2 : reg n917 sp = F := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n917 (3 : Fin 32) = G3 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n917 (4 : Fin 32) = G4 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n917 (5 : Fin 32) = v603 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n917 (6 : Fin 32) = v525 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n917 (7 : Fin 32) = v506 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n917 (8 : Fin 32) = v901 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n917 (9 : Fin 32) = outp := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n917 a0 = v879 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n917 a1 = v913 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n917 a2 = v885 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n917 a3 = v907 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n917 a4 = v891 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n917 a5 = v896 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n917 a6 = v875 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n917 a7 = v693 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n917 (18 : Fin 32) = v906 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n917 (19 : Fin 32) = v876 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n917 (20 : Fin 32) = v899 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n917 (21 : Fin 32) = v516 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n917 (22 : Fin 32) = v522 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n917 (23 : Fin 32) = v510 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n917 (24 : Fin 32) = v509 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n917 (25 : Fin 32) = v882 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n917 (26 : Fin 32) = v894 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n917 (27 : Fin 32) = v864 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n917 (28 : Fin 32) = v761 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n917 (29 : Fin 32) = v494 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n917 (30 : Fin 32) = v615 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n917 (31 : Fin 32) = v755 := by rw [u917.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so28 : memLoad32 M917 (F + 0x28) = outp := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x28) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x28) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 40) (l := 4) (by decide)), sl28]
  have so2C : memLoad32 M917 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x2C) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x2C) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 44) (l := 4) (by decide)), sl2C]
  have so30 : memLoad32 M917 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x30) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x30) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 48) (l := 4) (by decide)), sl30]
  have so34 : memLoad32 M917 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x34) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x34) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 52) (l := 4) (by decide)), sl34]
  have so38 : memLoad32 M917 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x38) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x38) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 56) (l := 4) (by decide)), sl38]
  have so3C : memLoad32 M917 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x3C) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x3C) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 60) (l := 4) (by decide)), sl3C]
  have so40 : memLoad32 M917 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x40) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x40) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 64) (l := 4) (by decide)), sl40]
  have so44 : memLoad32 M917 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x44) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x44) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 68) (l := 4) (by decide)), sl44]
  have so48 : memLoad32 M917 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x48) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x48) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 72) (l := 4) (by decide)), sl48]
  have so4C : memLoad32 M917 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x4C) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x4C) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 76) (l := 4) (by decide)), sl4C]
  have so50 : memLoad32 M917 (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x50) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 80) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x50) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 80) (l := 4) (by decide)), sl50]
  have so54 : memLoad32 M917 (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x54) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 84) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x54) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 84) (l := 4) (by decide)), sl54]
  have so58 : memLoad32 M917 (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x58) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 88) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x58) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 88) (l := 4) (by decide)), sl58]
  have so5C : memLoad32 M917 (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x5C) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 92) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x5C) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 92) (l := 4) (by decide)), sl5C]
  have so60 : memLoad32 M917 (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x60) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 96) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x60) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 96) (l := 4) (by decide)), sl60]
  have so64 : memLoad32 M917 (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x64) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 100) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x64) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 100) (l := 4) (by decide)), sl64]
  have so68 : memLoad32 M917 (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x68) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 104) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x68) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 104) (l := 4) (by decide)), sl68]
  have so6C : memLoad32 M917 (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x6C) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 108) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x6C) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 108) (l := 4) (by decide)), sl6C]
  have so70 : memLoad32 M917 (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x70) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 112) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x70) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 112) (l := 4) (by decide)), sl70]
  have so74 : memLoad32 M917 (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x74) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 116) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x74) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 116) (l := 4) (by decide)), sl74]
  have so78 : memLoad32 M917 (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x78) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 120) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x78) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 120) (l := 4) (by decide)), sl78]
  have so7C : memLoad32 M917 (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x7C) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 124) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x7C) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 124) (l := 4) (by decide)), sl7C]
  have so80 : memLoad32 M917 (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x80) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 128) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x80) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 128) (l := 4) (by decide)), sl80]
  have so84 : memLoad32 M917 (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x84) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 132) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x84) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 132) (l := 4) (by decide)), sl84]
  have so88 : memLoad32 M917 (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x88) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 136) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x88) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 136) (l := 4) (by decide)), sl88]
  have so8C : memLoad32 M917 (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x8C) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 140) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x8C) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 140) (l := 4) (by decide)), sl8C]
  have so90 : memLoad32 M917 (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x90) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 144) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x90) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 144) (l := 4) (by decide)), sl90]
  have so94 : memLoad32 M917 (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x94) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 148) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x94) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 148) (l := 4) (by decide)), sl94]
  have so98 : memLoad32 M917 (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x98) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 152) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x98) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 152) (l := 4) (by decide)), sl98]
  have so9C : memLoad32 M917 (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (F + 0x9C) 4 from (sOF.sub (c := 28) (l := 4) (by decide)).subR (c := 156) (l := 4) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (F + 0x9C) 4 from (sOF.sub (c := 24) (l := 4) (by decide)).subR (c := 156) (l := 4) (by decide)), sl9C]
  have sooutp0 : memLoad32 M917 (outp + 0x0) = v875 := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (outp + 0x0) 4 from sep_offsets outp (c := 28) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (outp + 0x0) 4 from sep_offsets outp (c := 24) (n := 4) (d := 0) (k := 4) (by decide) (by decide) (by decide)), sloutp0]
  have sooutp4 : memLoad32 M917 (outp + 0x4) = v879 := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (outp + 0x4) 4 from sep_offsets outp (c := 28) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (outp + 0x4) 4 from sep_offsets outp (c := 24) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)), sloutp4]
  have sooutp8 : memLoad32 M917 (outp + 0x8) = v885 := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (outp + 0x8) 4 from sep_offsets outp (c := 28) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (outp + 0x8) 4 from sep_offsets outp (c := 24) (n := 4) (d := 8) (k := 4) (by decide) (by decide) (by decide)), sloutp8]
  have sooutpC : memLoad32 M917 (outp + 0xC) = v891 := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (outp + 0xC) 4 from sep_offsets outp (c := 28) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (outp + 0xC) 4 from sep_offsets outp (c := 24) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), sloutpC]
  have sooutp10 : memLoad32 M917 (outp + 0x10) = v896 := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (outp + 0x10) 4 from sep_offsets outp (c := 28) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (outp + 0x10) 4 from sep_offsets outp (c := 24) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sloutp10]
  have sooutp14 : memLoad32 M917 (outp + 0x14) = v901 := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (outp + 0x14) 4 from sep_offsets outp (c := 28) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), ← hM916, memLoad32_store32_sep (show Sep (outp + 0x18) 4 (outp + 0x14) 4 from sep_offsets outp (c := 24) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), sloutp14]
  have sooutp18 : memLoad32 M917 (outp + 0x18) = v906 := by
    rw [← hM917, memLoad32_store32_sep (show Sep (outp + 0x1C) 4 (outp + 0x18) 4 from sep_offsets outp (c := 28) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), ← hM916, memLoad32_store32_same]
  have sooutp1C : memLoad32 M917 (outp + 0x1C) = v913 := by
    rw [← hM917, memLoad32_store32_same]
  exact ⟨n917, M917, (.cons d916 (.single d917)), u917.self, hc917, fr917, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, sooutp0, sooutp4, sooutp8, sooutpC, sooutp10, sooutp14, sooutp18, sooutp1C⟩

end C3.RV32
