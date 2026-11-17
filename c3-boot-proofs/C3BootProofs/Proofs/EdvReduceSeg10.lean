import C3BootProofs.Proofs.EdvReduceFacts

/-! # The inlined `Scalar::reduce` in `ed25519_verify`, segments 28 to 32

Each theorem steps 40 instructions. `scripts/gen-ev-reduce.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g28 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v150 v174 v199 v203 v206 v231 v239 v264 v274 v279 v302 v335 v341 v352 v357 v405 v419 v467 v481 v485 v540 v545 v557 v559 v572 v579 v582 v593 v656 v667 v669 v680 v682 v689 v691 v693 v695 v702 v706 v708 v710 v713 v715 v717 v722 v765 v797 v803 v819 v823 v831 v833 v851 v861 v869 v873 v874 v876 v878 v879 : Word}
    (s : St Mi B n 0xC16 (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v357)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v831)
    (q6 : reg n (6 : Fin 32) = v797)
    (q7 : reg n (7 : Fin 32) = v873)
    (q8 : reg n (8 : Fin 32) = v851)
    (q9 : reg n (9 : Fin 32) = v861)
    (q10 : reg n a0 = v878)
    (q11 : reg n a1 = v656)
    (q12 : reg n a2 = v833)
    (q13 : reg n a3 = v874)
    (q14 : reg n a4 = v876)
    (q15 : reg n a5 = v879)
    (q16 : reg n a6 = v869)
    (q17 : reg n a7 = v485)
    (q18 : reg n (18 : Fin 32) = v7)
    (q19 : reg n (19 : Fin 32) = v593)
    (q20 : reg n (20 : Fin 32) = v722)
    (q21 : reg n (21 : Fin 32) = v485)
    (q22 : reg n (22 : Fin 32) = v557)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v150)
    (q25 : reg n (25 : Fin 32) = v174)
    (q26 : reg n (26 : Fin 32) = v545)
    (q27 : reg n (27 : Fin 32) = v765)
    (q28 : reg n (28 : Fin 32) = v823)
    (q29 : reg n (29 : Fin 32) = v819)
    (q30 : reg n (30 : Fin 32) = v239)
    (q31 : reg n (31 : Fin 32) = v481)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (sl58 : memLoad32 Mi (F + 0x58) = v708)
    (sl5C : memLoad32 Mi (F + 0x5C) = v706)
    (sl60 : memLoad32 Mi (F + 0x60) = v680)
    (sl64 : memLoad32 Mi (F + 0x64) = v682)
    (sl68 : memLoad32 Mi (F + 0x68) = v689)
    (sl6C : memLoad32 Mi (F + 0x6C) = v691)
    (sl70 : memLoad32 Mi (F + 0x70) = v669)
    (sl74 : memLoad32 Mi (F + 0x74) = v667)
    (sl7C : memLoad32 Mi (F + 0x7C) = v717)
    (sl80 : memLoad32 Mi (F + 0x80) = v715)
    (sl84 : memLoad32 Mi (F + 0x84) = v572)
    (sl88 : memLoad32 Mi (F + 0x88) = v695)
    (sl8C : memLoad32 Mi (F + 0x8C) = v559)
    (sl98 : memLoad32 Mi (F + 0x98) = v352)
    (sl9C : memLoad32 Mi (F + 0x9C) = v713)
    (slA8 : memLoad32 Mi (F + 0xA8) = v279)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v880 v881 v882 v884 v885 v886 v887 v888 v889 v890 v892 v893 v894 v895 v896 v897 v898 v899 v900 v901 v902 v903 v904 v905 v906 v907 v908 v909 v910 v911 v912 v913 v914 v915 v916 v919 : Word),
      Steps n n' ∧
      St M' B n' 0xC8C (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v357 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v831 ∧
      reg n' (6 : Fin 32) = v239 ∧
      reg n' (7 : Fin 32) = v873 ∧
      reg n' (8 : Fin 32) = v898 ∧
      reg n' (9 : Fin 32) = v904 ∧
      reg n' a0 = v916 ∧
      reg n' a1 = v915 ∧
      reg n' a2 = v908 ∧
      reg n' a3 = v919 ∧
      reg n' a4 = v206 ∧
      reg n' a5 = v680 ∧
      reg n' a6 = v869 ∧
      reg n' a7 = v485 ∧
      reg n' (18 : Fin 32) = v7 ∧
      reg n' (19 : Fin 32) = v896 ∧
      reg n' (20 : Fin 32) = v722 ∧
      reg n' (21 : Fin 32) = v485 ∧
      reg n' (22 : Fin 32) = v557 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v150 ∧
      reg n' (25 : Fin 32) = v174 ∧
      reg n' (26 : Fin 32) = v545 ∧
      reg n' (27 : Fin 32) = v882 ∧
      reg n' (28 : Fin 32) = v823 ∧
      reg n' (29 : Fin 32) = v819 ∧
      reg n' (30 : Fin 32) = v897 ∧
      reg n' (31 : Fin 32) = v481 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0x58) = v708 ∧
      memLoad32 M' (F + 0x5C) = v706 ∧
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
      memLoad32 M' (F + 0xC8) = v335 ∧
      memLoad32 M' (F + 0xCC) = v264 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xE8) = v419 ∧
      memLoad32 M' (F + 0xEC) = v341 ∧
      memLoad32 M' (F + 0xFC) = v579 ∧
      memLoad32 M' (F + 0x100) = v540 ∧
      memLoad32 M' (F + 0x104) = v710 ∧
      memLoad32 M' (F + 0x108) = v203 ∧
      memLoad32 M' (F + 0x10C) = v274 ∧
      memLoad32 M' (F + 0x110) = v702 ∧
      memLoad32 M' (F + 0x118) = v803 ∧
      memLoad32 M' (F + 0x11C) = v231 ∧
      aluEval .add v874 v876 = v880 ∧
      aluEval .mul v485 v878 = v881 ∧
      aluEval .add 0 0x14D = v882 ∧
      aluEval .sll v199 0x14 = v884 ∧
      aluEval .sub v861 v481 = v885 ∧
      aluEval .add v884 v885 = v886 ∧
      aluEval .mul v557 v302 = v887 ∧
      aluEval .sltu v886 v885 = v888 ∧
      aluEval .mulhu v557 v302 = v889 ∧
      aluEval .add v880 v888 = v890 ∧
      aluEval .mul v722 v239 = v892 ∧
      aluEval .add v890 v879 = v893 ∧
      aluEval .mulhu v722 v239 = v894 ∧
      aluEval .add v881 v886 = v895 ∧
      aluEval .mul v819 v174 = v896 ∧
      aluEval .mulhu v819 v174 = v897 ∧
      aluEval .sltu v895 v886 = v898 ∧
      aluEval .add v893 v898 = v899 ∧
      aluEval .add v887 v895 = v900 ∧
      aluEval .add v889 v899 = v901 ∧
      aluEval .sltu v900 v895 = v902 ∧
      aluEval .add v901 v902 = v903 ∧
      aluEval .add v892 v900 = v904 ∧
      aluEval .add v903 v894 = v905 ∧
      aluEval .sltu v904 v900 = v906 ∧
      aluEval .add v906 v905 = v907 ∧
      aluEval .add v904 v896 = v908 ∧
      aluEval .add v907 v897 = v909 ∧
      aluEval .sltu v908 v904 = v910 ∧
      aluEval .add v909 v910 = v911 ∧
      aluEval .srl v869 0x1D = v912 ∧
      aluEval .sll v873 0x3 = v913 ∧
      aluEval .srl v873 0x1D = v914 ∧
      aluEval .or v912 v913 = v915 ∧
      aluEval .add v911 v914 = v916 ∧
      aluEval .sltu v680 v206 = v919 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n880, v880, d880, hv880, u880⟩ := s.aluG hc ev_at_c16 (off' := 0xC18) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv880
  obtain ⟨n881, v881, d881, hv881, u881⟩ := u880.aluG hc ev_at_c18 (off' := 0xC1C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv881
  obtain ⟨n882, v882, d882, hv882, u882⟩ := u881.aluImmG hc ev_at_c1c (off' := 0xC20) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv882
  obtain ⟨n883, d883, u883⟩ := u882.lwE hc ev_at_c20 (off' := 0xC22) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 196) (by decide)) (v := v199)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slC4])
  obtain ⟨n884, v884, d884, hv884, u884⟩ := u883.aluImmG hc ev_at_c22 (off' := 0xC24) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv884
  obtain ⟨n885, v885, d885, hv885, u885⟩ := u884.aluG hc ev_at_c24 (off' := 0xC28) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv885
  obtain ⟨n886, v886, d886, hv886, u886⟩ := u885.aluG hc ev_at_c28 (off' := 0xC2A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv886
  obtain ⟨n887, v887, d887, hv887, u887⟩ := u886.aluG hc ev_at_c2a (off' := 0xC2E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv887
  obtain ⟨n888, v888, d888, hv888, u888⟩ := u887.aluG hc ev_at_c2e (off' := 0xC32) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv888
  obtain ⟨n889, v889, d889, hv889, u889⟩ := u888.aluG hc ev_at_c32 (off' := 0xC36) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv889
  obtain ⟨n890, v890, d890, hv890, u890⟩ := u889.aluG hc ev_at_c36 (off' := 0xC38) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv890
  obtain ⟨n891, d891, u891⟩ := u890.aluE hc ev_at_c38 (off' := 0xC3A) (by decide) (v := v239)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n892, v892, d892, hv892, u892⟩ := u891.aluG hc ev_at_c3a (off' := 0xC3E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv892
  obtain ⟨n893, v893, d893, hv893, u893⟩ := u892.aluG hc ev_at_c3e (off' := 0xC40) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv893
  obtain ⟨n894, v894, d894, hv894, u894⟩ := u893.aluG hc ev_at_c40 (off' := 0xC44) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv894
  obtain ⟨n895, v895, d895, hv895, u895⟩ := u894.aluG hc ev_at_c44 (off' := 0xC46) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv895
  obtain ⟨n896, v896, d896, hv896, u896⟩ := u895.aluG hc ev_at_c46 (off' := 0xC4A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv896
  obtain ⟨n897, v897, d897, hv897, u897⟩ := u896.aluG hc ev_at_c4a (off' := 0xC4E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv897
  obtain ⟨n898, v898, d898, hv898, u898⟩ := u897.aluG hc ev_at_c4e (off' := 0xC52) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv898
  obtain ⟨n899, v899, d899, hv899, u899⟩ := u898.aluG hc ev_at_c52 (off' := 0xC54) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv899
  obtain ⟨n900, v900, d900, hv900, u900⟩ := u899.aluG hc ev_at_c54 (off' := 0xC56) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv900
  obtain ⟨n901, v901, d901, hv901, u901⟩ := u900.aluG hc ev_at_c56 (off' := 0xC58) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv901
  obtain ⟨n902, v902, d902, hv902, u902⟩ := u901.aluG hc ev_at_c58 (off' := 0xC5C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv902
  obtain ⟨n903, v903, d903, hv903, u903⟩ := u902.aluG hc ev_at_c5c (off' := 0xC5E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv903
  obtain ⟨n904, v904, d904, hv904, u904⟩ := u903.aluG hc ev_at_c5e (off' := 0xC60) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv904
  obtain ⟨n905, v905, d905, hv905, u905⟩ := u904.aluG hc ev_at_c60 (off' := 0xC62) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv905
  obtain ⟨n906, v906, d906, hv906, u906⟩ := u905.aluG hc ev_at_c62 (off' := 0xC66) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv906
  obtain ⟨n907, v907, d907, hv907, u907⟩ := u906.aluG hc ev_at_c66 (off' := 0xC68) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv907
  obtain ⟨n908, v908, d908, hv908, u908⟩ := u907.aluG hc ev_at_c68 (off' := 0xC6C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv908
  obtain ⟨n909, v909, d909, hv909, u909⟩ := u908.aluG hc ev_at_c6c (off' := 0xC6E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv909
  obtain ⟨n910, v910, d910, hv910, u910⟩ := u909.aluG hc ev_at_c6e (off' := 0xC72) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv910
  obtain ⟨n911, v911, d911, hv911, u911⟩ := u910.aluG hc ev_at_c72 (off' := 0xC74) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv911
  obtain ⟨n912, v912, d912, hv912, u912⟩ := u911.aluImmG hc ev_at_c74 (off' := 0xC78) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv912
  obtain ⟨n913, v913, d913, hv913, u913⟩ := u912.aluImmG hc ev_at_c78 (off' := 0xC7C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv913
  obtain ⟨n914, v914, d914, hv914, u914⟩ := u913.aluImmG hc ev_at_c7c (off' := 0xC80) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv914
  obtain ⟨n915, v915, d915, hv915, u915⟩ := u914.aluG hc ev_at_c80 (off' := 0xC82) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv915
  obtain ⟨n916, v916, d916, hv916, u916⟩ := u915.aluG hc ev_at_c82 (off' := 0xC84) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv916
  obtain ⟨n917, d917, u917⟩ := u916.lwE hc ev_at_c84 (off' := 0xC86) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 240) (by decide)) (v := v206)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slF0])
  obtain ⟨n918, d918, u918⟩ := u917.lwE hc ev_at_c86 (off' := 0xC88) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 96) (by decide)) (v := v680)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl60])
  obtain ⟨n919, v919, d919, hv919, u919⟩ := u918.aluG hc ev_at_c88 (off' := 0xC8C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv919
  have qo1 : reg n919 ra = v357 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n919 sp = F := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n919 (3 : Fin 32) = G3 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n919 (4 : Fin 32) = G4 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n919 (5 : Fin 32) = v831 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n919 (6 : Fin 32) = v239 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n919 (7 : Fin 32) = v873 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n919 (8 : Fin 32) = v898 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n919 (9 : Fin 32) = v904 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n919 a0 = v916 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n919 a1 = v915 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n919 a2 = v908 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n919 a3 = v919 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n919 a4 = v206 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n919 a5 = v680 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n919 a6 = v869 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n919 a7 = v485 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n919 (18 : Fin 32) = v7 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n919 (19 : Fin 32) = v896 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n919 (20 : Fin 32) = v722 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n919 (21 : Fin 32) = v485 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n919 (22 : Fin 32) = v557 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n919 (23 : Fin 32) = v302 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n919 (24 : Fin 32) = v150 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n919 (25 : Fin 32) = v174 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n919 (26 : Fin 32) = v545 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n919 (27 : Fin 32) = v882 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n919 (28 : Fin 32) = v823 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n919 (29 : Fin 32) = v819 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n919 (30 : Fin 32) = v897 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n919 (31 : Fin 32) = v481 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mi (F + 0xC) = G21 := by
    rw [slC]
  have so10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [sl10]
  have so58 : memLoad32 Mi (F + 0x58) = v708 := by
    rw [sl58]
  have so5C : memLoad32 Mi (F + 0x5C) = v706 := by
    rw [sl5C]
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
  exact ⟨n919, Mi, v880, v881, v882, v884, v885, v886, v887, v888, v889, v890, v892, v893, v894, v895, v896, v897, v898, v899, v900, v901, v902, v903, v904, v905, v906, v907, v908, v909, v910, v911, v912, v913, v914, v915, v916, v919, (.cons d880 (.cons d881 (.cons d882 (.cons d883 (.cons d884 (.cons d885 (.cons d886 (.cons d887 (.cons d888 (.cons d889 (.cons d890 (.cons d891 (.cons d892 (.cons d893 (.cons d894 (.cons d895 (.cons d896 (.cons d897 (.cons d898 (.cons d899 (.cons d900 (.cons d901 (.cons d902 (.cons d903 (.cons d904 (.cons d905 (.cons d906 (.cons d907 (.cons d908 (.cons d909 (.cons d910 (.cons d911 (.cons d912 (.cons d913 (.cons d914 (.cons d915 (.cons d916 (.cons d917 (.cons d918 (.single d919)))))))))))))))))))))))))))))))))))))))), u919.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so58, so5C, so64, so68, so6C, so70, so74, so7C, so80, so84, so88, so8C, so98, so9C, soA8, soB0, soB4, soBC, soC0, soC8, soCC, soD0, soE8, soEC, soFC, so100, so104, so108, so10C, so110, so118, so11C, hv880, hv881, hv882, hv884, hv885, hv886, hv887, hv888, hv889, hv890, hv892, hv893, hv894, hv895, hv896, hv897, hv898, hv899, hv900, hv901, hv902, hv903, hv904, hv905, hv906, hv907, hv908, hv909, hv910, hv911, hv912, hv913, hv914, hv915, hv916, hv919⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g29 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v150 v174 v203 v206 v231 v239 v264 v274 v279 v302 v335 v341 v352 v357 v405 v419 v467 v481 v485 v540 v545 v557 v559 v572 v579 v582 v667 v669 v680 v682 v689 v691 v693 v695 v702 v706 v708 v710 v713 v715 v717 v722 v803 v819 v823 v831 v869 v873 v882 v896 v897 v898 v904 v908 v915 v916 v919 : Word}
    (s : St Mi B n 0xC8C (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v357)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v831)
    (q6 : reg n (6 : Fin 32) = v239)
    (q7 : reg n (7 : Fin 32) = v873)
    (q8 : reg n (8 : Fin 32) = v898)
    (q9 : reg n (9 : Fin 32) = v904)
    (q10 : reg n a0 = v916)
    (q11 : reg n a1 = v915)
    (q12 : reg n a2 = v908)
    (q13 : reg n a3 = v919)
    (q14 : reg n a4 = v206)
    (q15 : reg n a5 = v680)
    (q16 : reg n a6 = v869)
    (q17 : reg n a7 = v485)
    (q18 : reg n (18 : Fin 32) = v7)
    (q19 : reg n (19 : Fin 32) = v896)
    (q20 : reg n (20 : Fin 32) = v722)
    (q21 : reg n (21 : Fin 32) = v485)
    (q22 : reg n (22 : Fin 32) = v557)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v150)
    (q25 : reg n (25 : Fin 32) = v174)
    (q26 : reg n (26 : Fin 32) = v545)
    (q27 : reg n (27 : Fin 32) = v882)
    (q28 : reg n (28 : Fin 32) = v823)
    (q29 : reg n (29 : Fin 32) = v819)
    (q30 : reg n (30 : Fin 32) = v897)
    (q31 : reg n (31 : Fin 32) = v481)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (sl58 : memLoad32 Mi (F + 0x58) = v708)
    (sl5C : memLoad32 Mi (F + 0x5C) = v706)
    (sl64 : memLoad32 Mi (F + 0x64) = v682)
    (sl68 : memLoad32 Mi (F + 0x68) = v689)
    (sl6C : memLoad32 Mi (F + 0x6C) = v691)
    (sl70 : memLoad32 Mi (F + 0x70) = v669)
    (sl74 : memLoad32 Mi (F + 0x74) = v667)
    (sl7C : memLoad32 Mi (F + 0x7C) = v717)
    (sl80 : memLoad32 Mi (F + 0x80) = v715)
    (sl84 : memLoad32 Mi (F + 0x84) = v572)
    (sl88 : memLoad32 Mi (F + 0x88) = v695)
    (sl8C : memLoad32 Mi (F + 0x8C) = v559)
    (sl98 : memLoad32 Mi (F + 0x98) = v352)
    (sl9C : memLoad32 Mi (F + 0x9C) = v713)
    (slA8 : memLoad32 Mi (F + 0xA8) = v279)
    (slB0 : memLoad32 Mi (F + 0xB0) = v693)
    (slB4 : memLoad32 Mi (F + 0xB4) = v582)
    (slBC : memLoad32 Mi (F + 0xBC) = v467)
    (slC0 : memLoad32 Mi (F + 0xC0) = v405)
    (slC8 : memLoad32 Mi (F + 0xC8) = v335)
    (slCC : memLoad32 Mi (F + 0xCC) = v264)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slE8 : memLoad32 Mi (F + 0xE8) = v419)
    (slEC : memLoad32 Mi (F + 0xEC) = v341)
    (slFC : memLoad32 Mi (F + 0xFC) = v579)
    (sl100 : memLoad32 Mi (F + 0x100) = v540)
    (sl104 : memLoad32 Mi (F + 0x104) = v710)
    (sl108 : memLoad32 Mi (F + 0x108) = v203)
    (sl10C : memLoad32 Mi (F + 0x10C) = v274)
    (sl110 : memLoad32 Mi (F + 0x110) = v702)
    (sl118 : memLoad32 Mi (F + 0x118) = v803)
    (sl11C : memLoad32 Mi (F + 0x11C) = v231)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v920 v922 v924 v926 v927 v929 v931 v932 v934 v935 v937 v939 v940 v941 v943 v944 v945 v946 v948 v949 v950 v952 v953 v954 v955 v957 v958 v959 : Word),
      Steps n n' ∧
      St M' B n' 0xCF8 (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v357 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v831 ∧
      reg n' (6 : Fin 32) = v239 ∧
      reg n' (7 : Fin 32) = v949 ∧
      reg n' (8 : Fin 32) = v935 ∧
      reg n' (9 : Fin 32) = v959 ∧
      reg n' a0 = v916 ∧
      reg n' a1 = v954 ∧
      reg n' a2 = v953 ∧
      reg n' a3 = v955 ∧
      reg n' a4 = v957 ∧
      reg n' a5 = v958 ∧
      reg n' a6 = v945 ∧
      reg n' a7 = v485 ∧
      reg n' (18 : Fin 32) = v7 ∧
      reg n' (19 : Fin 32) = v572 ∧
      reg n' (20 : Fin 32) = v722 ∧
      reg n' (21 : Fin 32) = v485 ∧
      reg n' (22 : Fin 32) = v557 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v150 ∧
      reg n' (25 : Fin 32) = v559 ∧
      reg n' (26 : Fin 32) = v545 ∧
      reg n' (27 : Fin 32) = v882 ∧
      reg n' (28 : Fin 32) = v823 ∧
      reg n' (29 : Fin 32) = v819 ∧
      reg n' (30 : Fin 32) = v897 ∧
      reg n' (31 : Fin 32) = v481 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0x7C) = v717 ∧
      memLoad32 M' (F + 0x80) = v715 ∧
      memLoad32 M' (F + 0x88) = v695 ∧
      memLoad32 M' (F + 0x98) = v352 ∧
      memLoad32 M' (F + 0x9C) = v713 ∧
      memLoad32 M' (F + 0xB0) = v693 ∧
      memLoad32 M' (F + 0xB4) = v582 ∧
      memLoad32 M' (F + 0xBC) = v467 ∧
      memLoad32 M' (F + 0xC0) = v405 ∧
      memLoad32 M' (F + 0xC8) = v335 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xE8) = v419 ∧
      memLoad32 M' (F + 0xEC) = v341 ∧
      memLoad32 M' (F + 0xFC) = v579 ∧
      memLoad32 M' (F + 0x100) = v540 ∧
      memLoad32 M' (F + 0x104) = v710 ∧
      memLoad32 M' (F + 0x10C) = v274 ∧
      memLoad32 M' (F + 0x110) = v702 ∧
      memLoad32 M' (F + 0x118) = v803 ∧
      memLoad32 M' (F + 0x11C) = v231 ∧
      aluEval .sub v680 v206 = v920 ∧
      aluEval .sub v682 v919 = v922 ∧
      aluEval .add v667 v920 = v924 ∧
      aluEval .add v669 v922 = v926 ∧
      aluEval .sltu v924 v920 = v927 ∧
      aluEval .sub v926 v203 = v929 ∧
      aluEval .add v689 v927 = v931 ∧
      aluEval .add v929 v931 = v932 ∧
      aluEval .add v691 v924 = v934 ∧
      aluEval .sltu v934 v924 = v935 ∧
      aluEval .add v706 v934 = v937 ∧
      aluEval .add v708 v935 = v939 ∧
      aluEval .sltu v937 v934 = v940 ∧
      aluEval .add v932 v939 = v941 ∧
      aluEval .sub v940 v572 = v943 ∧
      aluEval .add v941 v943 = v944 ∧
      aluEval .add v908 v915 = v945 ∧
      aluEval .sltu v945 v908 = v946 ∧
      aluEval .sltu v937 v559 = v948 ∧
      aluEval .add v916 v946 = v949 ∧
      aluEval .sub v944 v948 = v950 ∧
      aluEval .srl v279 0xC = v952 ∧
      aluEval .mul v557 v882 = v953 ∧
      aluEval .add v952 v950 = v954 ∧
      aluEval .mulhu v557 v882 = v955 ∧
      aluEval .sll v264 0x14 = v957 ∧
      aluEval .mul v722 v302 = v958 ∧
      aluEval .sub v937 v559 = v959 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n920, v920, d920, hv920, u920⟩ := s.aluG hc ev_at_c8c (off' := 0xC90) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv920
  obtain ⟨n921, d921, u921⟩ := u920.lwE hc ev_at_c90 (off' := 0xC92) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 100) (by decide)) (v := v682)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl64])
  obtain ⟨n922, v922, d922, hv922, u922⟩ := u921.aluG hc ev_at_c92 (off' := 0xC94) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv922
  obtain ⟨n923, d923, u923⟩ := u922.lwE hc ev_at_c94 (off' := 0xC96) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 116) (by decide)) (v := v667)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl74])
  obtain ⟨n924, v924, d924, hv924, u924⟩ := u923.aluG hc ev_at_c96 (off' := 0xC98) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv924
  obtain ⟨n925, d925, u925⟩ := u924.lwE hc ev_at_c98 (off' := 0xC9A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 112) (by decide)) (v := v669)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl70])
  obtain ⟨n926, v926, d926, hv926, u926⟩ := u925.aluG hc ev_at_c9a (off' := 0xC9C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv926
  obtain ⟨n927, v927, d927, hv927, u927⟩ := u926.aluG hc ev_at_c9c (off' := 0xCA0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv927
  obtain ⟨n928, d928, u928⟩ := u927.lwE hc ev_at_ca0 (off' := 0xCA4) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 264) (by decide)) (v := v203)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl108])
  obtain ⟨n929, v929, d929, hv929, u929⟩ := u928.aluG hc ev_at_ca4 (off' := 0xCA6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv929
  obtain ⟨n930, d930, u930⟩ := u929.lwE hc ev_at_ca6 (off' := 0xCA8) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 104) (by decide)) (v := v689)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl68])
  obtain ⟨n931, v931, d931, hv931, u931⟩ := u930.aluG hc ev_at_ca8 (off' := 0xCAA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv931
  obtain ⟨n932, v932, d932, hv932, u932⟩ := u931.aluG hc ev_at_caa (off' := 0xCAC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv932
  obtain ⟨n933, d933, u933⟩ := u932.lwE hc ev_at_cac (off' := 0xCAE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 108) (by decide)) (v := v691)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl6C])
  obtain ⟨n934, v934, d934, hv934, u934⟩ := u933.aluG hc ev_at_cae (off' := 0xCB0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv934
  obtain ⟨n935, v935, d935, hv935, u935⟩ := u934.aluG hc ev_at_cb0 (off' := 0xCB4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv935
  obtain ⟨n936, d936, u936⟩ := u935.lwE hc ev_at_cb4 (off' := 0xCB6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 92) (by decide)) (v := v706)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl5C])
  obtain ⟨n937, v937, d937, hv937, u937⟩ := u936.aluG hc ev_at_cb6 (off' := 0xCB8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv937
  obtain ⟨n938, d938, u938⟩ := u937.lwE hc ev_at_cb8 (off' := 0xCBA) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 88) (by decide)) (v := v708)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl58])
  obtain ⟨n939, v939, d939, hv939, u939⟩ := u938.aluG hc ev_at_cba (off' := 0xCBC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv939
  obtain ⟨n940, v940, d940, hv940, u940⟩ := u939.aluG hc ev_at_cbc (off' := 0xCC0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv940
  obtain ⟨n941, v941, d941, hv941, u941⟩ := u940.aluG hc ev_at_cc0 (off' := 0xCC2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv941
  obtain ⟨n942, d942, u942⟩ := u941.lwE hc ev_at_cc2 (off' := 0xCC4) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 132) (by decide)) (v := v572)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl84])
  obtain ⟨n943, v943, d943, hv943, u943⟩ := u942.aluG hc ev_at_cc4 (off' := 0xCC8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv943
  obtain ⟨n944, v944, d944, hv944, u944⟩ := u943.aluG hc ev_at_cc8 (off' := 0xCCA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv944
  obtain ⟨n945, v945, d945, hv945, u945⟩ := u944.aluG hc ev_at_cca (off' := 0xCCE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv945
  obtain ⟨n946, v946, d946, hv946, u946⟩ := u945.aluG hc ev_at_cce (off' := 0xCD2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv946
  obtain ⟨n947, d947, u947⟩ := u946.lwE hc ev_at_cd2 (off' := 0xCD4) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 140) (by decide)) (v := v559)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl8C])
  obtain ⟨n948, v948, d948, hv948, u948⟩ := u947.aluG hc ev_at_cd4 (off' := 0xCD8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv948
  obtain ⟨n949, v949, d949, hv949, u949⟩ := u948.aluG hc ev_at_cd8 (off' := 0xCDC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv949
  obtain ⟨n950, v950, d950, hv950, u950⟩ := u949.aluG hc ev_at_cdc (off' := 0xCDE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv950
  obtain ⟨n951, d951, u951⟩ := u950.lwE hc ev_at_cde (off' := 0xCE0) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 168) (by decide)) (v := v279)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slA8])
  obtain ⟨n952, v952, d952, hv952, u952⟩ := u951.aluImmG hc ev_at_ce0 (off' := 0xCE2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv952
  obtain ⟨n953, v953, d953, hv953, u953⟩ := u952.aluG hc ev_at_ce2 (off' := 0xCE6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv953
  obtain ⟨n954, v954, d954, hv954, u954⟩ := u953.aluG hc ev_at_ce6 (off' := 0xCE8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv954
  obtain ⟨n955, v955, d955, hv955, u955⟩ := u954.aluG hc ev_at_ce8 (off' := 0xCEC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv955
  obtain ⟨n956, d956, u956⟩ := u955.lwE hc ev_at_cec (off' := 0xCEE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 204) (by decide)) (v := v264)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slCC])
  obtain ⟨n957, v957, d957, hv957, u957⟩ := u956.aluImmG hc ev_at_cee (off' := 0xCF0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv957
  obtain ⟨n958, v958, d958, hv958, u958⟩ := u957.aluG hc ev_at_cf0 (off' := 0xCF4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv958
  obtain ⟨n959, v959, d959, hv959, u959⟩ := u958.aluG hc ev_at_cf4 (off' := 0xCF8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv959
  have qo1 : reg n959 ra = v357 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n959 sp = F := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n959 (3 : Fin 32) = G3 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n959 (4 : Fin 32) = G4 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n959 (5 : Fin 32) = v831 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n959 (6 : Fin 32) = v239 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n959 (7 : Fin 32) = v949 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n959 (8 : Fin 32) = v935 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n959 (9 : Fin 32) = v959 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n959 a0 = v916 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n959 a1 = v954 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n959 a2 = v953 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n959 a3 = v955 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n959 a4 = v957 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n959 a5 = v958 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n959 a6 = v945 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n959 a7 = v485 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n959 (18 : Fin 32) = v7 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n959 (19 : Fin 32) = v572 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n959 (20 : Fin 32) = v722 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n959 (21 : Fin 32) = v485 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n959 (22 : Fin 32) = v557 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n959 (23 : Fin 32) = v302 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n959 (24 : Fin 32) = v150 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n959 (25 : Fin 32) = v559 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n959 (26 : Fin 32) = v545 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n959 (27 : Fin 32) = v882 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n959 (28 : Fin 32) = v823 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n959 (29 : Fin 32) = v819 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n959 (30 : Fin 32) = v897 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n959 (31 : Fin 32) = v481 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mi (F + 0xC) = G21 := by
    rw [slC]
  have so10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [sl10]
  have so7C : memLoad32 Mi (F + 0x7C) = v717 := by
    rw [sl7C]
  have so80 : memLoad32 Mi (F + 0x80) = v715 := by
    rw [sl80]
  have so88 : memLoad32 Mi (F + 0x88) = v695 := by
    rw [sl88]
  have so98 : memLoad32 Mi (F + 0x98) = v352 := by
    rw [sl98]
  have so9C : memLoad32 Mi (F + 0x9C) = v713 := by
    rw [sl9C]
  have soB0 : memLoad32 Mi (F + 0xB0) = v693 := by
    rw [slB0]
  have soB4 : memLoad32 Mi (F + 0xB4) = v582 := by
    rw [slB4]
  have soBC : memLoad32 Mi (F + 0xBC) = v467 := by
    rw [slBC]
  have soC0 : memLoad32 Mi (F + 0xC0) = v405 := by
    rw [slC0]
  have soC8 : memLoad32 Mi (F + 0xC8) = v335 := by
    rw [slC8]
  have soD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [slD0]
  have soE8 : memLoad32 Mi (F + 0xE8) = v419 := by
    rw [slE8]
  have soEC : memLoad32 Mi (F + 0xEC) = v341 := by
    rw [slEC]
  have soFC : memLoad32 Mi (F + 0xFC) = v579 := by
    rw [slFC]
  have so100 : memLoad32 Mi (F + 0x100) = v540 := by
    rw [sl100]
  have so104 : memLoad32 Mi (F + 0x104) = v710 := by
    rw [sl104]
  have so10C : memLoad32 Mi (F + 0x10C) = v274 := by
    rw [sl10C]
  have so110 : memLoad32 Mi (F + 0x110) = v702 := by
    rw [sl110]
  have so118 : memLoad32 Mi (F + 0x118) = v803 := by
    rw [sl118]
  have so11C : memLoad32 Mi (F + 0x11C) = v231 := by
    rw [sl11C]
  exact ⟨n959, Mi, v920, v922, v924, v926, v927, v929, v931, v932, v934, v935, v937, v939, v940, v941, v943, v944, v945, v946, v948, v949, v950, v952, v953, v954, v955, v957, v958, v959, (.cons d920 (.cons d921 (.cons d922 (.cons d923 (.cons d924 (.cons d925 (.cons d926 (.cons d927 (.cons d928 (.cons d929 (.cons d930 (.cons d931 (.cons d932 (.cons d933 (.cons d934 (.cons d935 (.cons d936 (.cons d937 (.cons d938 (.cons d939 (.cons d940 (.cons d941 (.cons d942 (.cons d943 (.cons d944 (.cons d945 (.cons d946 (.cons d947 (.cons d948 (.cons d949 (.cons d950 (.cons d951 (.cons d952 (.cons d953 (.cons d954 (.cons d955 (.cons d956 (.cons d957 (.cons d958 (.single d959)))))))))))))))))))))))))))))))))))))))), u959.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so7C, so80, so88, so98, so9C, soB0, soB4, soBC, soC0, soC8, soD0, soE8, soEC, soFC, so100, so104, so10C, so110, so118, so11C, hv920, hv922, hv924, hv926, hv927, hv929, hv931, hv932, hv934, hv935, hv937, hv939, hv940, hv941, hv943, hv944, hv945, hv946, hv948, hv949, hv950, hv952, hv953, hv954, hv955, hv957, hv958, hv959⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g30 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v150 v231 v239 v274 v302 v335 v341 v352 v357 v405 v419 v467 v481 v485 v540 v545 v557 v559 v572 v579 v582 v693 v695 v702 v710 v713 v715 v717 v722 v803 v819 v823 v831 v882 v897 v916 v935 v945 v949 v953 v954 v955 v957 v958 v959 : Word}
    (s : St Mi B n 0xCF8 (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v357)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v831)
    (q6 : reg n (6 : Fin 32) = v239)
    (q7 : reg n (7 : Fin 32) = v949)
    (q8 : reg n (8 : Fin 32) = v935)
    (q9 : reg n (9 : Fin 32) = v959)
    (q10 : reg n a0 = v916)
    (q11 : reg n a1 = v954)
    (q12 : reg n a2 = v953)
    (q13 : reg n a3 = v955)
    (q14 : reg n a4 = v957)
    (q15 : reg n a5 = v958)
    (q16 : reg n a6 = v945)
    (q17 : reg n a7 = v485)
    (q18 : reg n (18 : Fin 32) = v7)
    (q19 : reg n (19 : Fin 32) = v572)
    (q20 : reg n (20 : Fin 32) = v722)
    (q21 : reg n (21 : Fin 32) = v485)
    (q22 : reg n (22 : Fin 32) = v557)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v150)
    (q25 : reg n (25 : Fin 32) = v559)
    (q26 : reg n (26 : Fin 32) = v545)
    (q27 : reg n (27 : Fin 32) = v882)
    (q28 : reg n (28 : Fin 32) = v823)
    (q29 : reg n (29 : Fin 32) = v819)
    (q30 : reg n (30 : Fin 32) = v897)
    (q31 : reg n (31 : Fin 32) = v481)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (sl7C : memLoad32 Mi (F + 0x7C) = v717)
    (sl80 : memLoad32 Mi (F + 0x80) = v715)
    (sl88 : memLoad32 Mi (F + 0x88) = v695)
    (sl98 : memLoad32 Mi (F + 0x98) = v352)
    (sl9C : memLoad32 Mi (F + 0x9C) = v713)
    (slB0 : memLoad32 Mi (F + 0xB0) = v693)
    (slB4 : memLoad32 Mi (F + 0xB4) = v582)
    (slBC : memLoad32 Mi (F + 0xBC) = v467)
    (slC0 : memLoad32 Mi (F + 0xC0) = v405)
    (slC8 : memLoad32 Mi (F + 0xC8) = v335)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slE8 : memLoad32 Mi (F + 0xE8) = v419)
    (slEC : memLoad32 Mi (F + 0xEC) = v341)
    (slFC : memLoad32 Mi (F + 0xFC) = v579)
    (sl100 : memLoad32 Mi (F + 0x100) = v540)
    (sl104 : memLoad32 Mi (F + 0x104) = v710)
    (sl10C : memLoad32 Mi (F + 0x10C) = v274)
    (sl110 : memLoad32 Mi (F + 0x110) = v702)
    (sl118 : memLoad32 Mi (F + 0x118) = v803)
    (sl11C : memLoad32 Mi (F + 0x11C) = v231)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v960 v961 v962 v963 v964 v965 v966 v967 v968 v969 v970 v971 v972 v973 v974 v975 v976 v977 v978 v979 v980 v983 v986 v987 v988 v989 v990 v991 v994 v995 v996 v997 v998 v999 : Word),
      Steps n n' ∧
      St M' B n' 0xD6C (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v357 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v831 ∧
      reg n' (6 : Fin 32) = v239 ∧
      reg n' (7 : Fin 32) = v991 ∧
      reg n' (8 : Fin 32) = v986 ∧
      reg n' (9 : Fin 32) = v996 ∧
      reg n' a0 = v995 ∧
      reg n' a1 = v999 ∧
      reg n' a2 = v998 ∧
      reg n' a3 = v274 ∧
      reg n' a4 = v695 ∧
      reg n' a5 = v994 ∧
      reg n' a6 = v945 ∧
      reg n' a7 = v485 ∧
      reg n' (18 : Fin 32) = v7 ∧
      reg n' (19 : Fin 32) = v572 ∧
      reg n' (20 : Fin 32) = v722 ∧
      reg n' (21 : Fin 32) = v485 ∧
      reg n' (22 : Fin 32) = v557 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v582 ∧
      reg n' (25 : Fin 32) = v559 ∧
      reg n' (26 : Fin 32) = v545 ∧
      reg n' (27 : Fin 32) = v882 ∧
      reg n' (28 : Fin 32) = v823 ∧
      reg n' (29 : Fin 32) = v819 ∧
      reg n' (30 : Fin 32) = v997 ∧
      reg n' (31 : Fin 32) = v481 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0x98) = v352 ∧
      memLoad32 M' (F + 0x9C) = v713 ∧
      memLoad32 M' (F + 0xBC) = v467 ∧
      memLoad32 M' (F + 0xC0) = v405 ∧
      memLoad32 M' (F + 0xC8) = v335 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xE8) = v419 ∧
      memLoad32 M' (F + 0xEC) = v341 ∧
      memLoad32 M' (F + 0xFC) = v579 ∧
      memLoad32 M' (F + 0x100) = v540 ∧
      memLoad32 M' (F + 0x104) = v710 ∧
      memLoad32 M' (F + 0x110) = v702 ∧
      memLoad32 M' (F + 0x118) = v803 ∧
      memLoad32 M' (F + 0x11C) = v231 ∧
      aluEval .mulhu v722 v302 = v960 ∧
      aluEval .add v957 v959 = v961 ∧
      aluEval .mul v819 v239 = v962 ∧
      aluEval .mulhu v819 v239 = v963 ∧
      aluEval .sltu v961 v959 = v964 ∧
      aluEval .add v954 v964 = v965 ∧
      aluEval .add v953 v961 = v966 ∧
      aluEval .add v965 v955 = v967 ∧
      aluEval .sltu v966 v961 = v968 ∧
      aluEval .add v967 v968 = v969 ∧
      aluEval .add v958 v966 = v970 ∧
      aluEval .add v969 v960 = v971 ∧
      aluEval .sltu v970 v966 = v972 ∧
      aluEval .add v971 v972 = v973 ∧
      aluEval .add v962 v970 = v974 ∧
      aluEval .add v973 v963 = v975 ∧
      aluEval .sltu v974 v970 = v976 ∧
      aluEval .sll v949 0x3 = v977 ∧
      aluEval .srl v945 0x1D = v978 ∧
      aluEval .or v977 v978 = v979 ∧
      aluEval .add v975 v976 = v980 ∧
      aluEval .add v693 v715 = v983 ∧
      aluEval .add v717 v695 = v986 ∧
      aluEval .srl v949 0x1D = v987 ∧
      aluEval .sltu v986 v695 = v988 ∧
      aluEval .add v980 v987 = v989 ∧
      aluEval .add v983 v988 = v990 ∧
      aluEval .add v974 v979 = v991 ∧
      aluEval .add v274 v582 = v994 ∧
      aluEval .sltu v991 v974 = v995 ∧
      aluEval .sltu v986 v994 = v996 ∧
      aluEval .add v989 v995 = v997 ∧
      aluEval .sub v990 v996 = v998 ∧
      aluEval .sltu v994 v274 = v999 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n960, v960, d960, hv960, u960⟩ := s.aluG hc ev_at_cf8 (off' := 0xCFC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv960
  obtain ⟨n961, v961, d961, hv961, u961⟩ := u960.aluG hc ev_at_cfc (off' := 0xCFE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv961
  obtain ⟨n962, v962, d962, hv962, u962⟩ := u961.aluG hc ev_at_cfe (off' := 0xD02) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv962
  obtain ⟨n963, v963, d963, hv963, u963⟩ := u962.aluG hc ev_at_d02 (off' := 0xD06) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv963
  obtain ⟨n964, v964, d964, hv964, u964⟩ := u963.aluG hc ev_at_d06 (off' := 0xD0A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv964
  obtain ⟨n965, v965, d965, hv965, u965⟩ := u964.aluG hc ev_at_d0a (off' := 0xD0C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv965
  obtain ⟨n966, v966, d966, hv966, u966⟩ := u965.aluG hc ev_at_d0c (off' := 0xD0E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv966
  obtain ⟨n967, v967, d967, hv967, u967⟩ := u966.aluG hc ev_at_d0e (off' := 0xD10) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv967
  obtain ⟨n968, v968, d968, hv968, u968⟩ := u967.aluG hc ev_at_d10 (off' := 0xD14) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv968
  obtain ⟨n969, v969, d969, hv969, u969⟩ := u968.aluG hc ev_at_d14 (off' := 0xD16) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv969
  obtain ⟨n970, v970, d970, hv970, u970⟩ := u969.aluG hc ev_at_d16 (off' := 0xD18) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv970
  obtain ⟨n971, v971, d971, hv971, u971⟩ := u970.aluG hc ev_at_d18 (off' := 0xD1A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv971
  obtain ⟨n972, v972, d972, hv972, u972⟩ := u971.aluG hc ev_at_d1a (off' := 0xD1E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv972
  obtain ⟨n973, v973, d973, hv973, u973⟩ := u972.aluG hc ev_at_d1e (off' := 0xD20) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv973
  obtain ⟨n974, v974, d974, hv974, u974⟩ := u973.aluG hc ev_at_d20 (off' := 0xD22) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv974
  obtain ⟨n975, v975, d975, hv975, u975⟩ := u974.aluG hc ev_at_d22 (off' := 0xD24) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv975
  obtain ⟨n976, v976, d976, hv976, u976⟩ := u975.aluG hc ev_at_d24 (off' := 0xD28) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv976
  obtain ⟨n977, v977, d977, hv977, u977⟩ := u976.aluImmG hc ev_at_d28 (off' := 0xD2C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv977
  obtain ⟨n978, v978, d978, hv978, u978⟩ := u977.aluImmG hc ev_at_d2c (off' := 0xD30) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv978
  obtain ⟨n979, v979, d979, hv979, u979⟩ := u978.aluG hc ev_at_d30 (off' := 0xD32) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv979
  obtain ⟨n980, v980, d980, hv980, u980⟩ := u979.aluG hc ev_at_d32 (off' := 0xD34) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv980
  obtain ⟨n981, d981, u981⟩ := u980.lwE hc ev_at_d34 (off' := 0xD36) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 176) (by decide)) (v := v693)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slB0])
  obtain ⟨n982, d982, u982⟩ := u981.lwE hc ev_at_d36 (off' := 0xD38) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 128) (by decide)) (v := v715)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl80])
  obtain ⟨n983, v983, d983, hv983, u983⟩ := u982.aluG hc ev_at_d38 (off' := 0xD3A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv983
  obtain ⟨n984, d984, u984⟩ := u983.lwE hc ev_at_d3a (off' := 0xD3C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 136) (by decide)) (v := v695)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl88])
  obtain ⟨n985, d985, u985⟩ := u984.lwE hc ev_at_d3c (off' := 0xD3E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 124) (by decide)) (v := v717)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl7C])
  obtain ⟨n986, v986, d986, hv986, u986⟩ := u985.aluG hc ev_at_d3e (off' := 0xD40) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv986
  obtain ⟨n987, v987, d987, hv987, u987⟩ := u986.aluImmG hc ev_at_d40 (off' := 0xD44) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv987
  obtain ⟨n988, v988, d988, hv988, u988⟩ := u987.aluG hc ev_at_d44 (off' := 0xD48) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv988
  obtain ⟨n989, v989, d989, hv989, u989⟩ := u988.aluG hc ev_at_d48 (off' := 0xD4A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv989
  obtain ⟨n990, v990, d990, hv990, u990⟩ := u989.aluG hc ev_at_d4a (off' := 0xD4C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv990
  obtain ⟨n991, v991, d991, hv991, u991⟩ := u990.aluG hc ev_at_d4c (off' := 0xD50) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv991
  obtain ⟨n992, d992, u992⟩ := u991.lwE hc ev_at_d50 (off' := 0xD54) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 268) (by decide)) (v := v274)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl10C])
  obtain ⟨n993, d993, u993⟩ := u992.lwE hc ev_at_d54 (off' := 0xD56) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 180) (by decide)) (v := v582)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slB4])
  obtain ⟨n994, v994, d994, hv994, u994⟩ := u993.aluG hc ev_at_d56 (off' := 0xD5A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv994
  obtain ⟨n995, v995, d995, hv995, u995⟩ := u994.aluG hc ev_at_d5a (off' := 0xD5E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv995
  obtain ⟨n996, v996, d996, hv996, u996⟩ := u995.aluG hc ev_at_d5e (off' := 0xD62) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv996
  obtain ⟨n997, v997, d997, hv997, u997⟩ := u996.aluG hc ev_at_d62 (off' := 0xD66) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv997
  obtain ⟨n998, v998, d998, hv998, u998⟩ := u997.aluG hc ev_at_d66 (off' := 0xD68) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv998
  obtain ⟨n999, v999, d999, hv999, u999⟩ := u998.aluG hc ev_at_d68 (off' := 0xD6C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv999
  have qo1 : reg n999 ra = v357 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n999 sp = F := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n999 (3 : Fin 32) = G3 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n999 (4 : Fin 32) = G4 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n999 (5 : Fin 32) = v831 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n999 (6 : Fin 32) = v239 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n999 (7 : Fin 32) = v991 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n999 (8 : Fin 32) = v986 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n999 (9 : Fin 32) = v996 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n999 a0 = v995 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n999 a1 = v999 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n999 a2 = v998 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n999 a3 = v274 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n999 a4 = v695 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n999 a5 = v994 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n999 a6 = v945 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n999 a7 = v485 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n999 (18 : Fin 32) = v7 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n999 (19 : Fin 32) = v572 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n999 (20 : Fin 32) = v722 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n999 (21 : Fin 32) = v485 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n999 (22 : Fin 32) = v557 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n999 (23 : Fin 32) = v302 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n999 (24 : Fin 32) = v582 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n999 (25 : Fin 32) = v559 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n999 (26 : Fin 32) = v545 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n999 (27 : Fin 32) = v882 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n999 (28 : Fin 32) = v823 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n999 (29 : Fin 32) = v819 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n999 (30 : Fin 32) = v997 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n999 (31 : Fin 32) = v481 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mi (F + 0xC) = G21 := by
    rw [slC]
  have so10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [sl10]
  have so98 : memLoad32 Mi (F + 0x98) = v352 := by
    rw [sl98]
  have so9C : memLoad32 Mi (F + 0x9C) = v713 := by
    rw [sl9C]
  have soBC : memLoad32 Mi (F + 0xBC) = v467 := by
    rw [slBC]
  have soC0 : memLoad32 Mi (F + 0xC0) = v405 := by
    rw [slC0]
  have soC8 : memLoad32 Mi (F + 0xC8) = v335 := by
    rw [slC8]
  have soD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [slD0]
  have soE8 : memLoad32 Mi (F + 0xE8) = v419 := by
    rw [slE8]
  have soEC : memLoad32 Mi (F + 0xEC) = v341 := by
    rw [slEC]
  have soFC : memLoad32 Mi (F + 0xFC) = v579 := by
    rw [slFC]
  have so100 : memLoad32 Mi (F + 0x100) = v540 := by
    rw [sl100]
  have so104 : memLoad32 Mi (F + 0x104) = v710 := by
    rw [sl104]
  have so110 : memLoad32 Mi (F + 0x110) = v702 := by
    rw [sl110]
  have so118 : memLoad32 Mi (F + 0x118) = v803 := by
    rw [sl118]
  have so11C : memLoad32 Mi (F + 0x11C) = v231 := by
    rw [sl11C]
  exact ⟨n999, Mi, v960, v961, v962, v963, v964, v965, v966, v967, v968, v969, v970, v971, v972, v973, v974, v975, v976, v977, v978, v979, v980, v983, v986, v987, v988, v989, v990, v991, v994, v995, v996, v997, v998, v999, (.cons d960 (.cons d961 (.cons d962 (.cons d963 (.cons d964 (.cons d965 (.cons d966 (.cons d967 (.cons d968 (.cons d969 (.cons d970 (.cons d971 (.cons d972 (.cons d973 (.cons d974 (.cons d975 (.cons d976 (.cons d977 (.cons d978 (.cons d979 (.cons d980 (.cons d981 (.cons d982 (.cons d983 (.cons d984 (.cons d985 (.cons d986 (.cons d987 (.cons d988 (.cons d989 (.cons d990 (.cons d991 (.cons d992 (.cons d993 (.cons d994 (.cons d995 (.cons d996 (.cons d997 (.cons d998 (.single d999)))))))))))))))))))))))))))))))))))))))), u999.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so98, so9C, soBC, soC0, soC8, soD0, soE8, soEC, soFC, so100, so104, so110, so118, so11C, hv960, hv961, hv962, hv963, hv964, hv965, hv966, hv967, hv968, hv969, hv970, hv971, hv972, hv973, hv974, hv975, hv976, hv977, hv978, hv979, hv980, hv983, hv986, hv987, hv988, hv989, hv990, hv991, hv994, hv995, hv996, hv997, hv998, hv999⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g31 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v231 v239 v274 v302 v335 v341 v352 v357 v405 v419 v467 v481 v485 v540 v545 v557 v559 v572 v579 v582 v695 v702 v710 v713 v722 v803 v819 v823 v831 v882 v945 v986 v991 v994 v995 v996 v997 v998 v999 : Word}
    (s : St Mi B n 0xD6C (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v357)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v831)
    (q6 : reg n (6 : Fin 32) = v239)
    (q7 : reg n (7 : Fin 32) = v991)
    (q8 : reg n (8 : Fin 32) = v986)
    (q9 : reg n (9 : Fin 32) = v996)
    (q10 : reg n a0 = v995)
    (q11 : reg n a1 = v999)
    (q12 : reg n a2 = v998)
    (q13 : reg n a3 = v274)
    (q14 : reg n a4 = v695)
    (q15 : reg n a5 = v994)
    (q16 : reg n a6 = v945)
    (q17 : reg n a7 = v485)
    (q18 : reg n (18 : Fin 32) = v7)
    (q19 : reg n (19 : Fin 32) = v572)
    (q20 : reg n (20 : Fin 32) = v722)
    (q21 : reg n (21 : Fin 32) = v485)
    (q22 : reg n (22 : Fin 32) = v557)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v582)
    (q25 : reg n (25 : Fin 32) = v559)
    (q26 : reg n (26 : Fin 32) = v545)
    (q27 : reg n (27 : Fin 32) = v882)
    (q28 : reg n (28 : Fin 32) = v823)
    (q29 : reg n (29 : Fin 32) = v819)
    (q30 : reg n (30 : Fin 32) = v997)
    (q31 : reg n (31 : Fin 32) = v481)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (sl98 : memLoad32 Mi (F + 0x98) = v352)
    (sl9C : memLoad32 Mi (F + 0x9C) = v713)
    (slBC : memLoad32 Mi (F + 0xBC) = v467)
    (slC0 : memLoad32 Mi (F + 0xC0) = v405)
    (slC8 : memLoad32 Mi (F + 0xC8) = v335)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slE8 : memLoad32 Mi (F + 0xE8) = v419)
    (slEC : memLoad32 Mi (F + 0xEC) = v341)
    (slFC : memLoad32 Mi (F + 0xFC) = v579)
    (sl100 : memLoad32 Mi (F + 0x100) = v540)
    (sl104 : memLoad32 Mi (F + 0x104) = v710)
    (sl110 : memLoad32 Mi (F + 0x110) = v702)
    (sl118 : memLoad32 Mi (F + 0x118) = v803)
    (sl11C : memLoad32 Mi (F + 0x11C) = v231)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v1002 v1003 v1005 v1006 v1007 v1009 v1010 v1011 v1012 v1013 v1014 v1015 v1016 v1018 v1019 v1021 v1022 v1023 v1024 v1025 v1026 v1027 v1028 v1029 v1030 v1031 v1032 v1033 v1034 v1035 v1036 v1037 v1038 v1039 : Word),
      Steps n n' ∧
      St M' B n' 0xDE0 (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v357 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v831 ∧
      reg n' (6 : Fin 32) = v1038 ∧
      reg n' (7 : Fin 32) = v991 ∧
      reg n' (8 : Fin 32) = v1022 ∧
      reg n' (9 : Fin 32) = v1013 ∧
      reg n' a0 = v1036 ∧
      reg n' a1 = v1037 ∧
      reg n' a2 = v1039 ∧
      reg n' a3 = v1034 ∧
      reg n' a4 = v1030 ∧
      reg n' a5 = v1026 ∧
      reg n' a6 = v945 ∧
      reg n' a7 = v485 ∧
      reg n' (18 : Fin 32) = v7 ∧
      reg n' (19 : Fin 32) = v572 ∧
      reg n' (20 : Fin 32) = v722 ∧
      reg n' (21 : Fin 32) = v579 ∧
      reg n' (22 : Fin 32) = v557 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v582 ∧
      reg n' (25 : Fin 32) = v559 ∧
      reg n' (26 : Fin 32) = v545 ∧
      reg n' (27 : Fin 32) = v1014 ∧
      reg n' (28 : Fin 32) = v823 ∧
      reg n' (29 : Fin 32) = v819 ∧
      reg n' (30 : Fin 32) = v997 ∧
      reg n' (31 : Fin 32) = v481 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0xBC) = v467 ∧
      memLoad32 M' (F + 0xC0) = v405 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xE8) = v419 ∧
      memLoad32 M' (F + 0xEC) = v341 ∧
      memLoad32 M' (F + 0x100) = v540 ∧
      memLoad32 M' (F + 0x110) = v702 ∧
      memLoad32 M' (F + 0x118) = v803 ∧
      aluEval .add v231 v579 = v1002 ∧
      aluEval .add v999 v1002 = v1003 ∧
      aluEval .add v998 v713 = v1005 ∧
      aluEval .sub v986 v994 = v1006 ∧
      aluEval .sub v1005 v1003 = v1007 ∧
      aluEval .add v710 v1006 = v1009 ∧
      aluEval .add 0 0x14D = v1010 ∧
      aluEval .mul v722 v1010 = v1011 ∧
      aluEval .sltu v1009 v1006 = v1012 ∧
      aluEval .mulhu v722 v1010 = v1013 ∧
      aluEval .add 0 0x14D = v1014 ∧
      aluEval .add v1007 v1012 = v1015 ∧
      aluEval .mul v819 v302 = v1016 ∧
      aluEval .sll v335 0x14 = v1018 ∧
      aluEval .mulhu v819 v302 = v1019 ∧
      aluEval .srl v352 0xC = v1021 ∧
      aluEval .add v1018 v1009 = v1022 ∧
      aluEval .add v1021 v1015 = v1023 ∧
      aluEval .sltu v1022 v1009 = v1024 ∧
      aluEval .add v1023 v1024 = v1025 ∧
      aluEval .add v1011 v1022 = v1026 ∧
      aluEval .add v1025 v1013 = v1027 ∧
      aluEval .sltu v1026 v1022 = v1028 ∧
      aluEval .add v1027 v1028 = v1029 ∧
      aluEval .add v1016 v1026 = v1030 ∧
      aluEval .add v1029 v1019 = v1031 ∧
      aluEval .sltu v1030 v1026 = v1032 ∧
      aluEval .sll v997 0x3 = v1033 ∧
      aluEval .srl v991 0x1D = v1034 ∧
      aluEval .or v1033 v1034 = v1035 ∧
      aluEval .add v1031 v1032 = v1036 ∧
      aluEval .srl v997 0x1D = v1037 ∧
      aluEval .add v1030 v1035 = v1038 ∧
      aluEval .mul v819 v1014 = v1039 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n1000, d1000, u1000⟩ := s.lwE hc ev_at_d6c (off' := 0xD70) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 284) (by decide)) (v := v231)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl11C])
  obtain ⟨n1001, d1001, u1001⟩ := u1000.lwE hc ev_at_d70 (off' := 0xD72) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 252) (by decide)) (v := v579)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slFC])
  obtain ⟨n1002, v1002, d1002, hv1002, u1002⟩ := u1001.aluG hc ev_at_d72 (off' := 0xD74) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1002
  obtain ⟨n1003, v1003, d1003, hv1003, u1003⟩ := u1002.aluG hc ev_at_d74 (off' := 0xD76) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1003
  obtain ⟨n1004, d1004, u1004⟩ := u1003.lwE hc ev_at_d76 (off' := 0xD78) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 156) (by decide)) (v := v713)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl9C])
  obtain ⟨n1005, v1005, d1005, hv1005, u1005⟩ := u1004.aluG hc ev_at_d78 (off' := 0xD7A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1005
  obtain ⟨n1006, v1006, d1006, hv1006, u1006⟩ := u1005.aluG hc ev_at_d7a (off' := 0xD7E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1006
  obtain ⟨n1007, v1007, d1007, hv1007, u1007⟩ := u1006.aluG hc ev_at_d7e (off' := 0xD80) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1007
  obtain ⟨n1008, d1008, u1008⟩ := u1007.lwE hc ev_at_d80 (off' := 0xD84) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 260) (by decide)) (v := v710)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl104])
  obtain ⟨n1009, v1009, d1009, hv1009, u1009⟩ := u1008.aluG hc ev_at_d84 (off' := 0xD86) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1009
  obtain ⟨n1010, v1010, d1010, hv1010, u1010⟩ := u1009.aluImmG hc ev_at_d86 (off' := 0xD8A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1010
  obtain ⟨n1011, v1011, d1011, hv1011, u1011⟩ := u1010.aluG hc ev_at_d8a (off' := 0xD8E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1011
  obtain ⟨n1012, v1012, d1012, hv1012, u1012⟩ := u1011.aluG hc ev_at_d8e (off' := 0xD92) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1012
  obtain ⟨n1013, v1013, d1013, hv1013, u1013⟩ := u1012.aluG hc ev_at_d92 (off' := 0xD96) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1013
  obtain ⟨n1014, v1014, d1014, hv1014, u1014⟩ := u1013.aluImmG hc ev_at_d96 (off' := 0xD9A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1014
  obtain ⟨n1015, v1015, d1015, hv1015, u1015⟩ := u1014.aluG hc ev_at_d9a (off' := 0xD9C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1015
  obtain ⟨n1016, v1016, d1016, hv1016, u1016⟩ := u1015.aluG hc ev_at_d9c (off' := 0xDA0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1016
  obtain ⟨n1017, d1017, u1017⟩ := u1016.lwE hc ev_at_da0 (off' := 0xDA2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 200) (by decide)) (v := v335)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slC8])
  obtain ⟨n1018, v1018, d1018, hv1018, u1018⟩ := u1017.aluImmG hc ev_at_da2 (off' := 0xDA4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1018
  obtain ⟨n1019, v1019, d1019, hv1019, u1019⟩ := u1018.aluG hc ev_at_da4 (off' := 0xDA8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1019
  obtain ⟨n1020, d1020, u1020⟩ := u1019.lwE hc ev_at_da8 (off' := 0xDAA) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 152) (by decide)) (v := v352)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl98])
  obtain ⟨n1021, v1021, d1021, hv1021, u1021⟩ := u1020.aluImmG hc ev_at_daa (off' := 0xDAC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1021
  obtain ⟨n1022, v1022, d1022, hv1022, u1022⟩ := u1021.aluG hc ev_at_dac (off' := 0xDAE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1022
  obtain ⟨n1023, v1023, d1023, hv1023, u1023⟩ := u1022.aluG hc ev_at_dae (off' := 0xDB0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1023
  obtain ⟨n1024, v1024, d1024, hv1024, u1024⟩ := u1023.aluG hc ev_at_db0 (off' := 0xDB4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1024
  obtain ⟨n1025, v1025, d1025, hv1025, u1025⟩ := u1024.aluG hc ev_at_db4 (off' := 0xDB6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1025
  obtain ⟨n1026, v1026, d1026, hv1026, u1026⟩ := u1025.aluG hc ev_at_db6 (off' := 0xDB8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1026
  obtain ⟨n1027, v1027, d1027, hv1027, u1027⟩ := u1026.aluG hc ev_at_db8 (off' := 0xDBA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1027
  obtain ⟨n1028, v1028, d1028, hv1028, u1028⟩ := u1027.aluG hc ev_at_dba (off' := 0xDBE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1028
  obtain ⟨n1029, v1029, d1029, hv1029, u1029⟩ := u1028.aluG hc ev_at_dbe (off' := 0xDC0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1029
  obtain ⟨n1030, v1030, d1030, hv1030, u1030⟩ := u1029.aluG hc ev_at_dc0 (off' := 0xDC2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1030
  obtain ⟨n1031, v1031, d1031, hv1031, u1031⟩ := u1030.aluG hc ev_at_dc2 (off' := 0xDC4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1031
  obtain ⟨n1032, v1032, d1032, hv1032, u1032⟩ := u1031.aluG hc ev_at_dc4 (off' := 0xDC8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1032
  obtain ⟨n1033, v1033, d1033, hv1033, u1033⟩ := u1032.aluImmG hc ev_at_dc8 (off' := 0xDCC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1033
  obtain ⟨n1034, v1034, d1034, hv1034, u1034⟩ := u1033.aluImmG hc ev_at_dcc (off' := 0xDD0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1034
  obtain ⟨n1035, v1035, d1035, hv1035, u1035⟩ := u1034.aluG hc ev_at_dd0 (off' := 0xDD2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1035
  obtain ⟨n1036, v1036, d1036, hv1036, u1036⟩ := u1035.aluG hc ev_at_dd2 (off' := 0xDD4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1036
  obtain ⟨n1037, v1037, d1037, hv1037, u1037⟩ := u1036.aluImmG hc ev_at_dd4 (off' := 0xDD8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1037
  obtain ⟨n1038, v1038, d1038, hv1038, u1038⟩ := u1037.aluG hc ev_at_dd8 (off' := 0xDDC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1038
  obtain ⟨n1039, v1039, d1039, hv1039, u1039⟩ := u1038.aluG hc ev_at_ddc (off' := 0xDE0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1039
  have qo1 : reg n1039 ra = v357 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n1039 sp = F := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n1039 (3 : Fin 32) = G3 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n1039 (4 : Fin 32) = G4 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n1039 (5 : Fin 32) = v831 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n1039 (6 : Fin 32) = v1038 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n1039 (7 : Fin 32) = v991 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n1039 (8 : Fin 32) = v1022 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n1039 (9 : Fin 32) = v1013 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n1039 a0 = v1036 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n1039 a1 = v1037 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n1039 a2 = v1039 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n1039 a3 = v1034 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n1039 a4 = v1030 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n1039 a5 = v1026 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n1039 a6 = v945 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n1039 a7 = v485 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n1039 (18 : Fin 32) = v7 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n1039 (19 : Fin 32) = v572 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n1039 (20 : Fin 32) = v722 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n1039 (21 : Fin 32) = v579 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n1039 (22 : Fin 32) = v557 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n1039 (23 : Fin 32) = v302 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n1039 (24 : Fin 32) = v582 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n1039 (25 : Fin 32) = v559 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n1039 (26 : Fin 32) = v545 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n1039 (27 : Fin 32) = v1014 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n1039 (28 : Fin 32) = v823 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n1039 (29 : Fin 32) = v819 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n1039 (30 : Fin 32) = v997 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n1039 (31 : Fin 32) = v481 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mi (F + 0xC) = G21 := by
    rw [slC]
  have so10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [sl10]
  have soBC : memLoad32 Mi (F + 0xBC) = v467 := by
    rw [slBC]
  have soC0 : memLoad32 Mi (F + 0xC0) = v405 := by
    rw [slC0]
  have soD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [slD0]
  have soE8 : memLoad32 Mi (F + 0xE8) = v419 := by
    rw [slE8]
  have soEC : memLoad32 Mi (F + 0xEC) = v341 := by
    rw [slEC]
  have so100 : memLoad32 Mi (F + 0x100) = v540 := by
    rw [sl100]
  have so110 : memLoad32 Mi (F + 0x110) = v702 := by
    rw [sl110]
  have so118 : memLoad32 Mi (F + 0x118) = v803 := by
    rw [sl118]
  exact ⟨n1039, Mi, v1002, v1003, v1005, v1006, v1007, v1009, v1010, v1011, v1012, v1013, v1014, v1015, v1016, v1018, v1019, v1021, v1022, v1023, v1024, v1025, v1026, v1027, v1028, v1029, v1030, v1031, v1032, v1033, v1034, v1035, v1036, v1037, v1038, v1039, (.cons d1000 (.cons d1001 (.cons d1002 (.cons d1003 (.cons d1004 (.cons d1005 (.cons d1006 (.cons d1007 (.cons d1008 (.cons d1009 (.cons d1010 (.cons d1011 (.cons d1012 (.cons d1013 (.cons d1014 (.cons d1015 (.cons d1016 (.cons d1017 (.cons d1018 (.cons d1019 (.cons d1020 (.cons d1021 (.cons d1022 (.cons d1023 (.cons d1024 (.cons d1025 (.cons d1026 (.cons d1027 (.cons d1028 (.cons d1029 (.cons d1030 (.cons d1031 (.cons d1032 (.cons d1033 (.cons d1034 (.cons d1035 (.cons d1036 (.cons d1037 (.cons d1038 (.single d1039)))))))))))))))))))))))))))))))))))))))), u1039.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, soBC, soC0, soD0, soE8, soEC, so100, so110, so118, hv1002, hv1003, hv1005, hv1006, hv1007, hv1009, hv1010, hv1011, hv1012, hv1013, hv1014, hv1015, hv1016, hv1018, hv1019, hv1021, hv1022, hv1023, hv1024, hv1025, hv1026, hv1027, hv1028, hv1029, hv1030, hv1031, hv1032, hv1033, hv1034, hv1035, hv1036, hv1037, hv1038, hv1039⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g32 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v302 v341 v357 v405 v419 v467 v481 v485 v540 v545 v557 v559 v572 v579 v582 v702 v722 v803 v819 v823 v831 v945 v991 v997 v1013 v1014 v1022 v1026 v1030 v1034 v1036 v1037 v1038 v1039 : Word}
    (s : St Mi B n 0xDE0 (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v357)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v831)
    (q6 : reg n (6 : Fin 32) = v1038)
    (q7 : reg n (7 : Fin 32) = v991)
    (q8 : reg n (8 : Fin 32) = v1022)
    (q9 : reg n (9 : Fin 32) = v1013)
    (q10 : reg n a0 = v1036)
    (q11 : reg n a1 = v1037)
    (q12 : reg n a2 = v1039)
    (q13 : reg n a3 = v1034)
    (q14 : reg n a4 = v1030)
    (q15 : reg n a5 = v1026)
    (q16 : reg n a6 = v945)
    (q17 : reg n a7 = v485)
    (q18 : reg n (18 : Fin 32) = v7)
    (q19 : reg n (19 : Fin 32) = v572)
    (q20 : reg n (20 : Fin 32) = v722)
    (q21 : reg n (21 : Fin 32) = v579)
    (q22 : reg n (22 : Fin 32) = v557)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v582)
    (q25 : reg n (25 : Fin 32) = v559)
    (q26 : reg n (26 : Fin 32) = v545)
    (q27 : reg n (27 : Fin 32) = v1014)
    (q28 : reg n (28 : Fin 32) = v823)
    (q29 : reg n (29 : Fin 32) = v819)
    (q30 : reg n (30 : Fin 32) = v997)
    (q31 : reg n (31 : Fin 32) = v481)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (slBC : memLoad32 Mi (F + 0xBC) = v467)
    (slC0 : memLoad32 Mi (F + 0xC0) = v405)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slE8 : memLoad32 Mi (F + 0xE8) = v419)
    (slEC : memLoad32 Mi (F + 0xEC) = v341)
    (sl100 : memLoad32 Mi (F + 0x100) = v540)
    (sl110 : memLoad32 Mi (F + 0x110) = v702)
    (sl118 : memLoad32 Mi (F + 0x118) = v803)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v1040 v1041 v1042 v1043 v1045 v1047 v1048 v1049 v1050 v1051 v1052 v1053 v1054 v1055 v1056 v1057 v1058 v1059 v1060 v1061 v1062 v1063 v1064 v1065 v1067 v1069 v1070 v1071 v1072 v1073 v1074 v1075 v1076 v1077 v1078 v1079 : Word),
      Steps n n' ∧
      St M' B n' 0xE4E (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v357 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v1060 ∧
      reg n' (6 : Fin 32) = v1038 ∧
      reg n' (7 : Fin 32) = v991 ∧
      reg n' (8 : Fin 32) = v1022 ∧
      reg n' (9 : Fin 32) = v1072 ∧
      reg n' a0 = v1079 ∧
      reg n' a1 = v1077 ∧
      reg n' a2 = v1064 ∧
      reg n' a3 = v1074 ∧
      reg n' a4 = v1069 ∧
      reg n' a5 = v1026 ∧
      reg n' a6 = v945 ∧
      reg n' a7 = v485 ∧
      reg n' (18 : Fin 32) = v7 ∧
      reg n' (19 : Fin 32) = v572 ∧
      reg n' (20 : Fin 32) = v722 ∧
      reg n' (21 : Fin 32) = v579 ∧
      reg n' (22 : Fin 32) = v557 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v582 ∧
      reg n' (25 : Fin 32) = v559 ∧
      reg n' (26 : Fin 32) = v545 ∧
      reg n' (27 : Fin 32) = v1014 ∧
      reg n' (28 : Fin 32) = v1076 ∧
      reg n' (29 : Fin 32) = v819 ∧
      reg n' (30 : Fin 32) = v997 ∧
      reg n' (31 : Fin 32) = v481 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0x100) = v540 ∧
      memLoad32 M' (F + 0x110) = v702 ∧
      memLoad32 M' (F + 0x118) = v803 ∧
      aluEval .mulhu v819 v1014 = v1040 ∧
      aluEval .add v1036 v1037 = v1041 ∧
      aluEval .sltu v1038 v1030 = v1042 ∧
      aluEval .add v1041 v1042 = v1043 ∧
      aluEval .sll v405 0x14 = v1045 ∧
      aluEval .srl v419 0xC = v1047 ∧
      aluEval .add v1045 v831 = v1048 ∧
      aluEval .add v1047 v823 = v1049 ∧
      aluEval .sltu v1048 v831 = v1050 ∧
      aluEval .add v1049 v1050 = v1051 ∧
      aluEval .sll v1043 0x3 = v1052 ∧
      aluEval .add v1040 v1051 = v1053 ∧
      aluEval .add v1039 v1048 = v1054 ∧
      aluEval .srl v1038 0x1D = v1055 ∧
      aluEval .sltu v1054 v1048 = v1056 ∧
      aluEval .or v1055 v1052 = v1057 ∧
      aluEval .add v1056 v1053 = v1058 ∧
      aluEval .srl v1043 0x1D = v1059 ∧
      aluEval .add v1054 v1057 = v1060 ∧
      aluEval .add v1058 v1059 = v1061 ∧
      aluEval .sltu v1060 v1054 = v1062 ∧
      aluEval .add v1061 v1062 = v1063 ∧
      aluEval .sll v1063 0x3 = v1064 ∧
      aluEval .srl v485 0xC = v1065 ∧
      aluEval .sll v467 0x14 = v1067 ∧
      aluEval .add v341 v1067 = v1069 ∧
      aluEval .add v1065 v357 = v1070 ∧
      aluEval .srl v1060 0x1D = v1071 ∧
      aluEval .sltu v1069 v1067 = v1072 ∧
      aluEval .or v1071 v1064 = v1073 ∧
      aluEval .add v1070 v1072 = v1074 ∧
      aluEval .srl v1063 0x1D = v1075 ∧
      aluEval .add v1069 v1073 = v1076 ∧
      aluEval .add v1075 v1074 = v1077 ∧
      aluEval .sltu v1076 v1069 = v1078 ∧
      aluEval .add v1078 v1077 = v1079 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n1040, v1040, d1040, hv1040, u1040⟩ := s.aluG hc ev_at_de0 (off' := 0xDE4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1040
  obtain ⟨n1041, v1041, d1041, hv1041, u1041⟩ := u1040.aluG hc ev_at_de4 (off' := 0xDE6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1041
  obtain ⟨n1042, v1042, d1042, hv1042, u1042⟩ := u1041.aluG hc ev_at_de6 (off' := 0xDEA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1042
  obtain ⟨n1043, v1043, d1043, hv1043, u1043⟩ := u1042.aluG hc ev_at_dea (off' := 0xDEC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1043
  obtain ⟨n1044, d1044, u1044⟩ := u1043.lwE hc ev_at_dec (off' := 0xDEE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 192) (by decide)) (v := v405)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slC0])
  obtain ⟨n1045, v1045, d1045, hv1045, u1045⟩ := u1044.aluImmG hc ev_at_dee (off' := 0xDF0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1045
  obtain ⟨n1046, d1046, u1046⟩ := u1045.lwE hc ev_at_df0 (off' := 0xDF2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 232) (by decide)) (v := v419)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slE8])
  obtain ⟨n1047, v1047, d1047, hv1047, u1047⟩ := u1046.aluImmG hc ev_at_df2 (off' := 0xDF4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1047
  obtain ⟨n1048, v1048, d1048, hv1048, u1048⟩ := u1047.aluG hc ev_at_df4 (off' := 0xDF6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1048
  obtain ⟨n1049, v1049, d1049, hv1049, u1049⟩ := u1048.aluG hc ev_at_df6 (off' := 0xDF8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1049
  obtain ⟨n1050, v1050, d1050, hv1050, u1050⟩ := u1049.aluG hc ev_at_df8 (off' := 0xDFC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1050
  obtain ⟨n1051, v1051, d1051, hv1051, u1051⟩ := u1050.aluG hc ev_at_dfc (off' := 0xDFE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1051
  obtain ⟨n1052, v1052, d1052, hv1052, u1052⟩ := u1051.aluImmG hc ev_at_dfe (off' := 0xE02) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1052
  obtain ⟨n1053, v1053, d1053, hv1053, u1053⟩ := u1052.aluG hc ev_at_e02 (off' := 0xE04) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1053
  obtain ⟨n1054, v1054, d1054, hv1054, u1054⟩ := u1053.aluG hc ev_at_e04 (off' := 0xE06) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1054
  obtain ⟨n1055, v1055, d1055, hv1055, u1055⟩ := u1054.aluImmG hc ev_at_e06 (off' := 0xE0A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1055
  obtain ⟨n1056, v1056, d1056, hv1056, u1056⟩ := u1055.aluG hc ev_at_e0a (off' := 0xE0E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1056
  obtain ⟨n1057, v1057, d1057, hv1057, u1057⟩ := u1056.aluG hc ev_at_e0e (off' := 0xE10) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1057
  obtain ⟨n1058, v1058, d1058, hv1058, u1058⟩ := u1057.aluG hc ev_at_e10 (off' := 0xE12) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1058
  obtain ⟨n1059, v1059, d1059, hv1059, u1059⟩ := u1058.aluImmG hc ev_at_e12 (off' := 0xE16) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1059
  obtain ⟨n1060, v1060, d1060, hv1060, u1060⟩ := u1059.aluG hc ev_at_e16 (off' := 0xE1A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1060
  obtain ⟨n1061, v1061, d1061, hv1061, u1061⟩ := u1060.aluG hc ev_at_e1a (off' := 0xE1C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1061
  obtain ⟨n1062, v1062, d1062, hv1062, u1062⟩ := u1061.aluG hc ev_at_e1c (off' := 0xE20) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1062
  obtain ⟨n1063, v1063, d1063, hv1063, u1063⟩ := u1062.aluG hc ev_at_e20 (off' := 0xE22) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1063
  obtain ⟨n1064, v1064, d1064, hv1064, u1064⟩ := u1063.aluImmG hc ev_at_e22 (off' := 0xE26) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1064
  obtain ⟨n1065, v1065, d1065, hv1065, u1065⟩ := u1064.aluImmG hc ev_at_e26 (off' := 0xE2A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1065
  obtain ⟨n1066, d1066, u1066⟩ := u1065.lwE hc ev_at_e2a (off' := 0xE2C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 188) (by decide)) (v := v467)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slBC])
  obtain ⟨n1067, v1067, d1067, hv1067, u1067⟩ := u1066.aluImmG hc ev_at_e2c (off' := 0xE2E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1067
  obtain ⟨n1068, d1068, u1068⟩ := u1067.lwE hc ev_at_e2e (off' := 0xE30) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 236) (by decide)) (v := v341)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slEC])
  obtain ⟨n1069, v1069, d1069, hv1069, u1069⟩ := u1068.aluG hc ev_at_e30 (off' := 0xE32) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1069
  obtain ⟨n1070, v1070, d1070, hv1070, u1070⟩ := u1069.aluG hc ev_at_e32 (off' := 0xE34) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1070
  obtain ⟨n1071, v1071, d1071, hv1071, u1071⟩ := u1070.aluImmG hc ev_at_e34 (off' := 0xE38) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1071
  obtain ⟨n1072, v1072, d1072, hv1072, u1072⟩ := u1071.aluG hc ev_at_e38 (off' := 0xE3C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1072
  obtain ⟨n1073, v1073, d1073, hv1073, u1073⟩ := u1072.aluG hc ev_at_e3c (off' := 0xE3E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1073
  obtain ⟨n1074, v1074, d1074, hv1074, u1074⟩ := u1073.aluG hc ev_at_e3e (off' := 0xE40) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1074
  obtain ⟨n1075, v1075, d1075, hv1075, u1075⟩ := u1074.aluImmG hc ev_at_e40 (off' := 0xE42) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1075
  obtain ⟨n1076, v1076, d1076, hv1076, u1076⟩ := u1075.aluG hc ev_at_e42 (off' := 0xE46) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1076
  obtain ⟨n1077, v1077, d1077, hv1077, u1077⟩ := u1076.aluG hc ev_at_e46 (off' := 0xE48) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1077
  obtain ⟨n1078, v1078, d1078, hv1078, u1078⟩ := u1077.aluG hc ev_at_e48 (off' := 0xE4C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1078
  obtain ⟨n1079, v1079, d1079, hv1079, u1079⟩ := u1078.aluG hc ev_at_e4c (off' := 0xE4E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1079
  have qo1 : reg n1079 ra = v357 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n1079 sp = F := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n1079 (3 : Fin 32) = G3 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n1079 (4 : Fin 32) = G4 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n1079 (5 : Fin 32) = v1060 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n1079 (6 : Fin 32) = v1038 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n1079 (7 : Fin 32) = v991 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n1079 (8 : Fin 32) = v1022 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n1079 (9 : Fin 32) = v1072 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n1079 a0 = v1079 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n1079 a1 = v1077 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n1079 a2 = v1064 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n1079 a3 = v1074 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n1079 a4 = v1069 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n1079 a5 = v1026 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n1079 a6 = v945 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n1079 a7 = v485 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n1079 (18 : Fin 32) = v7 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n1079 (19 : Fin 32) = v572 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n1079 (20 : Fin 32) = v722 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n1079 (21 : Fin 32) = v579 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n1079 (22 : Fin 32) = v557 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n1079 (23 : Fin 32) = v302 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n1079 (24 : Fin 32) = v582 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n1079 (25 : Fin 32) = v559 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n1079 (26 : Fin 32) = v545 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n1079 (27 : Fin 32) = v1014 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n1079 (28 : Fin 32) = v1076 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n1079 (29 : Fin 32) = v819 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n1079 (30 : Fin 32) = v997 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n1079 (31 : Fin 32) = v481 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mi (F + 0xC) = G21 := by
    rw [slC]
  have so10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [sl10]
  have soD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [slD0]
  have so100 : memLoad32 Mi (F + 0x100) = v540 := by
    rw [sl100]
  have so110 : memLoad32 Mi (F + 0x110) = v702 := by
    rw [sl110]
  have so118 : memLoad32 Mi (F + 0x118) = v803 := by
    rw [sl118]
  exact ⟨n1079, Mi, v1040, v1041, v1042, v1043, v1045, v1047, v1048, v1049, v1050, v1051, v1052, v1053, v1054, v1055, v1056, v1057, v1058, v1059, v1060, v1061, v1062, v1063, v1064, v1065, v1067, v1069, v1070, v1071, v1072, v1073, v1074, v1075, v1076, v1077, v1078, v1079, (.cons d1040 (.cons d1041 (.cons d1042 (.cons d1043 (.cons d1044 (.cons d1045 (.cons d1046 (.cons d1047 (.cons d1048 (.cons d1049 (.cons d1050 (.cons d1051 (.cons d1052 (.cons d1053 (.cons d1054 (.cons d1055 (.cons d1056 (.cons d1057 (.cons d1058 (.cons d1059 (.cons d1060 (.cons d1061 (.cons d1062 (.cons d1063 (.cons d1064 (.cons d1065 (.cons d1066 (.cons d1067 (.cons d1068 (.cons d1069 (.cons d1070 (.cons d1071 (.cons d1072 (.cons d1073 (.cons d1074 (.cons d1075 (.cons d1076 (.cons d1077 (.cons d1078 (.single d1079)))))))))))))))))))))))))))))))))))))))), u1079.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, soD0, so100, so110, so118, hv1040, hv1041, hv1042, hv1043, hv1045, hv1047, hv1048, hv1049, hv1050, hv1051, hv1052, hv1053, hv1054, hv1055, hv1056, hv1057, hv1058, hv1059, hv1060, hv1061, hv1062, hv1063, hv1064, hv1065, hv1067, hv1069, hv1070, hv1071, hv1072, hv1073, hv1074, hv1075, hv1076, hv1077, hv1078, hv1079⟩

end C3.RV32
