import C3BootProofs.Proofs.P256ScalarDecode

/-! # P-256's `Scalar::mul`, segments 4 to 7

Each theorem steps 40 instructions. `scripts/gen-p256-scalar.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g4 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v3 v4 v7 v9 v10 v12 v17 v18 v19 v75 v95 v101 v114 v120 v123 v125 v129 v133 v134 v137 v143 v149 v152 v153 v154 v155 v157 v158 v159 : Word}
    (s : St Mi B n 0x236 (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q1 : reg n ra = v123)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v3)
    (q6 : reg n (6 : Fin 32) = v12)
    (q7 : reg n (7 : Fin 32) = v159)
    (q8 : reg n (8 : Fin 32) = v101)
    (q9 : reg n (9 : Fin 32) = v133)
    (q10 : reg n a0 = v153)
    (q11 : reg n a1 = v134)
    (q12 : reg n a2 = v152)
    (q13 : reg n a3 = v120)
    (q14 : reg n a4 = v155)
    (q15 : reg n a5 = v125)
    (q16 : reg n a6 = v18)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v75)
    (q19 : reg n (19 : Fin 32) = v10)
    (q20 : reg n (20 : Fin 32) = v154)
    (q21 : reg n (21 : Fin 32) = v95)
    (q22 : reg n (22 : Fin 32) = v149)
    (q23 : reg n (23 : Fin 32) = v143)
    (q24 : reg n (24 : Fin 32) = v129)
    (q25 : reg n (25 : Fin 32) = v137)
    (q26 : reg n (26 : Fin 32) = v9)
    (q27 : reg n (27 : Fin 32) = v157)
    (q28 : reg n (28 : Fin 32) = v158)
    (q29 : reg n (29 : Fin 32) = v4)
    (q30 : reg n (30 : Fin 32) = v19)
    (q31 : reg n (31 : Fin 32) = v114)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v160 v161 v162 v163 v164 v165 v166 v167 v168 v169 v170 v171 v172 v173 v174 v175 v176 v177 v178 v179 v180 v181 v182 v183 v184 v185 v186 v187 v188 v189 v190 v191 v192 v193 v194 v195 v196 v197 v198 v199 : Word),
      Steps n n' ∧
      St M' B n' 0x2B4 (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v192 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v3 ∧
      reg n' (6 : Fin 32) = v12 ∧
      reg n' (7 : Fin 32) = v161 ∧
      reg n' (8 : Fin 32) = v188 ∧
      reg n' (9 : Fin 32) = v186 ∧
      reg n' a0 = v197 ∧
      reg n' a1 = v199 ∧
      reg n' a2 = v168 ∧
      reg n' a3 = v181 ∧
      reg n' a4 = v195 ∧
      reg n' a5 = v196 ∧
      reg n' a6 = v18 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v170 ∧
      reg n' (19 : Fin 32) = v10 ∧
      reg n' (20 : Fin 32) = v154 ∧
      reg n' (21 : Fin 32) = v177 ∧
      reg n' (22 : Fin 32) = v149 ∧
      reg n' (23 : Fin 32) = v143 ∧
      reg n' (24 : Fin 32) = v129 ∧
      reg n' (25 : Fin 32) = v137 ∧
      reg n' (26 : Fin 32) = v9 ∧
      reg n' (27 : Fin 32) = v169 ∧
      reg n' (28 : Fin 32) = v158 ∧
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
      aluEval .sltu v158 v157 = v160 ∧
      aluEval .add v159 v160 = v161 ∧
      aluEval .mul v9 v4 = v162 ∧
      aluEval .and v114 0xFFFFFFFE = v163 ∧
      aluEval .mulhu v9 v3 = v164 ∧
      aluEval .add v155 v163 = v165 ∧
      aluEval .mulhu v9 v4 = v166 ∧
      aluEval .mul v9 v12 = v167 ∧
      memLoad32 M0 (F + 0x5C) = v168 ∧
      memLoad32 M0 (F + 0x60) = v169 ∧
      memLoad32 M0 (F + 0x64) = v170 ∧
      memLoad32 M0 (F + 0x68) = v171 ∧
      aluEval .sltu v165 v163 = v172 ∧
      aluEval .add v162 v123 = v173 ∧
      aluEval .mulhu v9 v12 = v174 ∧
      aluEval .add v172 v164 = v175 ∧
      aluEval .sltu v173 v123 = v176 ∧
      aluEval .add v173 v175 = v177 ∧
      aluEval .mul v9 v19 = v178 ∧
      aluEval .add v166 v176 = v179 ∧
      aluEval .sltu v177 v173 = v180 ∧
      aluEval .add v167 v129 = v181 ∧
      aluEval .mulhu v9 v19 = v182 ∧
      aluEval .add v179 v180 = v183 ∧
      aluEval .sltu v181 v129 = v184 ∧
      aluEval .add v184 v174 = v185 ∧
      aluEval .add v181 v183 = v186 ∧
      aluEval .sltu v186 v181 = v187 ∧
      aluEval .mulhu v9 v17 = v188 ∧
      aluEval .add v187 v185 = v189 ∧
      aluEval .add v178 v137 = v190 ∧
      aluEval .sltu v190 v137 = v191 ∧
      aluEval .add v190 v189 = v192 ∧
      aluEval .add v182 v191 = v193 ∧
      aluEval .sltu v192 v190 = v194 ∧
      aluEval .sub v143 v9 = v195 ∧
      aluEval .mulhu v9 v18 = v196 ∧
      aluEval .add v193 v194 = v197 ∧
      aluEval .sltu v195 v143 = v198 ∧
      aluEval .add v198 v188 = v199 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n160, v160, d160, hv160, u160⟩ := s.aluG hc psm_at_236 (off' := 0x23A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv160
  obtain ⟨n161, v161, d161, hv161, u161⟩ := u160.aluG hc psm_at_23a (off' := 0x23C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv161
  obtain ⟨n162, v162, d162, hv162, u162⟩ := u161.aluG hc psm_at_23c (off' := 0x240) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv162
  obtain ⟨n163, v163, d163, hv163, u163⟩ := u162.aluImmG hc psm_at_240 (off' := 0x244) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv163
  obtain ⟨n164, v164, d164, hv164, u164⟩ := u163.aluG hc psm_at_244 (off' := 0x248) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv164
  obtain ⟨n165, v165, d165, hv165, u165⟩ := u164.aluG hc psm_at_248 (off' := 0x24A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv165
  obtain ⟨n166, v166, d166, hv166, u166⟩ := u165.aluG hc psm_at_24a (off' := 0x24E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv166
  obtain ⟨n167, v167, d167, hv167, u167⟩ := u166.aluG hc psm_at_24e (off' := 0x252) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv167
  obtain ⟨n168, v168, d168, hv168, u168⟩ := u167.lwG hc psm_at_252 (off' := 0x254) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 92) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv168
  rw [sl5C] at hv168
  obtain ⟨n169, v169, d169, hv169, u169⟩ := u168.lwG hc psm_at_254 (off' := 0x256) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 96) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv169
  rw [sl60] at hv169
  obtain ⟨n170, v170, d170, hv170, u170⟩ := u169.lwG hc psm_at_256 (off' := 0x258) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 100) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv170
  rw [sl64] at hv170
  obtain ⟨n171, v171, d171, hv171, u171⟩ := u170.lwG hc psm_at_258 (off' := 0x25A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 104) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv171
  rw [sl68] at hv171
  obtain ⟨n172, v172, d172, hv172, u172⟩ := u171.aluG hc psm_at_25a (off' := 0x25E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv172
  obtain ⟨n173, v173, d173, hv173, u173⟩ := u172.aluG hc psm_at_25e (off' := 0x260) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv173
  obtain ⟨n174, v174, d174, hv174, u174⟩ := u173.aluG hc psm_at_260 (off' := 0x264) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv174
  obtain ⟨n175, v175, d175, hv175, u175⟩ := u174.aluG hc psm_at_264 (off' := 0x266) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv175
  obtain ⟨n176, v176, d176, hv176, u176⟩ := u175.aluG hc psm_at_266 (off' := 0x26A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv176
  obtain ⟨n177, v177, d177, hv177, u177⟩ := u176.aluG hc psm_at_26a (off' := 0x26E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv177
  obtain ⟨n178, v178, d178, hv178, u178⟩ := u177.aluG hc psm_at_26e (off' := 0x272) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv178
  obtain ⟨n179, v179, d179, hv179, u179⟩ := u178.aluG hc psm_at_272 (off' := 0x274) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv179
  obtain ⟨n180, v180, d180, hv180, u180⟩ := u179.aluG hc psm_at_274 (off' := 0x278) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv180
  obtain ⟨n181, v181, d181, hv181, u181⟩ := u180.aluG hc psm_at_278 (off' := 0x27A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv181
  obtain ⟨n182, v182, d182, hv182, u182⟩ := u181.aluG hc psm_at_27a (off' := 0x27E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv182
  obtain ⟨n183, v183, d183, hv183, u183⟩ := u182.aluG hc psm_at_27e (off' := 0x280) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv183
  obtain ⟨n184, v184, d184, hv184, u184⟩ := u183.aluG hc psm_at_280 (off' := 0x284) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv184
  obtain ⟨n185, v185, d185, hv185, u185⟩ := u184.aluG hc psm_at_284 (off' := 0x286) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv185
  obtain ⟨n186, v186, d186, hv186, u186⟩ := u185.aluG hc psm_at_286 (off' := 0x28A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv186
  obtain ⟨n187, v187, d187, hv187, u187⟩ := u186.aluG hc psm_at_28a (off' := 0x28E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv187
  obtain ⟨n188, v188, d188, hv188, u188⟩ := u187.aluG hc psm_at_28e (off' := 0x292) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv188
  obtain ⟨n189, v189, d189, hv189, u189⟩ := u188.aluG hc psm_at_292 (off' := 0x294) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv189
  obtain ⟨n190, v190, d190, hv190, u190⟩ := u189.aluG hc psm_at_294 (off' := 0x296) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv190
  obtain ⟨n191, v191, d191, hv191, u191⟩ := u190.aluG hc psm_at_296 (off' := 0x29A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv191
  obtain ⟨n192, v192, d192, hv192, u192⟩ := u191.aluG hc psm_at_29a (off' := 0x29E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv192
  obtain ⟨n193, v193, d193, hv193, u193⟩ := u192.aluG hc psm_at_29e (off' := 0x2A0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv193
  obtain ⟨n194, v194, d194, hv194, u194⟩ := u193.aluG hc psm_at_2a0 (off' := 0x2A4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv194
  obtain ⟨n195, v195, d195, hv195, u195⟩ := u194.aluG hc psm_at_2a4 (off' := 0x2A8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv195
  obtain ⟨n196, v196, d196, hv196, u196⟩ := u195.aluG hc psm_at_2a8 (off' := 0x2AC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv196
  obtain ⟨n197, v197, d197, hv197, u197⟩ := u196.aluG hc psm_at_2ac (off' := 0x2AE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv197
  obtain ⟨n198, v198, d198, hv198, u198⟩ := u197.aluG hc psm_at_2ae (off' := 0x2B2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv198
  obtain ⟨n199, v199, d199, hv199, u199⟩ := u198.aluG hc psm_at_2b2 (off' := 0x2B4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv199
  have qo1 : reg n199 ra = v192 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n199 sp = F := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n199 (3 : Fin 32) = G3 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n199 (4 : Fin 32) = G4 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n199 (5 : Fin 32) = v3 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n199 (6 : Fin 32) = v12 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n199 (7 : Fin 32) = v161 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n199 (8 : Fin 32) = v188 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n199 (9 : Fin 32) = v186 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n199 a0 = v197 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n199 a1 = v199 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n199 a2 = v168 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n199 a3 = v181 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n199 a4 = v195 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n199 a5 = v196 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n199 a6 = v18 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n199 a7 = v17 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n199 (18 : Fin 32) = v170 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n199 (19 : Fin 32) = v10 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n199 (20 : Fin 32) = v154 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n199 (21 : Fin 32) = v177 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n199 (22 : Fin 32) = v149 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n199 (23 : Fin 32) = v143 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n199 (24 : Fin 32) = v129 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n199 (25 : Fin 32) = v137 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n199 (26 : Fin 32) = v9 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n199 (27 : Fin 32) = v169 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n199 (28 : Fin 32) = v158 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n199 (29 : Fin 32) = v4 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n199 (30 : Fin 32) = v19 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n199 (31 : Fin 32) = v171 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
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
  exact ⟨n199, Mi, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174, v175, v176, v177, v178, v179, v180, v181, v182, v183, v184, v185, v186, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198, v199, (.cons d160 (.cons d161 (.cons d162 (.cons d163 (.cons d164 (.cons d165 (.cons d166 (.cons d167 (.cons d168 (.cons d169 (.cons d170 (.cons d171 (.cons d172 (.cons d173 (.cons d174 (.cons d175 (.cons d176 (.cons d177 (.cons d178 (.cons d179 (.cons d180 (.cons d181 (.cons d182 (.cons d183 (.cons d184 (.cons d185 (.cons d186 (.cons d187 (.cons d188 (.cons d189 (.cons d190 (.cons d191 (.cons d192 (.cons d193 (.cons d194 (.cons d195 (.cons d196 (.cons d197 (.cons d198 (.single d199)))))))))))))))))))))))))))))))))))))))), u199.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv160, hv161, hv162, hv163, hv164, hv165, hv166, hv167, hv168, hv169, hv170, hv171, hv172, hv173, hv174, hv175, hv176, hv177, hv178, hv179, hv180, hv181, hv182, hv183, hv184, hv185, hv186, hv187, hv188, hv189, hv190, hv191, hv192, hv193, hv194, hv195, hv196, hv197, hv198, hv199⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g5 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v3 v4 v7 v9 v10 v12 v17 v18 v19 v129 v137 v143 v149 v154 v158 v161 v168 v169 v170 v171 v177 v181 v186 v188 v192 v195 v196 v197 v199 : Word}
    (s : St Mi B n 0x2B4 (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q1 : reg n ra = v192)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v3)
    (q6 : reg n (6 : Fin 32) = v12)
    (q7 : reg n (7 : Fin 32) = v161)
    (q8 : reg n (8 : Fin 32) = v188)
    (q9 : reg n (9 : Fin 32) = v186)
    (q10 : reg n a0 = v197)
    (q11 : reg n a1 = v199)
    (q12 : reg n a2 = v168)
    (q13 : reg n a3 = v181)
    (q14 : reg n a4 = v195)
    (q15 : reg n a5 = v196)
    (q16 : reg n a6 = v18)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v170)
    (q19 : reg n (19 : Fin 32) = v10)
    (q20 : reg n (20 : Fin 32) = v154)
    (q21 : reg n (21 : Fin 32) = v177)
    (q22 : reg n (22 : Fin 32) = v149)
    (q23 : reg n (23 : Fin 32) = v143)
    (q24 : reg n (24 : Fin 32) = v129)
    (q25 : reg n (25 : Fin 32) = v137)
    (q26 : reg n (26 : Fin 32) = v9)
    (q27 : reg n (27 : Fin 32) = v169)
    (q28 : reg n (28 : Fin 32) = v158)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v200 v201 v202 v203 v204 v205 v206 v207 v208 v209 v210 v211 v212 v213 v214 v215 v216 v217 v218 v219 v220 v221 v222 v223 v224 v225 v226 v227 v228 v229 v230 v231 v232 v233 v234 v235 v236 v237 v238 v239 : Word),
      Steps n n' ∧
      St M' B n' 0x33A (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v192 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v3 ∧
      reg n' (6 : Fin 32) = v12 ∧
      reg n' (7 : Fin 32) = v222 ∧
      reg n' (8 : Fin 32) = v233 ∧
      reg n' (9 : Fin 32) = v234 ∧
      reg n' a0 = v239 ∧
      reg n' a1 = v238 ∧
      reg n' a2 = v168 ∧
      reg n' a3 = v237 ∧
      reg n' a4 = v235 ∧
      reg n' a5 = v230 ∧
      reg n' a6 = v18 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v170 ∧
      reg n' (19 : Fin 32) = v10 ∧
      reg n' (20 : Fin 32) = v223 ∧
      reg n' (21 : Fin 32) = v227 ∧
      reg n' (22 : Fin 32) = v236 ∧
      reg n' (23 : Fin 32) = v200 ∧
      reg n' (24 : Fin 32) = v212 ∧
      reg n' (25 : Fin 32) = v206 ∧
      reg n' (26 : Fin 32) = v218 ∧
      reg n' (27 : Fin 32) = v169 ∧
      reg n' (28 : Fin 32) = v217 ∧
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
      aluEval .add v195 v197 = v200 ∧
      aluEval .sltu v200 v195 = v201 ∧
      aluEval .add v9 v9 = v202 ∧
      aluEval .add v199 v201 = v203 ∧
      aluEval .sub v149 v202 = v204 ∧
      aluEval .sltu v204 v149 = v205 ∧
      aluEval .add v204 v203 = v206 ∧
      aluEval .add v205 v196 = v207 ∧
      aluEval .sltu v206 v204 = v208 ∧
      aluEval .add v208 v207 = v209 ∧
      aluEval .sub v154 v9 = v210 ∧
      aluEval .sltu v210 v154 = v211 ∧
      aluEval .add v210 v209 = v212 ∧
      aluEval .add v211 v188 = v213 ∧
      aluEval .sltu v212 v210 = v214 ∧
      aluEval .add v214 v213 = v215 ∧
      aluEval .mul v10 v3 = v216 ∧
      aluEval .add v158 v215 = v217 ∧
      aluEval .add v9 v161 = v218 ∧
      aluEval .mulhu v10 v3 = v219 ∧
      aluEval .mul v10 v4 = v220 ∧
      aluEval .sltu v217 v215 = v221 ∧
      aluEval .sltu v218 v161 = v222 ∧
      aluEval .add v221 v218 = v223 ∧
      aluEval .mulhu v10 v4 = v224 ∧
      aluEval .and v177 0xFFFFFFFE = v225 ∧
      aluEval .mul v10 v12 = v226 ∧
      aluEval .sltu v223 v218 = v227 ∧
      aluEval .add v216 v225 = v228 ∧
      aluEval .sltu v228 v225 = v229 ∧
      aluEval .mulhu v10 v12 = v230 ∧
      aluEval .add v229 v219 = v231 ∧
      aluEval .add v220 v186 = v232 ∧
      aluEval .sltu v232 v186 = v233 ∧
      aluEval .mul v10 v19 = v234 ∧
      aluEval .add v224 v233 = v235 ∧
      aluEval .add v232 v231 = v236 ∧
      aluEval .add v226 v192 = v237 ∧
      aluEval .mulhu v10 v19 = v238 ∧
      aluEval .sltu v236 v232 = v239 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n200, v200, d200, hv200, u200⟩ := s.aluG hc psm_at_2b4 (off' := 0x2B8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv200
  obtain ⟨n201, v201, d201, hv201, u201⟩ := u200.aluG hc psm_at_2b8 (off' := 0x2BC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv201
  obtain ⟨n202, v202, d202, hv202, u202⟩ := u201.aluG hc psm_at_2bc (off' := 0x2C0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv202
  obtain ⟨n203, v203, d203, hv203, u203⟩ := u202.aluG hc psm_at_2c0 (off' := 0x2C2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv203
  obtain ⟨n204, v204, d204, hv204, u204⟩ := u203.aluG hc psm_at_2c2 (off' := 0x2C6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv204
  obtain ⟨n205, v205, d205, hv205, u205⟩ := u204.aluG hc psm_at_2c6 (off' := 0x2CA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv205
  obtain ⟨n206, v206, d206, hv206, u206⟩ := u205.aluG hc psm_at_2ca (off' := 0x2CE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv206
  obtain ⟨n207, v207, d207, hv207, u207⟩ := u206.aluG hc psm_at_2ce (off' := 0x2D0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv207
  obtain ⟨n208, v208, d208, hv208, u208⟩ := u207.aluG hc psm_at_2d0 (off' := 0x2D4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv208
  obtain ⟨n209, v209, d209, hv209, u209⟩ := u208.aluG hc psm_at_2d4 (off' := 0x2D6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv209
  obtain ⟨n210, v210, d210, hv210, u210⟩ := u209.aluG hc psm_at_2d6 (off' := 0x2DA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv210
  obtain ⟨n211, v211, d211, hv211, u211⟩ := u210.aluG hc psm_at_2da (off' := 0x2DE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv211
  obtain ⟨n212, v212, d212, hv212, u212⟩ := u211.aluG hc psm_at_2de (off' := 0x2E2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv212
  obtain ⟨n213, v213, d213, hv213, u213⟩ := u212.aluG hc psm_at_2e2 (off' := 0x2E4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv213
  obtain ⟨n214, v214, d214, hv214, u214⟩ := u213.aluG hc psm_at_2e4 (off' := 0x2E8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv214
  obtain ⟨n215, v215, d215, hv215, u215⟩ := u214.aluG hc psm_at_2e8 (off' := 0x2EA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv215
  obtain ⟨n216, v216, d216, hv216, u216⟩ := u215.aluG hc psm_at_2ea (off' := 0x2EE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv216
  obtain ⟨n217, v217, d217, hv217, u217⟩ := u216.aluG hc psm_at_2ee (off' := 0x2F0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv217
  obtain ⟨n218, v218, d218, hv218, u218⟩ := u217.aluG hc psm_at_2f0 (off' := 0x2F2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv218
  obtain ⟨n219, v219, d219, hv219, u219⟩ := u218.aluG hc psm_at_2f2 (off' := 0x2F6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv219
  obtain ⟨n220, v220, d220, hv220, u220⟩ := u219.aluG hc psm_at_2f6 (off' := 0x2FA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv220
  obtain ⟨n221, v221, d221, hv221, u221⟩ := u220.aluG hc psm_at_2fa (off' := 0x2FE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv221
  obtain ⟨n222, v222, d222, hv222, u222⟩ := u221.aluG hc psm_at_2fe (off' := 0x302) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv222
  obtain ⟨n223, v223, d223, hv223, u223⟩ := u222.aluG hc psm_at_302 (off' := 0x304) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv223
  obtain ⟨n224, v224, d224, hv224, u224⟩ := u223.aluG hc psm_at_304 (off' := 0x308) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv224
  obtain ⟨n225, v225, d225, hv225, u225⟩ := u224.aluImmG hc psm_at_308 (off' := 0x30C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv225
  obtain ⟨n226, v226, d226, hv226, u226⟩ := u225.aluG hc psm_at_30c (off' := 0x310) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv226
  obtain ⟨n227, v227, d227, hv227, u227⟩ := u226.aluG hc psm_at_310 (off' := 0x314) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv227
  obtain ⟨n228, v228, d228, hv228, u228⟩ := u227.aluG hc psm_at_314 (off' := 0x316) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv228
  obtain ⟨n229, v229, d229, hv229, u229⟩ := u228.aluG hc psm_at_316 (off' := 0x31A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv229
  obtain ⟨n230, v230, d230, hv230, u230⟩ := u229.aluG hc psm_at_31a (off' := 0x31E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv230
  obtain ⟨n231, v231, d231, hv231, u231⟩ := u230.aluG hc psm_at_31e (off' := 0x320) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv231
  obtain ⟨n232, v232, d232, hv232, u232⟩ := u231.aluG hc psm_at_320 (off' := 0x322) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv232
  obtain ⟨n233, v233, d233, hv233, u233⟩ := u232.aluG hc psm_at_322 (off' := 0x326) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv233
  obtain ⟨n234, v234, d234, hv234, u234⟩ := u233.aluG hc psm_at_326 (off' := 0x32A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv234
  obtain ⟨n235, v235, d235, hv235, u235⟩ := u234.aluG hc psm_at_32a (off' := 0x32C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv235
  obtain ⟨n236, v236, d236, hv236, u236⟩ := u235.aluG hc psm_at_32c (off' := 0x330) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv236
  obtain ⟨n237, v237, d237, hv237, u237⟩ := u236.aluG hc psm_at_330 (off' := 0x332) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv237
  obtain ⟨n238, v238, d238, hv238, u238⟩ := u237.aluG hc psm_at_332 (off' := 0x336) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv238
  obtain ⟨n239, v239, d239, hv239, u239⟩ := u238.aluG hc psm_at_336 (off' := 0x33A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv239
  have qo1 : reg n239 ra = v192 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n239 sp = F := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n239 (3 : Fin 32) = G3 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n239 (4 : Fin 32) = G4 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n239 (5 : Fin 32) = v3 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n239 (6 : Fin 32) = v12 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n239 (7 : Fin 32) = v222 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n239 (8 : Fin 32) = v233 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n239 (9 : Fin 32) = v234 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n239 a0 = v239 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n239 a1 = v238 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n239 a2 = v168 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n239 a3 = v237 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n239 a4 = v235 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n239 a5 = v230 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n239 a6 = v18 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n239 a7 = v17 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n239 (18 : Fin 32) = v170 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n239 (19 : Fin 32) = v10 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n239 (20 : Fin 32) = v223 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n239 (21 : Fin 32) = v227 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n239 (22 : Fin 32) = v236 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n239 (23 : Fin 32) = v200 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n239 (24 : Fin 32) = v212 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n239 (25 : Fin 32) = v206 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n239 (26 : Fin 32) = v218 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n239 (27 : Fin 32) = v169 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n239 (28 : Fin 32) = v217 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n239 (29 : Fin 32) = v4 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n239 (30 : Fin 32) = v19 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n239 (31 : Fin 32) = v171 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
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
  exact ⟨n239, Mi, v200, v201, v202, v203, v204, v205, v206, v207, v208, v209, v210, v211, v212, v213, v214, v215, v216, v217, v218, v219, v220, v221, v222, v223, v224, v225, v226, v227, v228, v229, v230, v231, v232, v233, v234, v235, v236, v237, v238, v239, (.cons d200 (.cons d201 (.cons d202 (.cons d203 (.cons d204 (.cons d205 (.cons d206 (.cons d207 (.cons d208 (.cons d209 (.cons d210 (.cons d211 (.cons d212 (.cons d213 (.cons d214 (.cons d215 (.cons d216 (.cons d217 (.cons d218 (.cons d219 (.cons d220 (.cons d221 (.cons d222 (.cons d223 (.cons d224 (.cons d225 (.cons d226 (.cons d227 (.cons d228 (.cons d229 (.cons d230 (.cons d231 (.cons d232 (.cons d233 (.cons d234 (.cons d235 (.cons d236 (.cons d237 (.cons d238 (.single d239)))))))))))))))))))))))))))))))))))))))), u239.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv200, hv201, hv202, hv203, hv204, hv205, hv206, hv207, hv208, hv209, hv210, hv211, hv212, hv213, hv214, hv215, hv216, hv217, hv218, hv219, hv220, hv221, hv222, hv223, hv224, hv225, hv226, hv227, hv228, hv229, hv230, hv231, hv232, hv233, hv234, hv235, hv236, hv237, hv238, hv239⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g6 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v3 v4 v7 v10 v12 v17 v18 v19 v168 v169 v170 v171 v192 v200 v206 v212 v217 v218 v222 v223 v227 v230 v233 v234 v235 v236 v237 v238 v239 : Word}
    (s : St Mi B n 0x33A (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q1 : reg n ra = v192)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v3)
    (q6 : reg n (6 : Fin 32) = v12)
    (q7 : reg n (7 : Fin 32) = v222)
    (q8 : reg n (8 : Fin 32) = v233)
    (q9 : reg n (9 : Fin 32) = v234)
    (q10 : reg n a0 = v239)
    (q11 : reg n a1 = v238)
    (q12 : reg n a2 = v168)
    (q13 : reg n a3 = v237)
    (q14 : reg n a4 = v235)
    (q15 : reg n a5 = v230)
    (q16 : reg n a6 = v18)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v170)
    (q19 : reg n (19 : Fin 32) = v10)
    (q20 : reg n (20 : Fin 32) = v223)
    (q21 : reg n (21 : Fin 32) = v227)
    (q22 : reg n (22 : Fin 32) = v236)
    (q23 : reg n (23 : Fin 32) = v200)
    (q24 : reg n (24 : Fin 32) = v212)
    (q25 : reg n (25 : Fin 32) = v206)
    (q26 : reg n (26 : Fin 32) = v218)
    (q27 : reg n (27 : Fin 32) = v169)
    (q28 : reg n (28 : Fin 32) = v217)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v240 v241 v242 v243 v244 v245 v246 v247 v248 v249 v250 v251 v252 v253 v254 v255 v256 v257 v258 v259 v260 v261 v262 v263 v264 v265 v266 v267 v268 v269 v270 v271 v272 v273 v274 v275 v276 v277 v278 v279 : Word),
      Steps n n' ∧
      St M' B n' 0x3BA (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v192 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v3 ∧
      reg n' (6 : Fin 32) = v12 ∧
      reg n' (7 : Fin 32) = v273 ∧
      reg n' (8 : Fin 32) = v272 ∧
      reg n' (9 : Fin 32) = v253 ∧
      reg n' a0 = v243 ∧
      reg n' a1 = v274 ∧
      reg n' a2 = v168 ∧
      reg n' a3 = v278 ∧
      reg n' a4 = v244 ∧
      reg n' a5 = v276 ∧
      reg n' a6 = v18 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v170 ∧
      reg n' (19 : Fin 32) = v277 ∧
      reg n' (20 : Fin 32) = v275 ∧
      reg n' (21 : Fin 32) = v279 ∧
      reg n' (22 : Fin 32) = v236 ∧
      reg n' (23 : Fin 32) = v250 ∧
      reg n' (24 : Fin 32) = v264 ∧
      reg n' (25 : Fin 32) = v270 ∧
      reg n' (26 : Fin 32) = v257 ∧
      reg n' (27 : Fin 32) = v169 ∧
      reg n' (28 : Fin 32) = v217 ∧
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
      aluEval .sltu v237 v192 = v240 ∧
      aluEval .add v239 v235 = v241 ∧
      aluEval .add v230 v240 = v242 ∧
      aluEval .add v241 v237 = v243 ∧
      aluEval .mulhu v10 v17 = v244 ∧
      aluEval .sltu v243 v237 = v245 ∧
      aluEval .add v234 v200 = v246 ∧
      aluEval .add v245 v242 = v247 ∧
      aluEval .sltu v246 v200 = v248 ∧
      aluEval .add v238 v248 = v249 ∧
      aluEval .add v246 v247 = v250 ∧
      aluEval .sub v206 v10 = v251 ∧
      aluEval .mulhu v10 v18 = v252 ∧
      aluEval .sltu v250 v246 = v253 ∧
      aluEval .sltu v251 v206 = v254 ∧
      aluEval .add v249 v253 = v255 ∧
      aluEval .add v254 v244 = v256 ∧
      aluEval .add v251 v255 = v257 ∧
      aluEval .add v10 v10 = v258 ∧
      aluEval .sltu v257 v251 = v259 ∧
      aluEval .sub v212 v258 = v260 ∧
      aluEval .add v256 v259 = v261 ∧
      aluEval .sltu v260 v212 = v262 ∧
      aluEval .add v262 v252 = v263 ∧
      aluEval .add v260 v261 = v264 ∧
      aluEval .sltu v264 v260 = v265 ∧
      aluEval .sub v217 v10 = v266 ∧
      aluEval .add v265 v263 = v267 ∧
      aluEval .sltu v266 v217 = v268 ∧
      aluEval .add v268 v244 = v269 ∧
      aluEval .add v266 v267 = v270 ∧
      aluEval .sltu v270 v266 = v271 ∧
      aluEval .mul v168 v3 = v272 ∧
      aluEval .add v222 v227 = v273 ∧
      aluEval .add v271 v269 = v274 ∧
      aluEval .add v223 v274 = v275 ∧
      aluEval .mul v168 v4 = v276 ∧
      aluEval .add v10 v273 = v277 ∧
      aluEval .mulhu v168 v3 = v278 ∧
      aluEval .sltu v275 v274 = v279 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n240, v240, d240, hv240, u240⟩ := s.aluG hc psm_at_33a (off' := 0x33E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv240
  obtain ⟨n241, v241, d241, hv241, u241⟩ := u240.aluG hc psm_at_33e (off' := 0x340) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv241
  obtain ⟨n242, v242, d242, hv242, u242⟩ := u241.aluG hc psm_at_340 (off' := 0x342) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv242
  obtain ⟨n243, v243, d243, hv243, u243⟩ := u242.aluG hc psm_at_342 (off' := 0x344) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv243
  obtain ⟨n244, v244, d244, hv244, u244⟩ := u243.aluG hc psm_at_344 (off' := 0x348) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv244
  obtain ⟨n245, v245, d245, hv245, u245⟩ := u244.aluG hc psm_at_348 (off' := 0x34C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv245
  obtain ⟨n246, v246, d246, hv246, u246⟩ := u245.aluG hc psm_at_34c (off' := 0x34E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv246
  obtain ⟨n247, v247, d247, hv247, u247⟩ := u246.aluG hc psm_at_34e (off' := 0x350) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv247
  obtain ⟨n248, v248, d248, hv248, u248⟩ := u247.aluG hc psm_at_350 (off' := 0x354) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv248
  obtain ⟨n249, v249, d249, hv249, u249⟩ := u248.aluG hc psm_at_354 (off' := 0x356) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv249
  obtain ⟨n250, v250, d250, hv250, u250⟩ := u249.aluG hc psm_at_356 (off' := 0x35A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv250
  obtain ⟨n251, v251, d251, hv251, u251⟩ := u250.aluG hc psm_at_35a (off' := 0x35E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv251
  obtain ⟨n252, v252, d252, hv252, u252⟩ := u251.aluG hc psm_at_35e (off' := 0x362) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv252
  obtain ⟨n253, v253, d253, hv253, u253⟩ := u252.aluG hc psm_at_362 (off' := 0x366) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv253
  obtain ⟨n254, v254, d254, hv254, u254⟩ := u253.aluG hc psm_at_366 (off' := 0x36A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv254
  obtain ⟨n255, v255, d255, hv255, u255⟩ := u254.aluG hc psm_at_36a (off' := 0x36C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv255
  obtain ⟨n256, v256, d256, hv256, u256⟩ := u255.aluG hc psm_at_36c (off' := 0x36E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv256
  obtain ⟨n257, v257, d257, hv257, u257⟩ := u256.aluG hc psm_at_36e (off' := 0x372) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv257
  obtain ⟨n258, v258, d258, hv258, u258⟩ := u257.aluG hc psm_at_372 (off' := 0x376) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv258
  obtain ⟨n259, v259, d259, hv259, u259⟩ := u258.aluG hc psm_at_376 (off' := 0x37A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv259
  obtain ⟨n260, v260, d260, hv260, u260⟩ := u259.aluG hc psm_at_37a (off' := 0x37E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv260
  obtain ⟨n261, v261, d261, hv261, u261⟩ := u260.aluG hc psm_at_37e (off' := 0x380) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv261
  obtain ⟨n262, v262, d262, hv262, u262⟩ := u261.aluG hc psm_at_380 (off' := 0x384) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv262
  obtain ⟨n263, v263, d263, hv263, u263⟩ := u262.aluG hc psm_at_384 (off' := 0x386) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv263
  obtain ⟨n264, v264, d264, hv264, u264⟩ := u263.aluG hc psm_at_386 (off' := 0x38A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv264
  obtain ⟨n265, v265, d265, hv265, u265⟩ := u264.aluG hc psm_at_38a (off' := 0x38E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv265
  obtain ⟨n266, v266, d266, hv266, u266⟩ := u265.aluG hc psm_at_38e (off' := 0x392) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv266
  obtain ⟨n267, v267, d267, hv267, u267⟩ := u266.aluG hc psm_at_392 (off' := 0x394) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv267
  obtain ⟨n268, v268, d268, hv268, u268⟩ := u267.aluG hc psm_at_394 (off' := 0x398) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv268
  obtain ⟨n269, v269, d269, hv269, u269⟩ := u268.aluG hc psm_at_398 (off' := 0x39A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv269
  obtain ⟨n270, v270, d270, hv270, u270⟩ := u269.aluG hc psm_at_39a (off' := 0x39E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv270
  obtain ⟨n271, v271, d271, hv271, u271⟩ := u270.aluG hc psm_at_39e (off' := 0x3A2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv271
  obtain ⟨n272, v272, d272, hv272, u272⟩ := u271.aluG hc psm_at_3a2 (off' := 0x3A6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv272
  obtain ⟨n273, v273, d273, hv273, u273⟩ := u272.aluG hc psm_at_3a6 (off' := 0x3A8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv273
  obtain ⟨n274, v274, d274, hv274, u274⟩ := u273.aluG hc psm_at_3a8 (off' := 0x3AA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv274
  obtain ⟨n275, v275, d275, hv275, u275⟩ := u274.aluG hc psm_at_3aa (off' := 0x3AC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv275
  obtain ⟨n276, v276, d276, hv276, u276⟩ := u275.aluG hc psm_at_3ac (off' := 0x3B0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv276
  obtain ⟨n277, v277, d277, hv277, u277⟩ := u276.aluG hc psm_at_3b0 (off' := 0x3B2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv277
  obtain ⟨n278, v278, d278, hv278, u278⟩ := u277.aluG hc psm_at_3b2 (off' := 0x3B6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv278
  obtain ⟨n279, v279, d279, hv279, u279⟩ := u278.aluG hc psm_at_3b6 (off' := 0x3BA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv279
  have qo1 : reg n279 ra = v192 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n279 sp = F := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n279 (3 : Fin 32) = G3 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n279 (4 : Fin 32) = G4 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n279 (5 : Fin 32) = v3 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n279 (6 : Fin 32) = v12 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n279 (7 : Fin 32) = v273 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n279 (8 : Fin 32) = v272 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n279 (9 : Fin 32) = v253 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n279 a0 = v243 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n279 a1 = v274 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n279 a2 = v168 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n279 a3 = v278 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n279 a4 = v244 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n279 a5 = v276 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n279 a6 = v18 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n279 a7 = v17 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n279 (18 : Fin 32) = v170 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n279 (19 : Fin 32) = v277 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n279 (20 : Fin 32) = v275 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n279 (21 : Fin 32) = v279 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n279 (22 : Fin 32) = v236 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n279 (23 : Fin 32) = v250 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n279 (24 : Fin 32) = v264 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n279 (25 : Fin 32) = v270 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n279 (26 : Fin 32) = v257 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n279 (27 : Fin 32) = v169 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n279 (28 : Fin 32) = v217 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n279 (29 : Fin 32) = v4 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n279 (30 : Fin 32) = v19 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n279 (31 : Fin 32) = v171 := by rw [u279.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
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
  exact ⟨n279, Mi, v240, v241, v242, v243, v244, v245, v246, v247, v248, v249, v250, v251, v252, v253, v254, v255, v256, v257, v258, v259, v260, v261, v262, v263, v264, v265, v266, v267, v268, v269, v270, v271, v272, v273, v274, v275, v276, v277, v278, v279, (.cons d240 (.cons d241 (.cons d242 (.cons d243 (.cons d244 (.cons d245 (.cons d246 (.cons d247 (.cons d248 (.cons d249 (.cons d250 (.cons d251 (.cons d252 (.cons d253 (.cons d254 (.cons d255 (.cons d256 (.cons d257 (.cons d258 (.cons d259 (.cons d260 (.cons d261 (.cons d262 (.cons d263 (.cons d264 (.cons d265 (.cons d266 (.cons d267 (.cons d268 (.cons d269 (.cons d270 (.cons d271 (.cons d272 (.cons d273 (.cons d274 (.cons d275 (.cons d276 (.cons d277 (.cons d278 (.single d279)))))))))))))))))))))))))))))))))))))))), u279.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv240, hv241, hv242, hv243, hv244, hv245, hv246, hv247, hv248, hv249, hv250, hv251, hv252, hv253, hv254, hv255, hv256, hv257, hv258, hv259, hv260, hv261, hv262, hv263, hv264, hv265, hv266, hv267, hv268, hv269, hv270, hv271, hv272, hv273, hv274, hv275, hv276, hv277, hv278, hv279⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g7 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v3 v4 v7 v12 v17 v18 v19 v168 v169 v170 v171 v192 v217 v236 v243 v244 v250 v253 v257 v264 v270 v272 v273 v274 v275 v276 v277 v278 v279 : Word}
    (s : St Mi B n 0x3BA (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q1 : reg n ra = v192)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v3)
    (q6 : reg n (6 : Fin 32) = v12)
    (q7 : reg n (7 : Fin 32) = v273)
    (q8 : reg n (8 : Fin 32) = v272)
    (q9 : reg n (9 : Fin 32) = v253)
    (q10 : reg n a0 = v243)
    (q11 : reg n a1 = v274)
    (q12 : reg n a2 = v168)
    (q13 : reg n a3 = v278)
    (q14 : reg n a4 = v244)
    (q15 : reg n a5 = v276)
    (q16 : reg n a6 = v18)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v170)
    (q19 : reg n (19 : Fin 32) = v277)
    (q20 : reg n (20 : Fin 32) = v275)
    (q21 : reg n (21 : Fin 32) = v279)
    (q22 : reg n (22 : Fin 32) = v236)
    (q23 : reg n (23 : Fin 32) = v250)
    (q24 : reg n (24 : Fin 32) = v264)
    (q25 : reg n (25 : Fin 32) = v270)
    (q26 : reg n (26 : Fin 32) = v257)
    (q27 : reg n (27 : Fin 32) = v169)
    (q28 : reg n (28 : Fin 32) = v217)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v280 v281 v282 v283 v284 v285 v286 v287 v288 v289 v290 v291 v292 v293 v294 v295 v296 v297 v298 v299 v300 v301 v302 v303 v304 v305 v306 v307 v308 v309 v310 v311 v312 v313 v314 v315 v316 v317 v318 v319 : Word),
      Steps n n' ∧
      St M' B n' 0x43E (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v300 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v3 ∧
      reg n' (6 : Fin 32) = v12 ∧
      reg n' (7 : Fin 32) = v280 ∧
      reg n' (8 : Fin 32) = v302 ∧
      reg n' (9 : Fin 32) = v295 ∧
      reg n' a0 = v318 ∧
      reg n' a1 = v317 ∧
      reg n' a2 = v168 ∧
      reg n' a3 = v319 ∧
      reg n' a4 = v310 ∧
      reg n' a5 = v287 ∧
      reg n' a6 = v18 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v170 ∧
      reg n' (19 : Fin 32) = v277 ∧
      reg n' (20 : Fin 32) = v275 ∧
      reg n' (21 : Fin 32) = v285 ∧
      reg n' (22 : Fin 32) = v314 ∧
      reg n' (23 : Fin 32) = v250 ∧
      reg n' (24 : Fin 32) = v264 ∧
      reg n' (25 : Fin 32) = v270 ∧
      reg n' (26 : Fin 32) = v306 ∧
      reg n' (27 : Fin 32) = v169 ∧
      reg n' (28 : Fin 32) = v291 ∧
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
      aluEval .sltu v277 v273 = v280 ∧
      aluEval .and v236 0xFFFFFFFE = v281 ∧
      aluEval .mulhu v168 v4 = v282 ∧
      aluEval .add v272 v281 = v283 ∧
      aluEval .mul v168 v12 = v284 ∧
      aluEval .add v279 v277 = v285 ∧
      aluEval .sltu v283 v281 = v286 ∧
      aluEval .add v276 v243 = v287 ∧
      aluEval .mulhu v168 v12 = v288 ∧
      aluEval .add v286 v278 = v289 ∧
      aluEval .sltu v287 v243 = v290 ∧
      aluEval .add v287 v289 = v291 ∧
      aluEval .mul v168 v19 = v292 ∧
      aluEval .add v290 v282 = v293 ∧
      aluEval .sltu v291 v287 = v294 ∧
      aluEval .add v284 v250 = v295 ∧
      aluEval .mulhu v168 v19 = v296 ∧
      aluEval .add v293 v294 = v297 ∧
      aluEval .sltu v295 v250 = v298 ∧
      aluEval .add v298 v288 = v299 ∧
      aluEval .add v295 v297 = v300 ∧
      aluEval .sltu v300 v295 = v301 ∧
      aluEval .mulhu v168 v17 = v302 ∧
      aluEval .add v301 v299 = v303 ∧
      aluEval .add v292 v257 = v304 ∧
      aluEval .sltu v304 v257 = v305 ∧
      aluEval .add v304 v303 = v306 ∧
      aluEval .add v305 v296 = v307 ∧
      aluEval .sltu v306 v304 = v308 ∧
      aluEval .sub v264 v168 = v309 ∧
      aluEval .mulhu v168 v18 = v310 ∧
      aluEval .add v308 v307 = v311 ∧
      aluEval .sltu v309 v264 = v312 ∧
      aluEval .add v312 v302 = v313 ∧
      aluEval .add v309 v311 = v314 ∧
      aluEval .sltu v314 v309 = v315 ∧
      aluEval .add v168 v168 = v316 ∧
      aluEval .add v315 v313 = v317 ∧
      aluEval .sub v270 v316 = v318 ∧
      aluEval .sltu v318 v270 = v319 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n280, v280, d280, hv280, u280⟩ := s.aluG hc psm_at_3ba (off' := 0x3BE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv280
  obtain ⟨n281, v281, d281, hv281, u281⟩ := u280.aluImmG hc psm_at_3be (off' := 0x3C2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv281
  obtain ⟨n282, v282, d282, hv282, u282⟩ := u281.aluG hc psm_at_3c2 (off' := 0x3C6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv282
  obtain ⟨n283, v283, d283, hv283, u283⟩ := u282.aluG hc psm_at_3c6 (off' := 0x3C8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv283
  obtain ⟨n284, v284, d284, hv284, u284⟩ := u283.aluG hc psm_at_3c8 (off' := 0x3CC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv284
  obtain ⟨n285, v285, d285, hv285, u285⟩ := u284.aluG hc psm_at_3cc (off' := 0x3CE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv285
  obtain ⟨n286, v286, d286, hv286, u286⟩ := u285.aluG hc psm_at_3ce (off' := 0x3D2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv286
  obtain ⟨n287, v287, d287, hv287, u287⟩ := u286.aluG hc psm_at_3d2 (off' := 0x3D4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv287
  obtain ⟨n288, v288, d288, hv288, u288⟩ := u287.aluG hc psm_at_3d4 (off' := 0x3D8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv288
  obtain ⟨n289, v289, d289, hv289, u289⟩ := u288.aluG hc psm_at_3d8 (off' := 0x3DA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv289
  obtain ⟨n290, v290, d290, hv290, u290⟩ := u289.aluG hc psm_at_3da (off' := 0x3DE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv290
  obtain ⟨n291, v291, d291, hv291, u291⟩ := u290.aluG hc psm_at_3de (off' := 0x3E2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv291
  obtain ⟨n292, v292, d292, hv292, u292⟩ := u291.aluG hc psm_at_3e2 (off' := 0x3E6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv292
  obtain ⟨n293, v293, d293, hv293, u293⟩ := u292.aluG hc psm_at_3e6 (off' := 0x3E8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv293
  obtain ⟨n294, v294, d294, hv294, u294⟩ := u293.aluG hc psm_at_3e8 (off' := 0x3EC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv294
  obtain ⟨n295, v295, d295, hv295, u295⟩ := u294.aluG hc psm_at_3ec (off' := 0x3EE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv295
  obtain ⟨n296, v296, d296, hv296, u296⟩ := u295.aluG hc psm_at_3ee (off' := 0x3F2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv296
  obtain ⟨n297, v297, d297, hv297, u297⟩ := u296.aluG hc psm_at_3f2 (off' := 0x3F4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv297
  obtain ⟨n298, v298, d298, hv298, u298⟩ := u297.aluG hc psm_at_3f4 (off' := 0x3F8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv298
  obtain ⟨n299, v299, d299, hv299, u299⟩ := u298.aluG hc psm_at_3f8 (off' := 0x3FA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv299
  obtain ⟨n300, v300, d300, hv300, u300⟩ := u299.aluG hc psm_at_3fa (off' := 0x3FE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv300
  obtain ⟨n301, v301, d301, hv301, u301⟩ := u300.aluG hc psm_at_3fe (off' := 0x402) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv301
  obtain ⟨n302, v302, d302, hv302, u302⟩ := u301.aluG hc psm_at_402 (off' := 0x406) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv302
  obtain ⟨n303, v303, d303, hv303, u303⟩ := u302.aluG hc psm_at_406 (off' := 0x408) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv303
  obtain ⟨n304, v304, d304, hv304, u304⟩ := u303.aluG hc psm_at_408 (off' := 0x40A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv304
  obtain ⟨n305, v305, d305, hv305, u305⟩ := u304.aluG hc psm_at_40a (off' := 0x40E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv305
  obtain ⟨n306, v306, d306, hv306, u306⟩ := u305.aluG hc psm_at_40e (off' := 0x412) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv306
  obtain ⟨n307, v307, d307, hv307, u307⟩ := u306.aluG hc psm_at_412 (off' := 0x414) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv307
  obtain ⟨n308, v308, d308, hv308, u308⟩ := u307.aluG hc psm_at_414 (off' := 0x418) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv308
  obtain ⟨n309, v309, d309, hv309, u309⟩ := u308.aluG hc psm_at_418 (off' := 0x41C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv309
  obtain ⟨n310, v310, d310, hv310, u310⟩ := u309.aluG hc psm_at_41c (off' := 0x420) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv310
  obtain ⟨n311, v311, d311, hv311, u311⟩ := u310.aluG hc psm_at_420 (off' := 0x422) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv311
  obtain ⟨n312, v312, d312, hv312, u312⟩ := u311.aluG hc psm_at_422 (off' := 0x426) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv312
  obtain ⟨n313, v313, d313, hv313, u313⟩ := u312.aluG hc psm_at_426 (off' := 0x428) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv313
  obtain ⟨n314, v314, d314, hv314, u314⟩ := u313.aluG hc psm_at_428 (off' := 0x42C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv314
  obtain ⟨n315, v315, d315, hv315, u315⟩ := u314.aluG hc psm_at_42c (off' := 0x430) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv315
  obtain ⟨n316, v316, d316, hv316, u316⟩ := u315.aluG hc psm_at_430 (off' := 0x434) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv316
  obtain ⟨n317, v317, d317, hv317, u317⟩ := u316.aluG hc psm_at_434 (off' := 0x436) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv317
  obtain ⟨n318, v318, d318, hv318, u318⟩ := u317.aluG hc psm_at_436 (off' := 0x43A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv318
  obtain ⟨n319, v319, d319, hv319, u319⟩ := u318.aluG hc psm_at_43a (off' := 0x43E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv319
  have qo1 : reg n319 ra = v300 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n319 sp = F := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n319 (3 : Fin 32) = G3 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n319 (4 : Fin 32) = G4 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n319 (5 : Fin 32) = v3 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n319 (6 : Fin 32) = v12 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n319 (7 : Fin 32) = v280 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n319 (8 : Fin 32) = v302 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n319 (9 : Fin 32) = v295 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n319 a0 = v318 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n319 a1 = v317 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n319 a2 = v168 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n319 a3 = v319 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n319 a4 = v310 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n319 a5 = v287 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n319 a6 = v18 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n319 a7 = v17 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n319 (18 : Fin 32) = v170 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n319 (19 : Fin 32) = v277 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n319 (20 : Fin 32) = v275 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n319 (21 : Fin 32) = v285 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n319 (22 : Fin 32) = v314 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n319 (23 : Fin 32) = v250 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n319 (24 : Fin 32) = v264 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n319 (25 : Fin 32) = v270 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n319 (26 : Fin 32) = v306 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n319 (27 : Fin 32) = v169 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n319 (28 : Fin 32) = v291 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n319 (29 : Fin 32) = v4 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n319 (30 : Fin 32) = v19 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n319 (31 : Fin 32) = v171 := by rw [u319.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
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
  exact ⟨n319, Mi, v280, v281, v282, v283, v284, v285, v286, v287, v288, v289, v290, v291, v292, v293, v294, v295, v296, v297, v298, v299, v300, v301, v302, v303, v304, v305, v306, v307, v308, v309, v310, v311, v312, v313, v314, v315, v316, v317, v318, v319, (.cons d280 (.cons d281 (.cons d282 (.cons d283 (.cons d284 (.cons d285 (.cons d286 (.cons d287 (.cons d288 (.cons d289 (.cons d290 (.cons d291 (.cons d292 (.cons d293 (.cons d294 (.cons d295 (.cons d296 (.cons d297 (.cons d298 (.cons d299 (.cons d300 (.cons d301 (.cons d302 (.cons d303 (.cons d304 (.cons d305 (.cons d306 (.cons d307 (.cons d308 (.cons d309 (.cons d310 (.cons d311 (.cons d312 (.cons d313 (.cons d314 (.cons d315 (.cons d316 (.cons d317 (.cons d318 (.single d319)))))))))))))))))))))))))))))))))))))))), u319.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv280, hv281, hv282, hv283, hv284, hv285, hv286, hv287, hv288, hv289, hv290, hv291, hv292, hv293, hv294, hv295, hv296, hv297, hv298, hv299, hv300, hv301, hv302, hv303, hv304, hv305, hv306, hv307, hv308, hv309, hv310, hv311, hv312, hv313, hv314, hv315, hv316, hv317, hv318, hv319⟩

end C3.RV32
