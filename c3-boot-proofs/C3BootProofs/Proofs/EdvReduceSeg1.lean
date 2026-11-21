import C3BootProofs.Proofs.EdvReduceFacts

/-! # The inlined `Scalar::reduce` in `ed25519_verify`, segments 5 to 7

Each theorem steps 40 instructions. `scripts/gen-ev-reduce.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g5 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v8 v15 v16 v19 v22 v23 v30 v31 v33 v36 v40 v51 v53 v62 v67 v75 v87 v110 v111 v116 v118 v120 v122 v124 v132 v133 v136 v142 v143 v147 v150 v151 v152 v153 v154 v155 v156 v157 v158 v159 : Word}
    (s : St Mi B n 0x38C (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v132)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v19)
    (q6 : reg n (6 : Fin 32) = v87)
    (q7 : reg n (7 : Fin 32) = v159)
    (q8 : reg n (8 : Fin 32) = v153)
    (q9 : reg n (9 : Fin 32) = v110)
    (q10 : reg n a0 = v158)
    (q11 : reg n a1 = v156)
    (q12 : reg n a2 = v152)
    (q13 : reg n a3 = v120)
    (q14 : reg n a4 = v147)
    (q15 : reg n a5 = v143)
    (q16 : reg n a6 = v23)
    (q17 : reg n a7 = v30)
    (q18 : reg n (18 : Fin 32) = v75)
    (q19 : reg n (19 : Fin 32) = v53)
    (q20 : reg n (20 : Fin 32) = v157)
    (q21 : reg n (21 : Fin 32) = v36)
    (q22 : reg n (22 : Fin 32) = v118)
    (q23 : reg n (23 : Fin 32) = v154)
    (q24 : reg n (24 : Fin 32) = v8)
    (q25 : reg n (25 : Fin 32) = v155)
    (q26 : reg n (26 : Fin 32) = v133)
    (q27 : reg n (27 : Fin 32) = v142)
    (q28 : reg n (28 : Fin 32) = v22)
    (q29 : reg n (29 : Fin 32) = v7)
    (q30 : reg n (30 : Fin 32) = v151)
    (q31 : reg n (31 : Fin 32) = v150)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (slB0 : memLoad32 Mi (F + 0xB0) = v16)
    (slB4 : memLoad32 Mi (F + 0xB4) = v15)
    (slB8 : memLoad32 Mi (F + 0xB8) = v136)
    (slBC : memLoad32 Mi (F + 0xBC) = v120)
    (slC0 : memLoad32 Mi (F + 0xC0) = v147)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slE8 : memLoad32 Mi (F + 0xE8) = v8)
    (slEC : memLoad32 Mi (F + 0xEC) = v33)
    (slFC : memLoad32 Mi (F + 0xFC) = v40)
    (sl100 : memLoad32 Mi (F + 0x100) = v51)
    (sl104 : memLoad32 Mi (F + 0x104) = v62)
    (sl10C : memLoad32 Mi (F + 0x10C) = v31)
    (sl110 : memLoad32 Mi (F + 0x110) = v67)
    (sl114 : memLoad32 Mi (F + 0x114) = v111)
    (sl118 : memLoad32 Mi (F + 0x118) = v122)
    (sl120 : memLoad32 Mi (F + 0x120) = v116)
    (sl124 : memLoad32 Mi (F + 0x124) = v124)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v160 v161 v162 v163 v164 v165 v166 v167 v168 v169 v171 v172 v173 v174 v175 v176 v177 v178 v180 v181 v182 v183 v185 v186 v187 v188 v189 v193 v194 v195 v196 v199 : Word),
      Steps n n' ∧
      St M' B n' 0x40C (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v195 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v186 ∧
      reg n' (6 : Fin 32) = v87 ∧
      reg n' (7 : Fin 32) = v159 ∧
      reg n' (8 : Fin 32) = v133 ∧
      reg n' (9 : Fin 32) = v175 ∧
      reg n' a0 = v194 ∧
      reg n' a1 = v193 ∧
      reg n' a2 = v185 ∧
      reg n' a3 = v120 ∧
      reg n' a4 = v187 ∧
      reg n' a5 = v199 ∧
      reg n' a6 = v189 ∧
      reg n' a7 = v196 ∧
      reg n' (18 : Fin 32) = v75 ∧
      reg n' (19 : Fin 32) = v53 ∧
      reg n' (20 : Fin 32) = v181 ∧
      reg n' (21 : Fin 32) = v36 ∧
      reg n' (22 : Fin 32) = v31 ∧
      reg n' (23 : Fin 32) = v154 ∧
      reg n' (24 : Fin 32) = v173 ∧
      reg n' (25 : Fin 32) = v176 ∧
      reg n' (26 : Fin 32) = v133 ∧
      reg n' (27 : Fin 32) = v174 ∧
      reg n' (28 : Fin 32) = v162 ∧
      reg n' (29 : Fin 32) = v7 ∧
      reg n' (30 : Fin 32) = v151 ∧
      reg n' (31 : Fin 32) = v150 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0x84) = v175 ∧
      memLoad32 M' (F + 0x94) = v185 ∧
      memLoad32 M' (F + 0xA4) = v189 ∧
      memLoad32 M' (F + 0xB0) = v16 ∧
      memLoad32 M' (F + 0xB4) = v15 ∧
      memLoad32 M' (F + 0xB8) = v136 ∧
      memLoad32 M' (F + 0xBC) = v120 ∧
      memLoad32 M' (F + 0xC0) = v147 ∧
      memLoad32 M' (F + 0xC8) = v163 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xE0) = v133 ∧
      memLoad32 M' (F + 0xE8) = v8 ∧
      memLoad32 M' (F + 0xEC) = v33 ∧
      memLoad32 M' (F + 0xFC) = v40 ∧
      memLoad32 M' (F + 0x100) = v51 ∧
      memLoad32 M' (F + 0x104) = v62 ∧
      memLoad32 M' (F + 0x110) = v67 ∧
      memLoad32 M' (F + 0x114) = v111 ∧
      memLoad32 M' (F + 0x118) = v122 ∧
      memLoad32 M' (F + 0x120) = v116 ∧
      memLoad32 M' (F + 0x124) = v124 ∧
      aluEval .add v158 v156 = v160 ∧
      aluEval .sltu v159 v157 = v161 ∧
      aluEval .add v161 v160 = v162 ∧
      aluEval .srl v19 0x11 = v163 ∧
      aluEval .add v153 v147 = v164 ∧
      aluEval .add v152 v120 = v165 ∧
      aluEval .sltu v165 v152 = v166 ∧
      aluEval .sll v30 0xF = v167 ∧
      aluEval .add v166 v164 = v168 ∧
      aluEval .or v167 v163 = v169 ∧
      aluEval .mul v87 v23 = v171 ∧
      (0x932000 : Word) = v172 ∧
      aluEval .and v169 v7 = v173 ∧
      aluEval .add v172 0xFFFFF8D2 = v174 ∧
      aluEval .srl v30 0xE = v175 ∧
      aluEval .mul v151 v174 = v176 ∧
      aluEval .sll v168 0x3 = v177 ∧
      aluEval .srl v165 0x1D = v178 ∧
      aluEval .sll v31 0x12 = v180 ∧
      aluEval .mulhu v173 v7 = v181 ∧
      aluEval .or v178 v177 = v182 ∧
      aluEval .or v180 v175 = v183 ∧
      aluEval .and v183 v7 = v185 ∧
      aluEval .add v171 v132 = v186 ∧
      aluEval .sltu v186 v132 = v187 ∧
      aluEval .sll v163 0x1D = v188 ∧
      aluEval .mulhu v185 v7 = v189 ∧
      aluEval .add v40 v176 = v193 ∧
      aluEval .sub v188 v173 = v194 ∧
      aluEval .add v193 v182 = v195 ∧
      aluEval .sub v187 v181 = v196 ∧
      aluEval .mul v195 v133 = v199 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n160, v160, d160, hv160, u160⟩ := s.aluG hc ev_at_38c (off' := 0x38E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv160
  obtain ⟨n161, v161, d161, hv161, u161⟩ := u160.aluG hc ev_at_38e (off' := 0x392) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv161
  obtain ⟨n162, v162, d162, hv162, u162⟩ := u161.aluG hc ev_at_392 (off' := 0x394) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv162
  obtain ⟨n163, v163, d163, hv163, u163⟩ := u162.aluImmG hc ev_at_394 (off' := 0x398) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv163
  obtain ⟨n164, v164, d164, hv164, u164⟩ := u163.aluG hc ev_at_398 (off' := 0x39A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv164
  obtain ⟨n165, v165, d165, hv165, u165⟩ := u164.aluG hc ev_at_39a (off' := 0x39E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv165
  obtain ⟨n166, v166, d166, hv166, u166⟩ := u165.aluG hc ev_at_39e (off' := 0x3A2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv166
  obtain ⟨n167, v167, d167, hv167, u167⟩ := u166.aluImmG hc ev_at_3a2 (off' := 0x3A6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv167
  obtain ⟨n168, v168, d168, hv168, u168⟩ := u167.aluG hc ev_at_3a6 (off' := 0x3A8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv168
  obtain ⟨n169, v169, d169, hv169, u169⟩ := u168.aluG hc ev_at_3a8 (off' := 0x3AA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv169
  obtain ⟨n170, d170, u170⟩ := u169.swG hc ev_at_3aa (off' := 0x3AC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 200) (by decide)) (a := F + 0xC8) (v := v163)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm170, hM170⟩ : ∃ M', memStore32 Mi (F + 0xC8) v163 = M' := ⟨_, rfl⟩
  rw [hM170] at u170
  have hc170 : CodeIn Mm170 B ed25519VerifyCode := by rw [← hM170]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr170 : ∀ x, Sep F 0x128 x 1 → Mm170 x = M0 x := fun x hx => by
    rw [← hM170, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n171, v171, d171, hv171, u171⟩ := u170.aluG hc170 ev_at_3ac (off' := 0x3B0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv171
  obtain ⟨n172, v172, d172, hv172, u172⟩ := u171.luiG hc170 ev_at_3b0 (off' := 0x3B4) (by decide)
  obtain ⟨n173, v173, d173, hv173, u173⟩ := u172.aluG hc170 ev_at_3b4 (off' := 0x3B8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv173
  obtain ⟨n174, v174, d174, hv174, u174⟩ := u173.aluImmG hc170 ev_at_3b8 (off' := 0x3BC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv174
  obtain ⟨n175, v175, d175, hv175, u175⟩ := u174.aluImmG hc170 ev_at_3bc (off' := 0x3C0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv175
  obtain ⟨n176, v176, d176, hv176, u176⟩ := u175.aluG hc170 ev_at_3c0 (off' := 0x3C4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv176
  obtain ⟨n177, v177, d177, hv177, u177⟩ := u176.aluImmG hc170 ev_at_3c4 (off' := 0x3C8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv177
  obtain ⟨n178, v178, d178, hv178, u178⟩ := u177.aluImmG hc170 ev_at_3c8 (off' := 0x3CA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv178
  obtain ⟨n179, d179, u179⟩ := u178.lwE hc170 ev_at_3ca (off' := 0x3CE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 268) (by decide)) (v := v31)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x10C) 4 from sep_offsets F (c := 200) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C])
  obtain ⟨n180, v180, d180, hv180, u180⟩ := u179.aluImmG hc170 ev_at_3ce (off' := 0x3D2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv180
  obtain ⟨n181, v181, d181, hv181, u181⟩ := u180.aluG hc170 ev_at_3d2 (off' := 0x3D6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv181
  obtain ⟨n182, v182, d182, hv182, u182⟩ := u181.aluG hc170 ev_at_3d6 (off' := 0x3DA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv182
  obtain ⟨n183, v183, d183, hv183, u183⟩ := u182.aluG hc170 ev_at_3da (off' := 0x3DC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv183
  obtain ⟨n184, d184, u184⟩ := u183.swG hc170 ev_at_3dc (off' := 0x3DE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 132) (by decide)) (a := F + 0x84) (v := v175)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm184, hM184⟩ : ∃ M', memStore32 Mm170 (F + 0x84) v175 = M' := ⟨_, rfl⟩
  rw [hM184] at u184
  have hc184 : CodeIn Mm184 B ed25519VerifyCode := by rw [← hM184]; exact hc170.store32 (frm_sep' sFC (by decide))
  have fr184 : ∀ x, Sep F 0x128 x 1 → Mm184 x = M0 x := fun x hx => by
    rw [← hM184, memStore32_get_sep (frm_sep' hx (by decide)), fr170 x hx]
  obtain ⟨n185, v185, d185, hv185, u185⟩ := u184.aluG hc184 ev_at_3de (off' := 0x3E2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv185
  obtain ⟨n186, v186, d186, hv186, u186⟩ := u185.aluG hc184 ev_at_3e2 (off' := 0x3E4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv186
  obtain ⟨n187, v187, d187, hv187, u187⟩ := u186.aluG hc184 ev_at_3e4 (off' := 0x3E8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv187
  obtain ⟨n188, v188, d188, hv188, u188⟩ := u187.aluImmG hc184 ev_at_3e8 (off' := 0x3EC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv188
  obtain ⟨n189, v189, d189, hv189, u189⟩ := u188.aluG hc184 ev_at_3ec (off' := 0x3F0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv189
  obtain ⟨n190, d190, u190⟩ := u189.swG hc184 ev_at_3f0 (off' := 0x3F2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 164) (by decide)) (a := F + 0xA4) (v := v189)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm190, hM190⟩ : ∃ M', memStore32 Mm184 (F + 0xA4) v189 = M' := ⟨_, rfl⟩
  rw [hM190] at u190
  have hc190 : CodeIn Mm190 B ed25519VerifyCode := by rw [← hM190]; exact hc184.store32 (frm_sep' sFC (by decide))
  have fr190 : ∀ x, Sep F 0x128 x 1 → Mm190 x = M0 x := fun x hx => by
    rw [← hM190, memStore32_get_sep (frm_sep' hx (by decide)), fr184 x hx]
  obtain ⟨n191, d191, u191⟩ := u190.swG hc190 ev_at_3f2 (off' := 0x3F4) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 148) (by decide)) (a := F + 0x94) (v := v185)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm191, hM191⟩ : ∃ M', memStore32 Mm190 (F + 0x94) v185 = M' := ⟨_, rfl⟩
  rw [hM191] at u191
  have hc191 : CodeIn Mm191 B ed25519VerifyCode := by rw [← hM191]; exact hc190.store32 (frm_sep' sFC (by decide))
  have fr191 : ∀ x, Sep F 0x128 x 1 → Mm191 x = M0 x := fun x hx => by
    rw [← hM191, memStore32_get_sep (frm_sep' hx (by decide)), fr190 x hx]
  obtain ⟨n192, d192, u192⟩ := u191.lwE hc191 ev_at_3f4 (off' := 0x3F6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 252) (by decide)) (v := v40)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xFC) 4 from sep_offsets F (c := 148) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0xFC) 4 from sep_offsets F (c := 164) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xFC) 4 from sep_offsets F (c := 132) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xFC) 4 from sep_offsets F (c := 200) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), slFC])
  obtain ⟨n193, v193, d193, hv193, u193⟩ := u192.aluG hc191 ev_at_3f6 (off' := 0x3F8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv193
  obtain ⟨n194, v194, d194, hv194, u194⟩ := u193.aluG hc191 ev_at_3f8 (off' := 0x3FC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv194
  obtain ⟨n195, v195, d195, hv195, u195⟩ := u194.aluG hc191 ev_at_3fc (off' := 0x400) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv195
  obtain ⟨n196, v196, d196, hv196, u196⟩ := u195.aluG hc191 ev_at_400 (off' := 0x404) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv196
  obtain ⟨n197, d197, u197⟩ := u196.aluE hc191 ev_at_404 (off' := 0x406) (by decide) (v := v133)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n198, d198, u198⟩ := u197.swG hc191 ev_at_406 (off' := 0x408) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 224) (by decide)) (a := F + 0xE0) (v := v133)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm198, hM198⟩ : ∃ M', memStore32 Mm191 (F + 0xE0) v133 = M' := ⟨_, rfl⟩
  rw [hM198] at u198
  have hc198 : CodeIn Mm198 B ed25519VerifyCode := by rw [← hM198]; exact hc191.store32 (frm_sep' sFC (by decide))
  have fr198 : ∀ x, Sep F 0x128 x 1 → Mm198 x = M0 x := fun x hx => by
    rw [← hM198, memStore32_get_sep (frm_sep' hx (by decide)), fr191 x hx]
  obtain ⟨n199, v199, d199, hv199, u199⟩ := u198.aluG hc198 ev_at_408 (off' := 0x40C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv199
  have qo1 : reg n199 ra = v195 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n199 sp = F := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n199 (3 : Fin 32) = G3 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n199 (4 : Fin 32) = G4 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n199 (5 : Fin 32) = v186 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n199 (6 : Fin 32) = v87 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n199 (7 : Fin 32) = v159 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n199 (8 : Fin 32) = v133 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n199 (9 : Fin 32) = v175 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n199 a0 = v194 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n199 a1 = v193 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n199 a2 = v185 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n199 a3 = v120 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n199 a4 = v187 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n199 a5 = v199 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n199 a6 = v189 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n199 a7 = v196 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n199 (18 : Fin 32) = v75 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n199 (19 : Fin 32) = v53 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n199 (20 : Fin 32) = v181 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n199 (21 : Fin 32) = v36 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n199 (22 : Fin 32) = v31 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n199 (23 : Fin 32) = v154 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n199 (24 : Fin 32) = v173 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n199 (25 : Fin 32) = v176 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n199 (26 : Fin 32) = v133 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n199 (27 : Fin 32) = v174 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n199 (28 : Fin 32) = v162 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n199 (29 : Fin 32) = v7 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n199 (30 : Fin 32) = v151 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n199 (31 : Fin 32) = v150 := by rw [u199.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mm198 (F + 0xC) = G21 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0xC) 4 from sep_offsets F (c := 224) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xC) 4 from sep_offsets F (c := 148) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0xC) 4 from sep_offsets F (c := 164) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xC) 4 from sep_offsets F (c := 132) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xC) 4 from sep_offsets F (c := 200) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slC]
  have so10 : memLoad32 Mm198 (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x10) 4 from sep_offsets F (c := 224) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x10) 4 from sep_offsets F (c := 148) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0x10) 4 from sep_offsets F (c := 164) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x10) 4 from sep_offsets F (c := 132) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x10) 4 from sep_offsets F (c := 200) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have so84 : memLoad32 Mm198 (F + 0x84) = v175 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x84) 4 from sep_offsets F (c := 224) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x84) 4 from sep_offsets F (c := 148) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0x84) 4 from sep_offsets F (c := 164) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_same]
  have so94 : memLoad32 Mm198 (F + 0x94) = v185 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x94) 4 from sep_offsets F (c := 224) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_same]
  have soA4 : memLoad32 Mm198 (F + 0xA4) = v189 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0xA4) 4 from sep_offsets F (c := 224) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xA4) 4 from sep_offsets F (c := 148) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_same]
  have soB0 : memLoad32 Mm198 (F + 0xB0) = v16 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0xB0) 4 from sep_offsets F (c := 224) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xB0) 4 from sep_offsets F (c := 148) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0xB0) 4 from sep_offsets F (c := 164) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xB0) 4 from sep_offsets F (c := 132) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xB0) 4 from sep_offsets F (c := 200) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), slB0]
  have soB4 : memLoad32 Mm198 (F + 0xB4) = v15 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0xB4) 4 from sep_offsets F (c := 224) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xB4) 4 from sep_offsets F (c := 148) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0xB4) 4 from sep_offsets F (c := 164) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xB4) 4 from sep_offsets F (c := 132) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xB4) 4 from sep_offsets F (c := 200) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), slB4]
  have soB8 : memLoad32 Mm198 (F + 0xB8) = v136 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0xB8) 4 from sep_offsets F (c := 224) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xB8) 4 from sep_offsets F (c := 148) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0xB8) 4 from sep_offsets F (c := 164) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xB8) 4 from sep_offsets F (c := 132) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xB8) 4 from sep_offsets F (c := 200) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), slB8]
  have soBC : memLoad32 Mm198 (F + 0xBC) = v120 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0xBC) 4 from sep_offsets F (c := 224) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xBC) 4 from sep_offsets F (c := 148) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0xBC) 4 from sep_offsets F (c := 164) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xBC) 4 from sep_offsets F (c := 132) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xBC) 4 from sep_offsets F (c := 200) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), slBC]
  have soC0 : memLoad32 Mm198 (F + 0xC0) = v147 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0xC0) 4 from sep_offsets F (c := 224) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xC0) 4 from sep_offsets F (c := 148) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0xC0) 4 from sep_offsets F (c := 164) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xC0) 4 from sep_offsets F (c := 132) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xC0) 4 from sep_offsets F (c := 200) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), slC0]
  have soC8 : memLoad32 Mm198 (F + 0xC8) = v163 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0xC8) 4 from sep_offsets F (c := 224) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xC8) 4 from sep_offsets F (c := 148) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0xC8) 4 from sep_offsets F (c := 164) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xC8) 4 from sep_offsets F (c := 132) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_same]
  have soD0 : memLoad32 Mm198 (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0xD0) 4 from sep_offsets F (c := 224) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xD0) 4 from sep_offsets F (c := 148) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0xD0) 4 from sep_offsets F (c := 164) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xD0) 4 from sep_offsets F (c := 132) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xD0) 4 from sep_offsets F (c := 200) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), slD0]
  have soE0 : memLoad32 Mm198 (F + 0xE0) = v133 := by
    rw [← hM198, memLoad32_store32_same]
  have soE8 : memLoad32 Mm198 (F + 0xE8) = v8 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0xE8) 4 from sep_offsets F (c := 224) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xE8) 4 from sep_offsets F (c := 148) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0xE8) 4 from sep_offsets F (c := 164) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xE8) 4 from sep_offsets F (c := 132) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xE8) 4 from sep_offsets F (c := 200) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), slE8]
  have soEC : memLoad32 Mm198 (F + 0xEC) = v33 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0xEC) 4 from sep_offsets F (c := 224) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xEC) 4 from sep_offsets F (c := 148) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0xEC) 4 from sep_offsets F (c := 164) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xEC) 4 from sep_offsets F (c := 132) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xEC) 4 from sep_offsets F (c := 200) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soFC : memLoad32 Mm198 (F + 0xFC) = v40 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0xFC) 4 from sep_offsets F (c := 224) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xFC) 4 from sep_offsets F (c := 148) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0xFC) 4 from sep_offsets F (c := 164) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xFC) 4 from sep_offsets F (c := 132) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0xFC) 4 from sep_offsets F (c := 200) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), slFC]
  have so100 : memLoad32 Mm198 (F + 0x100) = v51 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x100) 4 from sep_offsets F (c := 224) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x100) 4 from sep_offsets F (c := 148) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0x100) 4 from sep_offsets F (c := 164) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x100) 4 from sep_offsets F (c := 132) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x100) 4 from sep_offsets F (c := 200) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100]
  have so104 : memLoad32 Mm198 (F + 0x104) = v62 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x104) 4 from sep_offsets F (c := 224) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x104) 4 from sep_offsets F (c := 148) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0x104) 4 from sep_offsets F (c := 164) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x104) 4 from sep_offsets F (c := 132) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x104) 4 from sep_offsets F (c := 200) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), sl104]
  have so110 : memLoad32 Mm198 (F + 0x110) = v67 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x110) 4 from sep_offsets F (c := 224) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x110) 4 from sep_offsets F (c := 148) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0x110) 4 from sep_offsets F (c := 164) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x110) 4 from sep_offsets F (c := 132) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x110) 4 from sep_offsets F (c := 200) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so114 : memLoad32 Mm198 (F + 0x114) = v111 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x114) 4 from sep_offsets F (c := 224) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x114) 4 from sep_offsets F (c := 148) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0x114) 4 from sep_offsets F (c := 164) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x114) 4 from sep_offsets F (c := 132) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x114) 4 from sep_offsets F (c := 200) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), sl114]
  have so118 : memLoad32 Mm198 (F + 0x118) = v122 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x118) 4 from sep_offsets F (c := 224) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x118) 4 from sep_offsets F (c := 148) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0x118) 4 from sep_offsets F (c := 164) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x118) 4 from sep_offsets F (c := 132) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x118) 4 from sep_offsets F (c := 200) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), sl118]
  have so120 : memLoad32 Mm198 (F + 0x120) = v116 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x120) 4 from sep_offsets F (c := 224) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x120) 4 from sep_offsets F (c := 148) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0x120) 4 from sep_offsets F (c := 164) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x120) 4 from sep_offsets F (c := 132) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x120) 4 from sep_offsets F (c := 200) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), sl120]
  have so124 : memLoad32 Mm198 (F + 0x124) = v124 := by
    rw [← hM198, memLoad32_store32_sep (show Sep (F + 0xE0) 4 (F + 0x124) 4 from sep_offsets F (c := 224) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM191, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x124) 4 from sep_offsets F (c := 148) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM190, memLoad32_store32_sep (show Sep (F + 0xA4) 4 (F + 0x124) 4 from sep_offsets F (c := 164) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM184, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x124) 4 from sep_offsets F (c := 132) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM170, memLoad32_store32_sep (show Sep (F + 0xC8) 4 (F + 0x124) 4 from sep_offsets F (c := 200) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), sl124]
  exact ⟨n199, Mm198, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v171, v172, v173, v174, v175, v176, v177, v178, v180, v181, v182, v183, v185, v186, v187, v188, v189, v193, v194, v195, v196, v199, (.cons d160 (.cons d161 (.cons d162 (.cons d163 (.cons d164 (.cons d165 (.cons d166 (.cons d167 (.cons d168 (.cons d169 (.cons d170 (.cons d171 (.cons d172 (.cons d173 (.cons d174 (.cons d175 (.cons d176 (.cons d177 (.cons d178 (.cons d179 (.cons d180 (.cons d181 (.cons d182 (.cons d183 (.cons d184 (.cons d185 (.cons d186 (.cons d187 (.cons d188 (.cons d189 (.cons d190 (.cons d191 (.cons d192 (.cons d193 (.cons d194 (.cons d195 (.cons d196 (.cons d197 (.cons d198 (.single d199)))))))))))))))))))))))))))))))))))))))), u199.self, hc198, fr198, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so84, so94, soA4, soB0, soB4, soB8, soBC, soC0, soC8, soD0, soE0, soE8, soEC, soFC, so100, so104, so110, so114, so118, so120, so124, hv160, hv161, hv162, hv163, hv164, hv165, hv166, hv167, hv168, hv169, hv171, hv172, hv173, hv174, hv175, hv176, hv177, hv178, hv180, hv181, hv182, hv183, hv185, hv186, hv187, hv188, hv189, hv193, hv194, hv195, hv196, hv199⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g6 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v8 v15 v16 v31 v33 v36 v40 v51 v53 v62 v67 v75 v87 v111 v116 v120 v122 v124 v133 v136 v147 v150 v151 v154 v159 v162 v163 v173 v174 v175 v176 v181 v185 v186 v187 v189 v193 v194 v195 v196 v199 : Word}
    (s : St Mi B n 0x40C (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v195)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v186)
    (q6 : reg n (6 : Fin 32) = v87)
    (q7 : reg n (7 : Fin 32) = v159)
    (q8 : reg n (8 : Fin 32) = v133)
    (q9 : reg n (9 : Fin 32) = v175)
    (q10 : reg n a0 = v194)
    (q11 : reg n a1 = v193)
    (q12 : reg n a2 = v185)
    (q13 : reg n a3 = v120)
    (q14 : reg n a4 = v187)
    (q15 : reg n a5 = v199)
    (q16 : reg n a6 = v189)
    (q17 : reg n a7 = v196)
    (q18 : reg n (18 : Fin 32) = v75)
    (q19 : reg n (19 : Fin 32) = v53)
    (q20 : reg n (20 : Fin 32) = v181)
    (q21 : reg n (21 : Fin 32) = v36)
    (q22 : reg n (22 : Fin 32) = v31)
    (q23 : reg n (23 : Fin 32) = v154)
    (q24 : reg n (24 : Fin 32) = v173)
    (q25 : reg n (25 : Fin 32) = v176)
    (q26 : reg n (26 : Fin 32) = v133)
    (q27 : reg n (27 : Fin 32) = v174)
    (q28 : reg n (28 : Fin 32) = v162)
    (q29 : reg n (29 : Fin 32) = v7)
    (q30 : reg n (30 : Fin 32) = v151)
    (q31 : reg n (31 : Fin 32) = v150)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (sl84 : memLoad32 Mi (F + 0x84) = v175)
    (sl94 : memLoad32 Mi (F + 0x94) = v185)
    (slA4 : memLoad32 Mi (F + 0xA4) = v189)
    (slB0 : memLoad32 Mi (F + 0xB0) = v16)
    (slB4 : memLoad32 Mi (F + 0xB4) = v15)
    (slB8 : memLoad32 Mi (F + 0xB8) = v136)
    (slBC : memLoad32 Mi (F + 0xBC) = v120)
    (slC0 : memLoad32 Mi (F + 0xC0) = v147)
    (slC8 : memLoad32 Mi (F + 0xC8) = v163)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slE0 : memLoad32 Mi (F + 0xE0) = v133)
    (slE8 : memLoad32 Mi (F + 0xE8) = v8)
    (slEC : memLoad32 Mi (F + 0xEC) = v33)
    (slFC : memLoad32 Mi (F + 0xFC) = v40)
    (sl100 : memLoad32 Mi (F + 0x100) = v51)
    (sl104 : memLoad32 Mi (F + 0x104) = v62)
    (sl110 : memLoad32 Mi (F + 0x110) = v67)
    (sl114 : memLoad32 Mi (F + 0x114) = v111)
    (sl118 : memLoad32 Mi (F + 0x118) = v122)
    (sl120 : memLoad32 Mi (F + 0x120) = v116)
    (sl124 : memLoad32 Mi (F + 0x124) = v124)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v201 v202 v203 v205 v206 v208 v209 v210 v211 v215 v216 v219 v220 v221 v222 v224 v225 v226 v227 v228 v229 v230 v231 : Word),
      Steps n n' ∧
      St M' B n' 0x474 (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v195 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v215 ∧
      reg n' (6 : Fin 32) = v87 ∧
      reg n' (7 : Fin 32) = v159 ∧
      reg n' (8 : Fin 32) = v133 ∧
      reg n' (9 : Fin 32) = v216 ∧
      reg n' a0 = v75 ∧
      reg n' a1 = v230 ∧
      reg n' a2 = v227 ∧
      reg n' a3 = v226 ∧
      reg n' a4 = v231 ∧
      reg n' a5 = v221 ∧
      reg n' a6 = v87 ∧
      reg n' a7 = v220 ∧
      reg n' (18 : Fin 32) = v219 ∧
      reg n' (19 : Fin 32) = v53 ∧
      reg n' (20 : Fin 32) = v211 ∧
      reg n' (21 : Fin 32) = v36 ∧
      reg n' (22 : Fin 32) = v31 ∧
      reg n' (23 : Fin 32) = v222 ∧
      reg n' (24 : Fin 32) = v173 ∧
      reg n' (25 : Fin 32) = v176 ∧
      reg n' (26 : Fin 32) = v209 ∧
      reg n' (27 : Fin 32) = v174 ∧
      reg n' (28 : Fin 32) = v162 ∧
      reg n' (29 : Fin 32) = v7 ∧
      reg n' (30 : Fin 32) = v151 ∧
      reg n' (31 : Fin 32) = v150 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0x84) = v175 ∧
      memLoad32 M' (F + 0x88) = v36 ∧
      memLoad32 M' (F + 0x94) = v185 ∧
      memLoad32 M' (F + 0x9C) = v75 ∧
      memLoad32 M' (F + 0xA0) = v87 ∧
      memLoad32 M' (F + 0xA4) = v189 ∧
      memLoad32 M' (F + 0xB0) = v16 ∧
      memLoad32 M' (F + 0xB4) = v15 ∧
      memLoad32 M' (F + 0xB8) = v136 ∧
      memLoad32 M' (F + 0xBC) = v120 ∧
      memLoad32 M' (F + 0xC0) = v147 ∧
      memLoad32 M' (F + 0xC4) = v199 ∧
      memLoad32 M' (F + 0xC8) = v163 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xE0) = v133 ∧
      memLoad32 M' (F + 0xE8) = v8 ∧
      memLoad32 M' (F + 0xEC) = v33 ∧
      memLoad32 M' (F + 0xF0) = v206 ∧
      memLoad32 M' (F + 0xFC) = v40 ∧
      memLoad32 M' (F + 0x100) = v51 ∧
      memLoad32 M' (F + 0x104) = v62 ∧
      memLoad32 M' (F + 0x108) = v203 ∧
      memLoad32 M' (F + 0x110) = v67 ∧
      memLoad32 M' (F + 0x114) = v111 ∧
      memLoad32 M' (F + 0x118) = v122 ∧
      memLoad32 M' (F + 0x120) = v116 ∧
      memLoad32 M' (F + 0x124) = v124 ∧
      aluEval .add v196 v154 = v201 ∧
      aluEval .sltu v186 v194 = v202 ∧
      aluEval .sub v201 v202 = v203 ∧
      aluEval .mulhu v151 v174 = v205 ∧
      aluEval .sub v186 v194 = v206 ∧
      aluEval .sll v175 0x1D = v208 ∧
      aluEval .sub v208 v185 = v209 ∧
      aluEval .add v189 v181 = v210 ∧
      aluEval .add v209 v194 = v211 ∧
      aluEval .mulhu v36 v75 = v215 ∧
      aluEval .mulhu v87 v53 = v216 ∧
      aluEval .and v199 v7 = v219 ∧
      aluEval .sltu v211 v209 = v220 ∧
      aluEval .mulhu v219 v150 = v221 ∧
      aluEval .add v210 v220 = v222 ∧
      aluEval .add v205 v51 = v224 ∧
      aluEval .sltu v193 v176 = v225 ∧
      aluEval .mul v219 v150 = v226 ∧
      aluEval .add v225 v224 = v227 ∧
      aluEval .sltu v159 v211 = v228 ∧
      aluEval .add v228 v222 = v229 ∧
      aluEval .sltu v195 v193 = v230 ∧
      aluEval .sub v162 v229 = v231 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n200, d200, u200⟩ := s.swG hc ev_at_40c (off' := 0x40E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 196) (by decide)) (a := F + 0xC4) (v := v199)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm200, hM200⟩ : ∃ M', memStore32 Mi (F + 0xC4) v199 = M' := ⟨_, rfl⟩
  rw [hM200] at u200
  have hc200 : CodeIn Mm200 B ed25519VerifyCode := by rw [← hM200]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr200 : ∀ x, Sep F 0x128 x 1 → Mm200 x = M0 x := fun x hx => by
    rw [← hM200, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n201, v201, d201, hv201, u201⟩ := u200.aluG hc200 ev_at_40e (off' := 0x410) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv201
  obtain ⟨n202, v202, d202, hv202, u202⟩ := u201.aluG hc200 ev_at_410 (off' := 0x414) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv202
  obtain ⟨n203, v203, d203, hv203, u203⟩ := u202.aluG hc200 ev_at_414 (off' := 0x418) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv203
  obtain ⟨n204, d204, u204⟩ := u203.swG hc200 ev_at_418 (off' := 0x41C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 264) (by decide)) (a := F + 0x108) (v := v203)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm204, hM204⟩ : ∃ M', memStore32 Mm200 (F + 0x108) v203 = M' := ⟨_, rfl⟩
  rw [hM204] at u204
  have hc204 : CodeIn Mm204 B ed25519VerifyCode := by rw [← hM204]; exact hc200.store32 (frm_sep' sFC (by decide))
  have fr204 : ∀ x, Sep F 0x128 x 1 → Mm204 x = M0 x := fun x hx => by
    rw [← hM204, memStore32_get_sep (frm_sep' hx (by decide)), fr200 x hx]
  obtain ⟨n205, v205, d205, hv205, u205⟩ := u204.aluG hc204 ev_at_41c (off' := 0x420) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv205
  obtain ⟨n206, v206, d206, hv206, u206⟩ := u205.aluG hc204 ev_at_420 (off' := 0x424) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv206
  obtain ⟨n207, d207, u207⟩ := u206.swG hc204 ev_at_424 (off' := 0x426) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 240) (by decide)) (a := F + 0xF0) (v := v206)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm207, hM207⟩ : ∃ M', memStore32 Mm204 (F + 0xF0) v206 = M' := ⟨_, rfl⟩
  rw [hM207] at u207
  have hc207 : CodeIn Mm207 B ed25519VerifyCode := by rw [← hM207]; exact hc204.store32 (frm_sep' sFC (by decide))
  have fr207 : ∀ x, Sep F 0x128 x 1 → Mm207 x = M0 x := fun x hx => by
    rw [← hM207, memStore32_get_sep (frm_sep' hx (by decide)), fr204 x hx]
  obtain ⟨n208, v208, d208, hv208, u208⟩ := u207.aluImmG hc207 ev_at_426 (off' := 0x428) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv208
  obtain ⟨n209, v209, d209, hv209, u209⟩ := u208.aluG hc207 ev_at_428 (off' := 0x42C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv209
  obtain ⟨n210, v210, d210, hv210, u210⟩ := u209.aluG hc207 ev_at_42c (off' := 0x430) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv210
  obtain ⟨n211, v211, d211, hv211, u211⟩ := u210.aluG hc207 ev_at_430 (off' := 0x434) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv211
  obtain ⟨n212, d212, u212⟩ := u211.aluE hc207 ev_at_434 (off' := 0x436) (by decide) (v := v75)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n213, d213, u213⟩ := u212.swG hc207 ev_at_436 (off' := 0x438) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 156) (by decide)) (a := F + 0x9C) (v := v75)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm213, hM213⟩ : ∃ M', memStore32 Mm207 (F + 0x9C) v75 = M' := ⟨_, rfl⟩
  rw [hM213] at u213
  have hc213 : CodeIn Mm213 B ed25519VerifyCode := by rw [← hM213]; exact hc207.store32 (frm_sep' sFC (by decide))
  have fr213 : ∀ x, Sep F 0x128 x 1 → Mm213 x = M0 x := fun x hx => by
    rw [← hM213, memStore32_get_sep (frm_sep' hx (by decide)), fr207 x hx]
  obtain ⟨n214, d214, u214⟩ := u213.swG hc213 ev_at_438 (off' := 0x43A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 136) (by decide)) (a := F + 0x88) (v := v36)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm214, hM214⟩ : ∃ M', memStore32 Mm213 (F + 0x88) v36 = M' := ⟨_, rfl⟩
  rw [hM214] at u214
  have hc214 : CodeIn Mm214 B ed25519VerifyCode := by rw [← hM214]; exact hc213.store32 (frm_sep' sFC (by decide))
  have fr214 : ∀ x, Sep F 0x128 x 1 → Mm214 x = M0 x := fun x hx => by
    rw [← hM214, memStore32_get_sep (frm_sep' hx (by decide)), fr213 x hx]
  obtain ⟨n215, v215, d215, hv215, u215⟩ := u214.aluG hc214 ev_at_43a (off' := 0x43E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv215
  obtain ⟨n216, v216, d216, hv216, u216⟩ := u215.aluG hc214 ev_at_43e (off' := 0x442) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv216
  obtain ⟨n217, d217, u217⟩ := u216.aluE hc214 ev_at_442 (off' := 0x444) (by decide) (v := v87)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n218, d218, u218⟩ := u217.swG hc214 ev_at_444 (off' := 0x446) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 160) (by decide)) (a := F + 0xA0) (v := v87)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm218, hM218⟩ : ∃ M', memStore32 Mm214 (F + 0xA0) v87 = M' := ⟨_, rfl⟩
  rw [hM218] at u218
  have hc218 : CodeIn Mm218 B ed25519VerifyCode := by rw [← hM218]; exact hc214.store32 (frm_sep' sFC (by decide))
  have fr218 : ∀ x, Sep F 0x128 x 1 → Mm218 x = M0 x := fun x hx => by
    rw [← hM218, memStore32_get_sep (frm_sep' hx (by decide)), fr214 x hx]
  obtain ⟨n219, v219, d219, hv219, u219⟩ := u218.aluG hc218 ev_at_446 (off' := 0x44A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv219
  obtain ⟨n220, v220, d220, hv220, u220⟩ := u219.aluG hc218 ev_at_44a (off' := 0x44E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv220
  obtain ⟨n221, v221, d221, hv221, u221⟩ := u220.aluG hc218 ev_at_44e (off' := 0x452) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv221
  obtain ⟨n222, v222, d222, hv222, u222⟩ := u221.aluG hc218 ev_at_452 (off' := 0x456) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv222
  obtain ⟨n223, d223, u223⟩ := u222.lwE hc218 ev_at_456 (off' := 0x45A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 256) (by decide)) (v := v51)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0x100) 4 from sep_offsets F (c := 160) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x100) 4 from sep_offsets F (c := 136) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x100) 4 from sep_offsets F (c := 156) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x100) 4 from sep_offsets F (c := 240) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x100) 4 from sep_offsets F (c := 264) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0x100) 4 from sep_offsets F (c := 196) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100])
  obtain ⟨n224, v224, d224, hv224, u224⟩ := u223.aluG hc218 ev_at_45a (off' := 0x45C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv224
  obtain ⟨n225, v225, d225, hv225, u225⟩ := u224.aluG hc218 ev_at_45c (off' := 0x460) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv225
  obtain ⟨n226, v226, d226, hv226, u226⟩ := u225.aluG hc218 ev_at_460 (off' := 0x464) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv226
  obtain ⟨n227, v227, d227, hv227, u227⟩ := u226.aluG hc218 ev_at_464 (off' := 0x466) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv227
  obtain ⟨n228, v228, d228, hv228, u228⟩ := u227.aluG hc218 ev_at_466 (off' := 0x46A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv228
  obtain ⟨n229, v229, d229, hv229, u229⟩ := u228.aluG hc218 ev_at_46a (off' := 0x46C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv229
  obtain ⟨n230, v230, d230, hv230, u230⟩ := u229.aluG hc218 ev_at_46c (off' := 0x470) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv230
  obtain ⟨n231, v231, d231, hv231, u231⟩ := u230.aluG hc218 ev_at_470 (off' := 0x474) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv231
  have qo1 : reg n231 ra = v195 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n231 sp = F := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n231 (3 : Fin 32) = G3 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n231 (4 : Fin 32) = G4 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n231 (5 : Fin 32) = v215 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n231 (6 : Fin 32) = v87 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n231 (7 : Fin 32) = v159 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n231 (8 : Fin 32) = v133 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n231 (9 : Fin 32) = v216 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n231 a0 = v75 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n231 a1 = v230 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n231 a2 = v227 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n231 a3 = v226 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n231 a4 = v231 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n231 a5 = v221 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n231 a6 = v87 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n231 a7 = v220 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n231 (18 : Fin 32) = v219 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n231 (19 : Fin 32) = v53 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n231 (20 : Fin 32) = v211 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n231 (21 : Fin 32) = v36 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n231 (22 : Fin 32) = v31 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n231 (23 : Fin 32) = v222 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n231 (24 : Fin 32) = v173 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n231 (25 : Fin 32) = v176 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n231 (26 : Fin 32) = v209 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n231 (27 : Fin 32) = v174 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n231 (28 : Fin 32) = v162 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n231 (29 : Fin 32) = v7 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n231 (30 : Fin 32) = v151 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n231 (31 : Fin 32) = v150 := by rw [u231.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mm218 (F + 0xC) = G21 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0xC) 4 from sep_offsets F (c := 160) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xC) 4 from sep_offsets F (c := 136) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xC) 4 from sep_offsets F (c := 156) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xC) 4 from sep_offsets F (c := 240) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0xC) 4 from sep_offsets F (c := 264) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0xC) 4 from sep_offsets F (c := 196) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slC]
  have so10 : memLoad32 Mm218 (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0x10) 4 from sep_offsets F (c := 160) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x10) 4 from sep_offsets F (c := 136) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x10) 4 from sep_offsets F (c := 156) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x10) 4 from sep_offsets F (c := 240) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x10) 4 from sep_offsets F (c := 264) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0x10) 4 from sep_offsets F (c := 196) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have so84 : memLoad32 Mm218 (F + 0x84) = v175 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0x84) 4 from sep_offsets F (c := 160) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x84) 4 from sep_offsets F (c := 136) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x84) 4 from sep_offsets F (c := 156) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x84) 4 from sep_offsets F (c := 240) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x84) 4 from sep_offsets F (c := 264) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0x84) 4 from sep_offsets F (c := 196) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), sl84]
  have so88 : memLoad32 Mm218 (F + 0x88) = v36 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0x88) 4 from sep_offsets F (c := 160) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_same]
  have so94 : memLoad32 Mm218 (F + 0x94) = v185 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0x94) 4 from sep_offsets F (c := 160) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x94) 4 from sep_offsets F (c := 136) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x94) 4 from sep_offsets F (c := 156) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x94) 4 from sep_offsets F (c := 240) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x94) 4 from sep_offsets F (c := 264) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0x94) 4 from sep_offsets F (c := 196) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), sl94]
  have so9C : memLoad32 Mm218 (F + 0x9C) = v75 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0x9C) 4 from sep_offsets F (c := 160) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x9C) 4 from sep_offsets F (c := 136) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_same]
  have soA0 : memLoad32 Mm218 (F + 0xA0) = v87 := by
    rw [← hM218, memLoad32_store32_same]
  have soA4 : memLoad32 Mm218 (F + 0xA4) = v189 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0xA4) 4 from sep_offsets F (c := 160) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xA4) 4 from sep_offsets F (c := 136) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xA4) 4 from sep_offsets F (c := 156) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xA4) 4 from sep_offsets F (c := 240) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0xA4) 4 from sep_offsets F (c := 264) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0xA4) 4 from sep_offsets F (c := 196) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), slA4]
  have soB0 : memLoad32 Mm218 (F + 0xB0) = v16 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0xB0) 4 from sep_offsets F (c := 160) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xB0) 4 from sep_offsets F (c := 136) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xB0) 4 from sep_offsets F (c := 156) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xB0) 4 from sep_offsets F (c := 240) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0xB0) 4 from sep_offsets F (c := 264) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0xB0) 4 from sep_offsets F (c := 196) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), slB0]
  have soB4 : memLoad32 Mm218 (F + 0xB4) = v15 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0xB4) 4 from sep_offsets F (c := 160) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xB4) 4 from sep_offsets F (c := 136) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xB4) 4 from sep_offsets F (c := 156) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xB4) 4 from sep_offsets F (c := 240) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0xB4) 4 from sep_offsets F (c := 264) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0xB4) 4 from sep_offsets F (c := 196) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), slB4]
  have soB8 : memLoad32 Mm218 (F + 0xB8) = v136 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0xB8) 4 from sep_offsets F (c := 160) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xB8) 4 from sep_offsets F (c := 136) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xB8) 4 from sep_offsets F (c := 156) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xB8) 4 from sep_offsets F (c := 240) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0xB8) 4 from sep_offsets F (c := 264) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0xB8) 4 from sep_offsets F (c := 196) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), slB8]
  have soBC : memLoad32 Mm218 (F + 0xBC) = v120 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0xBC) 4 from sep_offsets F (c := 160) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xBC) 4 from sep_offsets F (c := 136) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xBC) 4 from sep_offsets F (c := 156) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xBC) 4 from sep_offsets F (c := 240) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0xBC) 4 from sep_offsets F (c := 264) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0xBC) 4 from sep_offsets F (c := 196) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), slBC]
  have soC0 : memLoad32 Mm218 (F + 0xC0) = v147 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0xC0) 4 from sep_offsets F (c := 160) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xC0) 4 from sep_offsets F (c := 136) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xC0) 4 from sep_offsets F (c := 156) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xC0) 4 from sep_offsets F (c := 240) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0xC0) 4 from sep_offsets F (c := 264) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0xC0) 4 from sep_offsets F (c := 196) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), slC0]
  have soC4 : memLoad32 Mm218 (F + 0xC4) = v199 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0xC4) 4 from sep_offsets F (c := 160) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xC4) 4 from sep_offsets F (c := 136) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xC4) 4 from sep_offsets F (c := 156) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xC4) 4 from sep_offsets F (c := 240) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0xC4) 4 from sep_offsets F (c := 264) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_same]
  have soC8 : memLoad32 Mm218 (F + 0xC8) = v163 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0xC8) 4 from sep_offsets F (c := 160) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xC8) 4 from sep_offsets F (c := 136) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xC8) 4 from sep_offsets F (c := 156) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xC8) 4 from sep_offsets F (c := 240) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0xC8) 4 from sep_offsets F (c := 264) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0xC8) 4 from sep_offsets F (c := 196) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), slC8]
  have soD0 : memLoad32 Mm218 (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0xD0) 4 from sep_offsets F (c := 160) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xD0) 4 from sep_offsets F (c := 136) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xD0) 4 from sep_offsets F (c := 156) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xD0) 4 from sep_offsets F (c := 240) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0xD0) 4 from sep_offsets F (c := 264) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0xD0) 4 from sep_offsets F (c := 196) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), slD0]
  have soE0 : memLoad32 Mm218 (F + 0xE0) = v133 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0xE0) 4 from sep_offsets F (c := 160) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xE0) 4 from sep_offsets F (c := 136) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xE0) 4 from sep_offsets F (c := 156) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xE0) 4 from sep_offsets F (c := 240) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0xE0) 4 from sep_offsets F (c := 264) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0xE0) 4 from sep_offsets F (c := 196) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), slE0]
  have soE8 : memLoad32 Mm218 (F + 0xE8) = v8 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0xE8) 4 from sep_offsets F (c := 160) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xE8) 4 from sep_offsets F (c := 136) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xE8) 4 from sep_offsets F (c := 156) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xE8) 4 from sep_offsets F (c := 240) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0xE8) 4 from sep_offsets F (c := 264) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0xE8) 4 from sep_offsets F (c := 196) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), slE8]
  have soEC : memLoad32 Mm218 (F + 0xEC) = v33 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0xEC) 4 from sep_offsets F (c := 160) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xEC) 4 from sep_offsets F (c := 136) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xEC) 4 from sep_offsets F (c := 156) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xEC) 4 from sep_offsets F (c := 240) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0xEC) 4 from sep_offsets F (c := 264) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0xEC) 4 from sep_offsets F (c := 196) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soF0 : memLoad32 Mm218 (F + 0xF0) = v206 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0xF0) 4 from sep_offsets F (c := 160) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xF0) 4 from sep_offsets F (c := 136) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xF0) 4 from sep_offsets F (c := 156) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_same]
  have soFC : memLoad32 Mm218 (F + 0xFC) = v40 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0xFC) 4 from sep_offsets F (c := 160) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0xFC) 4 from sep_offsets F (c := 136) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0xFC) 4 from sep_offsets F (c := 156) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0xFC) 4 from sep_offsets F (c := 240) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0xFC) 4 from sep_offsets F (c := 264) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0xFC) 4 from sep_offsets F (c := 196) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), slFC]
  have so100 : memLoad32 Mm218 (F + 0x100) = v51 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0x100) 4 from sep_offsets F (c := 160) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x100) 4 from sep_offsets F (c := 136) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x100) 4 from sep_offsets F (c := 156) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x100) 4 from sep_offsets F (c := 240) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x100) 4 from sep_offsets F (c := 264) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0x100) 4 from sep_offsets F (c := 196) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100]
  have so104 : memLoad32 Mm218 (F + 0x104) = v62 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0x104) 4 from sep_offsets F (c := 160) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x104) 4 from sep_offsets F (c := 136) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x104) 4 from sep_offsets F (c := 156) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x104) 4 from sep_offsets F (c := 240) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x104) 4 from sep_offsets F (c := 264) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0x104) 4 from sep_offsets F (c := 196) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), sl104]
  have so108 : memLoad32 Mm218 (F + 0x108) = v203 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0x108) 4 from sep_offsets F (c := 160) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x108) 4 from sep_offsets F (c := 136) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x108) 4 from sep_offsets F (c := 156) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x108) 4 from sep_offsets F (c := 240) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_same]
  have so110 : memLoad32 Mm218 (F + 0x110) = v67 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0x110) 4 from sep_offsets F (c := 160) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x110) 4 from sep_offsets F (c := 136) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x110) 4 from sep_offsets F (c := 156) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x110) 4 from sep_offsets F (c := 240) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x110) 4 from sep_offsets F (c := 264) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0x110) 4 from sep_offsets F (c := 196) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so114 : memLoad32 Mm218 (F + 0x114) = v111 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0x114) 4 from sep_offsets F (c := 160) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x114) 4 from sep_offsets F (c := 136) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x114) 4 from sep_offsets F (c := 156) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x114) 4 from sep_offsets F (c := 240) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x114) 4 from sep_offsets F (c := 264) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0x114) 4 from sep_offsets F (c := 196) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), sl114]
  have so118 : memLoad32 Mm218 (F + 0x118) = v122 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0x118) 4 from sep_offsets F (c := 160) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x118) 4 from sep_offsets F (c := 136) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x118) 4 from sep_offsets F (c := 156) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x118) 4 from sep_offsets F (c := 240) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x118) 4 from sep_offsets F (c := 264) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0x118) 4 from sep_offsets F (c := 196) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), sl118]
  have so120 : memLoad32 Mm218 (F + 0x120) = v116 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0x120) 4 from sep_offsets F (c := 160) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x120) 4 from sep_offsets F (c := 136) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x120) 4 from sep_offsets F (c := 156) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x120) 4 from sep_offsets F (c := 240) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x120) 4 from sep_offsets F (c := 264) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0x120) 4 from sep_offsets F (c := 196) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), sl120]
  have so124 : memLoad32 Mm218 (F + 0x124) = v124 := by
    rw [← hM218, memLoad32_store32_sep (show Sep (F + 0xA0) 4 (F + 0x124) 4 from sep_offsets F (c := 160) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM214, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x124) 4 from sep_offsets F (c := 136) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM213, memLoad32_store32_sep (show Sep (F + 0x9C) 4 (F + 0x124) 4 from sep_offsets F (c := 156) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM207, memLoad32_store32_sep (show Sep (F + 0xF0) 4 (F + 0x124) 4 from sep_offsets F (c := 240) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM204, memLoad32_store32_sep (show Sep (F + 0x108) 4 (F + 0x124) 4 from sep_offsets F (c := 264) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM200, memLoad32_store32_sep (show Sep (F + 0xC4) 4 (F + 0x124) 4 from sep_offsets F (c := 196) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), sl124]
  exact ⟨n231, Mm218, v201, v202, v203, v205, v206, v208, v209, v210, v211, v215, v216, v219, v220, v221, v222, v224, v225, v226, v227, v228, v229, v230, v231, (.cons d200 (.cons d201 (.cons d202 (.cons d203 (.cons d204 (.cons d205 (.cons d206 (.cons d207 (.cons d208 (.cons d209 (.cons d210 (.cons d211 (.cons d212 (.cons d213 (.cons d214 (.cons d215 (.cons d216 (.cons d217 (.cons d218 (.cons d219 (.cons d220 (.cons d221 (.cons d222 (.cons d223 (.cons d224 (.cons d225 (.cons d226 (.cons d227 (.cons d228 (.cons d229 (.cons d230 (.single d231)))))))))))))))))))))))))))))))), u231.self, hc218, fr218, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so84, so88, so94, so9C, soA0, soA4, soB0, soB4, soB8, soBC, soC0, soC4, soC8, soD0, soE0, soE8, soEC, soF0, soFC, so100, so104, so108, so110, so114, so118, so120, so124, hv201, hv202, hv203, hv205, hv206, hv208, hv209, hv210, hv211, hv215, hv216, hv219, hv220, hv221, hv222, hv224, hv225, hv226, hv227, hv228, hv229, hv230, hv231⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g7 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v8 v15 v16 v31 v33 v36 v40 v51 v53 v62 v67 v75 v87 v111 v116 v120 v122 v124 v133 v136 v147 v150 v151 v159 v162 v163 v173 v174 v175 v176 v185 v189 v195 v199 v203 v206 v209 v211 v215 v216 v219 v220 v221 v222 v226 v227 v230 v231 : Word}
    (s : St Mi B n 0x474 (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v195)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v215)
    (q6 : reg n (6 : Fin 32) = v87)
    (q7 : reg n (7 : Fin 32) = v159)
    (q8 : reg n (8 : Fin 32) = v133)
    (q9 : reg n (9 : Fin 32) = v216)
    (q10 : reg n a0 = v75)
    (q11 : reg n a1 = v230)
    (q12 : reg n a2 = v227)
    (q13 : reg n a3 = v226)
    (q14 : reg n a4 = v231)
    (q15 : reg n a5 = v221)
    (q16 : reg n a6 = v87)
    (q17 : reg n a7 = v220)
    (q18 : reg n (18 : Fin 32) = v219)
    (q19 : reg n (19 : Fin 32) = v53)
    (q20 : reg n (20 : Fin 32) = v211)
    (q21 : reg n (21 : Fin 32) = v36)
    (q22 : reg n (22 : Fin 32) = v31)
    (q23 : reg n (23 : Fin 32) = v222)
    (q24 : reg n (24 : Fin 32) = v173)
    (q25 : reg n (25 : Fin 32) = v176)
    (q26 : reg n (26 : Fin 32) = v209)
    (q27 : reg n (27 : Fin 32) = v174)
    (q28 : reg n (28 : Fin 32) = v162)
    (q29 : reg n (29 : Fin 32) = v7)
    (q30 : reg n (30 : Fin 32) = v151)
    (q31 : reg n (31 : Fin 32) = v150)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (sl84 : memLoad32 Mi (F + 0x84) = v175)
    (sl88 : memLoad32 Mi (F + 0x88) = v36)
    (sl94 : memLoad32 Mi (F + 0x94) = v185)
    (sl9C : memLoad32 Mi (F + 0x9C) = v75)
    (slA0 : memLoad32 Mi (F + 0xA0) = v87)
    (slA4 : memLoad32 Mi (F + 0xA4) = v189)
    (slB0 : memLoad32 Mi (F + 0xB0) = v16)
    (slB4 : memLoad32 Mi (F + 0xB4) = v15)
    (slB8 : memLoad32 Mi (F + 0xB8) = v136)
    (slBC : memLoad32 Mi (F + 0xBC) = v120)
    (slC0 : memLoad32 Mi (F + 0xC0) = v147)
    (slC4 : memLoad32 Mi (F + 0xC4) = v199)
    (slC8 : memLoad32 Mi (F + 0xC8) = v163)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slE0 : memLoad32 Mi (F + 0xE0) = v133)
    (slE8 : memLoad32 Mi (F + 0xE8) = v8)
    (slEC : memLoad32 Mi (F + 0xEC) = v33)
    (slF0 : memLoad32 Mi (F + 0xF0) = v206)
    (slFC : memLoad32 Mi (F + 0xFC) = v40)
    (sl100 : memLoad32 Mi (F + 0x100) = v51)
    (sl104 : memLoad32 Mi (F + 0x104) = v62)
    (sl108 : memLoad32 Mi (F + 0x108) = v203)
    (sl110 : memLoad32 Mi (F + 0x110) = v67)
    (sl114 : memLoad32 Mi (F + 0x114) = v111)
    (sl118 : memLoad32 Mi (F + 0x118) = v122)
    (sl120 : memLoad32 Mi (F + 0x120) = v116)
    (sl124 : memLoad32 Mi (F + 0x124) = v124)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v233 v234 v235 v236 v237 v238 v239 : Word),
      Steps n n' ∧
      St M' B n' 0x48E (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v238 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v215 ∧
      reg n' (6 : Fin 32) = v235 ∧
      reg n' (7 : Fin 32) = v159 ∧
      reg n' (8 : Fin 32) = v133 ∧
      reg n' (9 : Fin 32) = v234 ∧
      reg n' a0 = v75 ∧
      reg n' a1 = v237 ∧
      reg n' a2 = v227 ∧
      reg n' a3 = v226 ∧
      reg n' a4 = v236 ∧
      reg n' a5 = v221 ∧
      reg n' a6 = v87 ∧
      reg n' a7 = v220 ∧
      reg n' (18 : Fin 32) = v219 ∧
      reg n' (19 : Fin 32) = v53 ∧
      reg n' (20 : Fin 32) = v211 ∧
      reg n' (21 : Fin 32) = v36 ∧
      reg n' (22 : Fin 32) = v31 ∧
      reg n' (23 : Fin 32) = v222 ∧
      reg n' (24 : Fin 32) = v173 ∧
      reg n' (25 : Fin 32) = v239 ∧
      reg n' (26 : Fin 32) = v209 ∧
      reg n' (27 : Fin 32) = v174 ∧
      reg n' (28 : Fin 32) = v162 ∧
      reg n' (29 : Fin 32) = v7 ∧
      reg n' (30 : Fin 32) = v151 ∧
      reg n' (31 : Fin 32) = v150 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0x84) = v175 ∧
      memLoad32 M' (F + 0x88) = v36 ∧
      memLoad32 M' (F + 0x94) = v185 ∧
      memLoad32 M' (F + 0x9C) = v75 ∧
      memLoad32 M' (F + 0xA0) = v87 ∧
      memLoad32 M' (F + 0xA4) = v189 ∧
      memLoad32 M' (F + 0xB0) = v16 ∧
      memLoad32 M' (F + 0xB4) = v15 ∧
      memLoad32 M' (F + 0xB8) = v136 ∧
      memLoad32 M' (F + 0xBC) = v120 ∧
      memLoad32 M' (F + 0xC0) = v147 ∧
      memLoad32 M' (F + 0xC4) = v199 ∧
      memLoad32 M' (F + 0xC8) = v163 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xE0) = v133 ∧
      memLoad32 M' (F + 0xE8) = v8 ∧
      memLoad32 M' (F + 0xEC) = v33 ∧
      memLoad32 M' (F + 0xF0) = v206 ∧
      memLoad32 M' (F + 0xFC) = v40 ∧
      memLoad32 M' (F + 0x100) = v51 ∧
      memLoad32 M' (F + 0x104) = v62 ∧
      memLoad32 M' (F + 0x108) = v203 ∧
      memLoad32 M' (F + 0x110) = v67 ∧
      memLoad32 M' (F + 0x114) = v111 ∧
      memLoad32 M' (F + 0x118) = v122 ∧
      memLoad32 M' (F + 0x11C) = v231 ∧
      memLoad32 M' (F + 0x120) = v116 ∧
      memLoad32 M' (F + 0x124) = v124 ∧
      aluEval .add v230 v227 = v233 ∧
      aluEval .add v216 v215 = v234 ∧
      aluEval .add v221 v233 = v235 ∧
      aluEval .srl v31 0xB = v236 ∧
      (0x1DE73000 : Word) = v237 ∧
      aluEval .add v195 v226 = v238 ∧
      aluEval .add v237 0x596 = v239 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n232, d232, u232⟩ := s.swG hc ev_at_474 (off' := 0x478) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 284) (by decide)) (a := F + 0x11C) (v := v231)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm232, hM232⟩ : ∃ M', memStore32 Mi (F + 0x11C) v231 = M' := ⟨_, rfl⟩
  rw [hM232] at u232
  have hc232 : CodeIn Mm232 B ed25519VerifyCode := by rw [← hM232]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr232 : ∀ x, Sep F 0x128 x 1 → Mm232 x = M0 x := fun x hx => by
    rw [← hM232, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n233, v233, d233, hv233, u233⟩ := u232.aluG hc232 ev_at_478 (off' := 0x47A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv233
  obtain ⟨n234, v234, d234, hv234, u234⟩ := u233.aluG hc232 ev_at_47a (off' := 0x47C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv234
  obtain ⟨n235, v235, d235, hv235, u235⟩ := u234.aluG hc232 ev_at_47c (off' := 0x480) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv235
  obtain ⟨n236, v236, d236, hv236, u236⟩ := u235.aluImmG hc232 ev_at_480 (off' := 0x484) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv236
  obtain ⟨n237, v237, d237, hv237, u237⟩ := u236.luiG hc232 ev_at_484 (off' := 0x488) (by decide)
  obtain ⟨n238, v238, d238, hv238, u238⟩ := u237.aluG hc232 ev_at_488 (off' := 0x48A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv238
  obtain ⟨n239, v239, d239, hv239, u239⟩ := u238.aluImmG hc232 ev_at_48a (off' := 0x48E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv239
  have qo1 : reg n239 ra = v238 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n239 sp = F := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n239 (3 : Fin 32) = G3 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n239 (4 : Fin 32) = G4 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n239 (5 : Fin 32) = v215 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n239 (6 : Fin 32) = v235 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n239 (7 : Fin 32) = v159 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n239 (8 : Fin 32) = v133 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n239 (9 : Fin 32) = v234 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n239 a0 = v75 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n239 a1 = v237 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n239 a2 = v227 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n239 a3 = v226 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n239 a4 = v236 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n239 a5 = v221 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n239 a6 = v87 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n239 a7 = v220 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n239 (18 : Fin 32) = v219 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n239 (19 : Fin 32) = v53 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n239 (20 : Fin 32) = v211 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n239 (21 : Fin 32) = v36 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n239 (22 : Fin 32) = v31 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n239 (23 : Fin 32) = v222 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n239 (24 : Fin 32) = v173 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n239 (25 : Fin 32) = v239 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n239 (26 : Fin 32) = v209 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n239 (27 : Fin 32) = v174 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n239 (28 : Fin 32) = v162 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n239 (29 : Fin 32) = v7 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n239 (30 : Fin 32) = v151 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n239 (31 : Fin 32) = v150 := by rw [u239.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mm232 (F + 0xC) = G21 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xC) 4 from sep_offsets F (c := 284) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slC]
  have so10 : memLoad32 Mm232 (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x10) 4 from sep_offsets F (c := 284) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have so84 : memLoad32 Mm232 (F + 0x84) = v175 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x84) 4 from sep_offsets F (c := 284) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), sl84]
  have so88 : memLoad32 Mm232 (F + 0x88) = v36 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x88) 4 from sep_offsets F (c := 284) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88]
  have so94 : memLoad32 Mm232 (F + 0x94) = v185 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x94) 4 from sep_offsets F (c := 284) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), sl94]
  have so9C : memLoad32 Mm232 (F + 0x9C) = v75 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x9C) 4 from sep_offsets F (c := 284) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), sl9C]
  have soA0 : memLoad32 Mm232 (F + 0xA0) = v87 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xA0) 4 from sep_offsets F (c := 284) (n := 4) (d := 160) (k := 4) (by decide) (by decide) (by decide)), slA0]
  have soA4 : memLoad32 Mm232 (F + 0xA4) = v189 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xA4) 4 from sep_offsets F (c := 284) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), slA4]
  have soB0 : memLoad32 Mm232 (F + 0xB0) = v16 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xB0) 4 from sep_offsets F (c := 284) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), slB0]
  have soB4 : memLoad32 Mm232 (F + 0xB4) = v15 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xB4) 4 from sep_offsets F (c := 284) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), slB4]
  have soB8 : memLoad32 Mm232 (F + 0xB8) = v136 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xB8) 4 from sep_offsets F (c := 284) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), slB8]
  have soBC : memLoad32 Mm232 (F + 0xBC) = v120 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xBC) 4 from sep_offsets F (c := 284) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), slBC]
  have soC0 : memLoad32 Mm232 (F + 0xC0) = v147 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xC0) 4 from sep_offsets F (c := 284) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), slC0]
  have soC4 : memLoad32 Mm232 (F + 0xC4) = v199 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xC4) 4 from sep_offsets F (c := 284) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), slC4]
  have soC8 : memLoad32 Mm232 (F + 0xC8) = v163 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xC8) 4 from sep_offsets F (c := 284) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), slC8]
  have soD0 : memLoad32 Mm232 (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xD0) 4 from sep_offsets F (c := 284) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), slD0]
  have soE0 : memLoad32 Mm232 (F + 0xE0) = v133 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xE0) 4 from sep_offsets F (c := 284) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), slE0]
  have soE8 : memLoad32 Mm232 (F + 0xE8) = v8 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xE8) 4 from sep_offsets F (c := 284) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), slE8]
  have soEC : memLoad32 Mm232 (F + 0xEC) = v33 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xEC) 4 from sep_offsets F (c := 284) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soF0 : memLoad32 Mm232 (F + 0xF0) = v206 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xF0) 4 from sep_offsets F (c := 284) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), slF0]
  have soFC : memLoad32 Mm232 (F + 0xFC) = v40 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0xFC) 4 from sep_offsets F (c := 284) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), slFC]
  have so100 : memLoad32 Mm232 (F + 0x100) = v51 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x100) 4 from sep_offsets F (c := 284) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100]
  have so104 : memLoad32 Mm232 (F + 0x104) = v62 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x104) 4 from sep_offsets F (c := 284) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), sl104]
  have so108 : memLoad32 Mm232 (F + 0x108) = v203 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x108) 4 from sep_offsets F (c := 284) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), sl108]
  have so110 : memLoad32 Mm232 (F + 0x110) = v67 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x110) 4 from sep_offsets F (c := 284) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so114 : memLoad32 Mm232 (F + 0x114) = v111 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x114) 4 from sep_offsets F (c := 284) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), sl114]
  have so118 : memLoad32 Mm232 (F + 0x118) = v122 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x118) 4 from sep_offsets F (c := 284) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), sl118]
  have so11C : memLoad32 Mm232 (F + 0x11C) = v231 := by
    rw [← hM232, memLoad32_store32_same]
  have so120 : memLoad32 Mm232 (F + 0x120) = v116 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x120) 4 from sep_offsets F (c := 284) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), sl120]
  have so124 : memLoad32 Mm232 (F + 0x124) = v124 := by
    rw [← hM232, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x124) 4 from sep_offsets F (c := 284) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), sl124]
  exact ⟨n239, Mm232, v233, v234, v235, v236, v237, v238, v239, (.cons d232 (.cons d233 (.cons d234 (.cons d235 (.cons d236 (.cons d237 (.cons d238 (.single d239)))))))), u239.self, hc232, fr232, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so84, so88, so94, so9C, soA0, soA4, soB0, soB4, soB8, soBC, soC0, soC4, soC8, soD0, soE0, soE8, soEC, soF0, soFC, so100, so104, so108, so110, so114, so118, so11C, so120, so124, hv233, hv234, hv235, hv236, hv237, hv238, hv239⟩

end C3.RV32
