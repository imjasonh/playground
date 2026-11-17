import C3BootProofs.Proofs.EdvReduceFacts

/-! # The inlined `Scalar::reduce` in `ed25519_verify`, segments 0 to 4

Each theorem steps 40 instructions. `scripts/gen-ev-reduce.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g0 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine}
    (s : St Mi B n 0x17C (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q20 : reg n (20 : Fin 32) = F + 0x90F)
    (q21 : reg n (21 : Fin 32) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v33 v35 v36 v37 v38 v39 : Word),
      Steps n n' ∧
      St M' B n' 0x1FC (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v19 ∧
      reg n' (6 : Fin 32) = v37 ∧
      reg n' (7 : Fin 32) = v16 ∧
      reg n' (8 : Fin 32) = v27 ∧
      reg n' (9 : Fin 32) = F + 0x990 ∧
      reg n' a0 = v39 ∧
      reg n' a1 = v38 ∧
      reg n' a2 = v24 ∧
      reg n' a3 = v15 ∧
      reg n' a4 = v35 ∧
      reg n' a5 = v29 ∧
      reg n' a6 = v23 ∧
      reg n' a7 = v30 ∧
      reg n' (20 : Fin 32) = F + 0x90F ∧
      reg n' (21 : Fin 32) = v36 ∧
      reg n' (24 : Fin 32) = v8 ∧
      reg n' (28 : Fin 32) = v22 ∧
      reg n' (29 : Fin 32) = v7 ∧
      reg n' (30 : Fin 32) = v26 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xEC) = v33 ∧
      memLoad32 M' (F + 0x10C) = v31 ∧
      memLoad32 M0 (F + 0x9F0) = v2 ∧
      memLoad32 M0 (F + 0x9F4) = v3 ∧
      (0x20000000 : Word) = v4 ∧
      memLoad32 M0 (F + 0x9F8) = v5 ∧
      memLoad32 M0 (F + 0x9FC) = v6 ∧
      aluEval .add v4 0xFFFFFFFF = v7 ∧
      aluEval .and v2 v7 = v8 ∧
      aluEval .srl v2 0x1D = v9 ∧
      aluEval .sll v3 0x3 = v10 ∧
      aluEval .srl v3 0x1A = v11 ∧
      aluEval .sll v5 0x6 = v12 ∧
      aluEval .or v9 v10 = v13 ∧
      aluEval .or v11 v12 = v14 ∧
      aluEval .and v13 v7 = v15 ∧
      aluEval .and v14 v7 = v16 ∧
      aluEval .srl v5 0x17 = v17 ∧
      aluEval .sll v6 0x9 = v18 ∧
      memLoad32 M0 (F + 0xA00) = v19 ∧
      (0x114E0000 : Word) = v20 ∧
      (0x1A617000 : Word) = v21 ∧
      aluEval .add v20 0xFFFFF9ED = v22 ∧
      aluEval .add v21 0x303 = v23 ∧
      aluEval .mulhu v8 v23 = v24 ∧
      aluEval .mulhu v15 v22 = v25 ∧
      aluEval .mul v8 v23 = v26 ∧
      aluEval .mul v15 v22 = v27 ∧
      aluEval .or v18 v17 = v28 ∧
      aluEval .srl v6 0x14 = v29 ∧
      memLoad32 M0 (F + 0xA04) = v30 ∧
      memLoad32 M0 (F + 0xA08) = v31 ∧
      memLoad32 M0 (F + 0xA0C) = v33 ∧
      aluEval .sll v19 0xC = v35 ∧
      aluEval .and v28 v7 = v36 ∧
      aluEval .or v35 v29 = v37 ∧
      aluEval .add v25 v24 = v38 ∧
      (0xF7C1000 : Word) = v39 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n0, d0, u0⟩ := s.swG hc ev_at_17c (off' := 0x17E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]; exact aligned_add hF (k := 12) (by decide)) (a := F + 0xC) (v := G21)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21])
  obtain ⟨Mm0, hM0⟩ : ∃ M', memStore32 Mi (F + 0xC) G21 = M' := ⟨_, rfl⟩
  rw [hM0] at u0
  have hc0 : CodeIn Mm0 B ed25519VerifyCode := by rw [← hM0]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr0 : ∀ x, Sep F 0x128 x 1 → Mm0 x = M0 x := fun x hx => by
    rw [← hM0, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n1, d1, u1⟩ := u0.aluImmE hc0 ev_at_17e (off' := 0x182) (by decide) (v := F + 0x990)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]; show F + 0x90F + 0x81 = _; rw [BitVec.add_assoc]; rfl)
  obtain ⟨n2, v2, d2, hv2, u2⟩ := u1.lwG hc0 ev_at_182 (off' := 0x184) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]; rw [show F + 0x990 + 0x60 = F + 0x9F0 from by rw [BitVec.add_assoc]; rfl]; exact aligned_add hF (k := 2544) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv2
  rw [show F + 0x990 + 0x60 = F + 0x9F0 from by rw [BitVec.add_assoc]; rfl] at hv2
  rw [load_frame fr0 (show Sep F 0x128 (F + 0x9F0) 4 from ev_sepIn F 2544 (by decide) (by decide))] at hv2
  obtain ⟨n3, v3, d3, hv3, u3⟩ := u2.lwG hc0 ev_at_184 (off' := 0x186) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]; rw [show F + 0x990 + 0x64 = F + 0x9F4 from by rw [BitVec.add_assoc]; rfl]; exact aligned_add hF (k := 2548) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv3
  rw [show F + 0x990 + 0x64 = F + 0x9F4 from by rw [BitVec.add_assoc]; rfl] at hv3
  rw [load_frame fr0 (show Sep F 0x128 (F + 0x9F4) 4 from ev_sepIn F 2548 (by decide) (by decide))] at hv3
  obtain ⟨n4, v4, d4, hv4, u4⟩ := u3.luiG hc0 ev_at_186 (off' := 0x18A) (by decide)
  obtain ⟨n5, v5, d5, hv5, u5⟩ := u4.lwG hc0 ev_at_18a (off' := 0x18C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]; rw [show F + 0x990 + 0x68 = F + 0x9F8 from by rw [BitVec.add_assoc]; rfl]; exact aligned_add hF (k := 2552) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv5
  rw [show F + 0x990 + 0x68 = F + 0x9F8 from by rw [BitVec.add_assoc]; rfl] at hv5
  rw [load_frame fr0 (show Sep F 0x128 (F + 0x9F8) 4 from ev_sepIn F 2552 (by decide) (by decide))] at hv5
  obtain ⟨n6, v6, d6, hv6, u6⟩ := u5.lwG hc0 ev_at_18c (off' := 0x18E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]; rw [show F + 0x990 + 0x6C = F + 0x9FC from by rw [BitVec.add_assoc]; rfl]; exact aligned_add hF (k := 2556) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv6
  rw [show F + 0x990 + 0x6C = F + 0x9FC from by rw [BitVec.add_assoc]; rfl] at hv6
  rw [load_frame fr0 (show Sep F 0x128 (F + 0x9FC) 4 from ev_sepIn F 2556 (by decide) (by decide))] at hv6
  obtain ⟨n7, v7, d7, hv7, u7⟩ := u6.aluImmG hc0 ev_at_18e (off' := 0x192) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv7
  obtain ⟨n8, v8, d8, hv8, u8⟩ := u7.aluG hc0 ev_at_192 (off' := 0x196) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv8
  obtain ⟨n9, v9, d9, hv9, u9⟩ := u8.aluImmG hc0 ev_at_196 (off' := 0x198) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv9
  obtain ⟨n10, v10, d10, hv10, u10⟩ := u9.aluImmG hc0 ev_at_198 (off' := 0x19C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv10
  obtain ⟨n11, v11, d11, hv11, u11⟩ := u10.aluImmG hc0 ev_at_19c (off' := 0x19E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv11
  obtain ⟨n12, v12, d12, hv12, u12⟩ := u11.aluImmG hc0 ev_at_19e (off' := 0x1A2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv12
  obtain ⟨n13, v13, d13, hv13, u13⟩ := u12.aluG hc0 ev_at_1a2 (off' := 0x1A4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv13
  obtain ⟨n14, v14, d14, hv14, u14⟩ := u13.aluG hc0 ev_at_1a4 (off' := 0x1A6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv14
  obtain ⟨n15, v15, d15, hv15, u15⟩ := u14.aluG hc0 ev_at_1a6 (off' := 0x1AA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv15
  obtain ⟨n16, v16, d16, hv16, u16⟩ := u15.aluG hc0 ev_at_1aa (off' := 0x1AE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv16
  obtain ⟨n17, v17, d17, hv17, u17⟩ := u16.aluImmG hc0 ev_at_1ae (off' := 0x1B0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv17
  obtain ⟨n18, v18, d18, hv18, u18⟩ := u17.aluImmG hc0 ev_at_1b0 (off' := 0x1B4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv18
  obtain ⟨n19, v19, d19, hv19, u19⟩ := u18.lwG hc0 ev_at_1b4 (off' := 0x1B8) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]; rw [show F + 0x90F + 0xF1 = F + 0xA00 from by rw [BitVec.add_assoc]; rfl]; exact aligned_add hF (k := 2560) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv19
  rw [show F + 0x90F + 0xF1 = F + 0xA00 from by rw [BitVec.add_assoc]; rfl] at hv19
  rw [load_frame fr0 (show Sep F 0x128 (F + 0xA00) 4 from ev_sepIn F 2560 (by decide) (by decide))] at hv19
  obtain ⟨n20, v20, d20, hv20, u20⟩ := u19.luiG hc0 ev_at_1b8 (off' := 0x1BC) (by decide)
  obtain ⟨n21, v21, d21, hv21, u21⟩ := u20.luiG hc0 ev_at_1bc (off' := 0x1C0) (by decide)
  obtain ⟨n22, v22, d22, hv22, u22⟩ := u21.aluImmG hc0 ev_at_1c0 (off' := 0x1C4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv22
  obtain ⟨n23, v23, d23, hv23, u23⟩ := u22.aluImmG hc0 ev_at_1c4 (off' := 0x1C8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv23
  obtain ⟨n24, v24, d24, hv24, u24⟩ := u23.aluG hc0 ev_at_1c8 (off' := 0x1CC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv24
  obtain ⟨n25, v25, d25, hv25, u25⟩ := u24.aluG hc0 ev_at_1cc (off' := 0x1D0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv25
  obtain ⟨n26, v26, d26, hv26, u26⟩ := u25.aluG hc0 ev_at_1d0 (off' := 0x1D4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv26
  obtain ⟨n27, v27, d27, hv27, u27⟩ := u26.aluG hc0 ev_at_1d4 (off' := 0x1D8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv27
  obtain ⟨n28, v28, d28, hv28, u28⟩ := u27.aluG hc0 ev_at_1d8 (off' := 0x1DA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv28
  obtain ⟨n29, v29, d29, hv29, u29⟩ := u28.aluImmG hc0 ev_at_1da (off' := 0x1DC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv29
  obtain ⟨n30, v30, d30, hv30, u30⟩ := u29.lwG hc0 ev_at_1dc (off' := 0x1E0) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]; rw [show F + 0x90F + 0xF5 = F + 0xA04 from by rw [BitVec.add_assoc]; rfl]; exact aligned_add hF (k := 2564) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv30
  rw [show F + 0x90F + 0xF5 = F + 0xA04 from by rw [BitVec.add_assoc]; rfl] at hv30
  rw [load_frame fr0 (show Sep F 0x128 (F + 0xA04) 4 from ev_sepIn F 2564 (by decide) (by decide))] at hv30
  obtain ⟨n31, v31, d31, hv31, u31⟩ := u30.lwG hc0 ev_at_1e0 (off' := 0x1E2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]; rw [show F + 0x990 + 0x78 = F + 0xA08 from by rw [BitVec.add_assoc]; rfl]; exact aligned_add hF (k := 2568) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv31
  rw [show F + 0x990 + 0x78 = F + 0xA08 from by rw [BitVec.add_assoc]; rfl] at hv31
  rw [load_frame fr0 (show Sep F 0x128 (F + 0xA08) 4 from ev_sepIn F 2568 (by decide) (by decide))] at hv31
  obtain ⟨n32, d32, u32⟩ := u31.swG hc0 ev_at_1e2 (off' := 0x1E6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]; exact aligned_add hF (k := 268) (by decide)) (a := F + 0x10C) (v := v31)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21])
  obtain ⟨Mm32, hM32⟩ : ∃ M', memStore32 Mm0 (F + 0x10C) v31 = M' := ⟨_, rfl⟩
  rw [hM32] at u32
  have hc32 : CodeIn Mm32 B ed25519VerifyCode := by rw [← hM32]; exact hc0.store32 (frm_sep' sFC (by decide))
  have fr32 : ∀ x, Sep F 0x128 x 1 → Mm32 x = M0 x := fun x hx => by
    rw [← hM32, memStore32_get_sep (frm_sep' hx (by decide)), fr0 x hx]
  obtain ⟨n33, v33, d33, hv33, u33⟩ := u32.lwG hc32 ev_at_1e6 (off' := 0x1E8) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]; rw [show F + 0x990 + 0x7C = F + 0xA0C from by rw [BitVec.add_assoc]; rfl]; exact aligned_add hF (k := 2572) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv33
  rw [show F + 0x990 + 0x7C = F + 0xA0C from by rw [BitVec.add_assoc]; rfl] at hv33
  rw [load_frame fr32 (show Sep F 0x128 (F + 0xA0C) 4 from ev_sepIn F 2572 (by decide) (by decide))] at hv33
  obtain ⟨n34, d34, u34⟩ := u33.swG hc32 ev_at_1e8 (off' := 0x1EA) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]; exact aligned_add hF (k := 236) (by decide)) (a := F + 0xEC) (v := v33)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21])
  obtain ⟨Mm34, hM34⟩ : ∃ M', memStore32 Mm32 (F + 0xEC) v33 = M' := ⟨_, rfl⟩
  rw [hM34] at u34
  have hc34 : CodeIn Mm34 B ed25519VerifyCode := by rw [← hM34]; exact hc32.store32 (frm_sep' sFC (by decide))
  have fr34 : ∀ x, Sep F 0x128 x 1 → Mm34 x = M0 x := fun x hx => by
    rw [← hM34, memStore32_get_sep (frm_sep' hx (by decide)), fr32 x hx]
  obtain ⟨n35, v35, d35, hv35, u35⟩ := u34.aluImmG hc34 ev_at_1ea (off' := 0x1EE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv35
  obtain ⟨n36, v36, d36, hv36, u36⟩ := u35.aluG hc34 ev_at_1ee (off' := 0x1F2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv36
  obtain ⟨n37, v37, d37, hv37, u37⟩ := u36.aluG hc34 ev_at_1f2 (off' := 0x1F6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv37
  obtain ⟨n38, v38, d38, hv38, u38⟩ := u37.aluG hc34 ev_at_1f6 (off' := 0x1F8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21] at hv38
  obtain ⟨n39, v39, d39, hv39, u39⟩ := u38.luiG hc34 ev_at_1f8 (off' := 0x1FC) (by decide)
  have qo2 : reg n39 sp = F := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo3 : reg n39 (3 : Fin 32) = G3 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo4 : reg n39 (4 : Fin 32) = G4 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo5 : reg n39 (5 : Fin 32) = v19 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo6 : reg n39 (6 : Fin 32) = v37 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo7 : reg n39 (7 : Fin 32) = v16 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo8 : reg n39 (8 : Fin 32) = v27 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo9 : reg n39 (9 : Fin 32) = F + 0x990 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo10 : reg n39 a0 = v39 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo11 : reg n39 a1 = v38 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo12 : reg n39 a2 = v24 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo13 : reg n39 a3 = v15 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo14 : reg n39 a4 = v35 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo15 : reg n39 a5 = v29 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo16 : reg n39 a6 = v23 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo17 : reg n39 a7 = v30 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo20 : reg n39 (20 : Fin 32) = F + 0x90F := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo21 : reg n39 (21 : Fin 32) = v36 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo24 : reg n39 (24 : Fin 32) = v8 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo28 : reg n39 (28 : Fin 32) = v22 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo29 : reg n39 (29 : Fin 32) = v7 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have qo30 : reg n39 (30 : Fin 32) = v26 := by rw [u39.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q20, q21]
  have soC : memLoad32 Mm34 (F + 0xC) = G21 := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0xC) 4 from sep_offsets F (c := 236) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM32, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0xC) 4 from sep_offsets F (c := 268) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM0, memLoad32_store32_same]
  have so10 : memLoad32 Mm34 (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x10) 4 from sep_offsets F (c := 236) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM32, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0x10) 4 from sep_offsets F (c := 268) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM0, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x10) 4 from sep_offsets F (c := 12) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have soD0 : memLoad32 Mm34 (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0xD0) 4 from sep_offsets F (c := 236) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM32, memLoad32_store32_sep (show Sep (F + 0x10C) 4 (F + 0xD0) 4 from sep_offsets F (c := 268) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM0, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0xD0) 4 from sep_offsets F (c := 12) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), slD0]
  have soEC : memLoad32 Mm34 (F + 0xEC) = v33 := by
    rw [← hM34, memLoad32_store32_same]
  have so10C : memLoad32 Mm34 (F + 0x10C) = v31 := by
    rw [← hM34, memLoad32_store32_sep (show Sep (F + 0xEC) 4 (F + 0x10C) 4 from sep_offsets F (c := 236) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM32, memLoad32_store32_same]
  exact ⟨n39, Mm34, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v33, v35, v36, v37, v38, v39, (.cons d0 (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.cons d18 (.cons d19 (.cons d20 (.cons d21 (.cons d22 (.cons d23 (.cons d24 (.cons d25 (.cons d26 (.cons d27 (.cons d28 (.cons d29 (.cons d30 (.cons d31 (.cons d32 (.cons d33 (.cons d34 (.cons d35 (.cons d36 (.cons d37 (.cons d38 (.single d39)))))))))))))))))))))))))))))))))))))))), u39.self, hc34, fr34, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo20, qo21, qo24, qo28, qo29, qo30, soC, so10, soD0, soEC, so10C, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15, hv16, hv17, hv18, hv19, hv20, hv21, hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31, hv33, hv35, hv36, hv37, hv38, hv39⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g1 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v8 v15 v16 v19 v22 v23 v24 v26 v27 v29 v30 v31 v33 v35 v36 v37 v38 v39 : Word}
    (s : St Mi B n 0x1FC (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v19)
    (q6 : reg n (6 : Fin 32) = v37)
    (q7 : reg n (7 : Fin 32) = v16)
    (q8 : reg n (8 : Fin 32) = v27)
    (q9 : reg n (9 : Fin 32) = F + 0x990)
    (q10 : reg n a0 = v39)
    (q11 : reg n a1 = v38)
    (q12 : reg n a2 = v24)
    (q13 : reg n a3 = v15)
    (q14 : reg n a4 = v35)
    (q15 : reg n a5 = v29)
    (q16 : reg n a6 = v23)
    (q17 : reg n a7 = v30)
    (q20 : reg n (20 : Fin 32) = F + 0x90F)
    (q21 : reg n (21 : Fin 32) = v36)
    (q24 : reg n (24 : Fin 32) = v8)
    (q28 : reg n (28 : Fin 32) = v22)
    (q29 : reg n (29 : Fin 32) = v7)
    (q30 : reg n (30 : Fin 32) = v26)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slEC : memLoad32 Mi (F + 0xEC) = v33)
    (sl10C : memLoad32 Mi (F + 0x10C) = v31)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v40 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v64 v65 v66 v67 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 : Word),
      Steps n n' ∧
      St M' B n' 0x288 (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v19 ∧
      reg n' (6 : Fin 32) = v37 ∧
      reg n' (7 : Fin 32) = v16 ∧
      reg n' (8 : Fin 32) = v74 ∧
      reg n' (9 : Fin 32) = F + 0x990 ∧
      reg n' a0 = v72 ∧
      reg n' a1 = v78 ∧
      reg n' a2 = v71 ∧
      reg n' a3 = v15 ∧
      reg n' a4 = v56 ∧
      reg n' a5 = v79 ∧
      reg n' a6 = v23 ∧
      reg n' a7 = v30 ∧
      reg n' (18 : Fin 32) = v75 ∧
      reg n' (19 : Fin 32) = v53 ∧
      reg n' (20 : Fin 32) = v76 ∧
      reg n' (21 : Fin 32) = v36 ∧
      reg n' (22 : Fin 32) = v69 ∧
      reg n' (23 : Fin 32) = v77 ∧
      reg n' (24 : Fin 32) = v8 ∧
      reg n' (28 : Fin 32) = v22 ∧
      reg n' (29 : Fin 32) = v7 ∧
      reg n' (30 : Fin 32) = v54 ∧
      reg n' (31 : Fin 32) = v42 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xEC) = v33 ∧
      memLoad32 M' (F + 0xFC) = v40 ∧
      memLoad32 M' (F + 0x100) = v51 ∧
      memLoad32 M' (F + 0x104) = v62 ∧
      memLoad32 M' (F + 0x10C) = v31 ∧
      memLoad32 M' (F + 0x110) = v67 ∧
      aluEval .add v27 v26 = v40 ∧
      aluEval .add v39 0xFFFFF98C = v42 ∧
      aluEval .sltu v40 v27 = v43 ∧
      aluEval .mul v8 v42 = v44 ∧
      aluEval .mulhu v8 v42 = v45 ∧
      aluEval .mul v15 v23 = v46 ∧
      aluEval .mulhu v15 v23 = v47 ∧
      aluEval .mulhu v16 v22 = v48 ∧
      aluEval .mul v16 v22 = v49 ∧
      (0x16793000 : Word) = v50 ∧
      aluEval .add v38 v43 = v51 ∧
      aluEval .add v50 0x167 = v53 ∧
      aluEval .mul v8 v53 = v54 ∧
      aluEval .mulhu v8 v53 = v55 ∧
      aluEval .mul v15 v42 = v56 ∧
      aluEval .mulhu v15 v42 = v57 ∧
      aluEval .add v44 v46 = v58 ∧
      aluEval .mulhu v16 v23 = v59 ∧
      aluEval .add v45 v47 = v60 ∧
      aluEval .sltu v58 v46 = v61 ∧
      aluEval .add v49 v58 = v62 ∧
      aluEval .add v60 v48 = v64 ∧
      aluEval .sltu v62 v58 = v65 ∧
      aluEval .add v61 v64 = v66 ∧
      aluEval .add v65 v66 = v67 ∧
      aluEval .mul v16 v23 = v69 ∧
      aluEval .add v57 v55 = v70 ∧
      aluEval .add v56 v54 = v71 ∧
      aluEval .add v70 v59 = v72 ∧
      (0x1FFD6000 : Word) = v73 ∧
      aluEval .mulhu v36 v22 = v74 ∧
      aluEval .add v73 0x56E = v75 ∧
      aluEval .mul v8 v75 = v76 ∧
      aluEval .mulhu v8 v75 = v77 ∧
      aluEval .mul v15 v53 = v78 ∧
      aluEval .mulhu v15 v53 = v79 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n40, v40, d40, hv40, u40⟩ := s.aluG hc ev_at_1fc (off' := 0x200) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv40
  obtain ⟨n41, d41, u41⟩ := u40.swG hc ev_at_200 (off' := 0x202) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]; exact aligned_add hF (k := 252) (by decide)) (a := F + 0xFC) (v := v40)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30])
  obtain ⟨Mm41, hM41⟩ : ∃ M', memStore32 Mi (F + 0xFC) v40 = M' := ⟨_, rfl⟩
  rw [hM41] at u41
  have hc41 : CodeIn Mm41 B ed25519VerifyCode := by rw [← hM41]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr41 : ∀ x, Sep F 0x128 x 1 → Mm41 x = M0 x := fun x hx => by
    rw [← hM41, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n42, v42, d42, hv42, u42⟩ := u41.aluImmG hc41 ev_at_202 (off' := 0x206) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv42
  obtain ⟨n43, v43, d43, hv43, u43⟩ := u42.aluG hc41 ev_at_206 (off' := 0x20A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv43
  obtain ⟨n44, v44, d44, hv44, u44⟩ := u43.aluG hc41 ev_at_20a (off' := 0x20E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv44
  obtain ⟨n45, v45, d45, hv45, u45⟩ := u44.aluG hc41 ev_at_20e (off' := 0x212) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv45
  obtain ⟨n46, v46, d46, hv46, u46⟩ := u45.aluG hc41 ev_at_212 (off' := 0x216) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv46
  obtain ⟨n47, v47, d47, hv47, u47⟩ := u46.aluG hc41 ev_at_216 (off' := 0x21A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv47
  obtain ⟨n48, v48, d48, hv48, u48⟩ := u47.aluG hc41 ev_at_21a (off' := 0x21E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv48
  obtain ⟨n49, v49, d49, hv49, u49⟩ := u48.aluG hc41 ev_at_21e (off' := 0x222) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv49
  obtain ⟨n50, v50, d50, hv50, u50⟩ := u49.luiG hc41 ev_at_222 (off' := 0x226) (by decide)
  obtain ⟨n51, v51, d51, hv51, u51⟩ := u50.aluG hc41 ev_at_226 (off' := 0x228) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv51
  obtain ⟨n52, d52, u52⟩ := u51.swG hc41 ev_at_228 (off' := 0x22C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]; exact aligned_add hF (k := 256) (by decide)) (a := F + 0x100) (v := v51)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30])
  obtain ⟨Mm52, hM52⟩ : ∃ M', memStore32 Mm41 (F + 0x100) v51 = M' := ⟨_, rfl⟩
  rw [hM52] at u52
  have hc52 : CodeIn Mm52 B ed25519VerifyCode := by rw [← hM52]; exact hc41.store32 (frm_sep' sFC (by decide))
  have fr52 : ∀ x, Sep F 0x128 x 1 → Mm52 x = M0 x := fun x hx => by
    rw [← hM52, memStore32_get_sep (frm_sep' hx (by decide)), fr41 x hx]
  obtain ⟨n53, v53, d53, hv53, u53⟩ := u52.aluImmG hc52 ev_at_22c (off' := 0x230) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv53
  obtain ⟨n54, v54, d54, hv54, u54⟩ := u53.aluG hc52 ev_at_230 (off' := 0x234) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv54
  obtain ⟨n55, v55, d55, hv55, u55⟩ := u54.aluG hc52 ev_at_234 (off' := 0x238) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv55
  obtain ⟨n56, v56, d56, hv56, u56⟩ := u55.aluG hc52 ev_at_238 (off' := 0x23C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv56
  obtain ⟨n57, v57, d57, hv57, u57⟩ := u56.aluG hc52 ev_at_23c (off' := 0x240) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv57
  obtain ⟨n58, v58, d58, hv58, u58⟩ := u57.aluG hc52 ev_at_240 (off' := 0x242) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv58
  obtain ⟨n59, v59, d59, hv59, u59⟩ := u58.aluG hc52 ev_at_242 (off' := 0x246) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv59
  obtain ⟨n60, v60, d60, hv60, u60⟩ := u59.aluG hc52 ev_at_246 (off' := 0x248) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv60
  obtain ⟨n61, v61, d61, hv61, u61⟩ := u60.aluG hc52 ev_at_248 (off' := 0x24C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv61
  obtain ⟨n62, v62, d62, hv62, u62⟩ := u61.aluG hc52 ev_at_24c (off' := 0x24E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv62
  obtain ⟨n63, d63, u63⟩ := u62.swG hc52 ev_at_24e (off' := 0x252) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]; exact aligned_add hF (k := 260) (by decide)) (a := F + 0x104) (v := v62)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30])
  obtain ⟨Mm63, hM63⟩ : ∃ M', memStore32 Mm52 (F + 0x104) v62 = M' := ⟨_, rfl⟩
  rw [hM63] at u63
  have hc63 : CodeIn Mm63 B ed25519VerifyCode := by rw [← hM63]; exact hc52.store32 (frm_sep' sFC (by decide))
  have fr63 : ∀ x, Sep F 0x128 x 1 → Mm63 x = M0 x := fun x hx => by
    rw [← hM63, memStore32_get_sep (frm_sep' hx (by decide)), fr52 x hx]
  obtain ⟨n64, v64, d64, hv64, u64⟩ := u63.aluG hc63 ev_at_252 (off' := 0x254) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv64
  obtain ⟨n65, v65, d65, hv65, u65⟩ := u64.aluG hc63 ev_at_254 (off' := 0x258) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv65
  obtain ⟨n66, v66, d66, hv66, u66⟩ := u65.aluG hc63 ev_at_258 (off' := 0x25A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv66
  obtain ⟨n67, v67, d67, hv67, u67⟩ := u66.aluG hc63 ev_at_25a (off' := 0x25C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv67
  obtain ⟨n68, d68, u68⟩ := u67.swG hc63 ev_at_25c (off' := 0x260) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]; exact aligned_add hF (k := 272) (by decide)) (a := F + 0x110) (v := v67)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30])
  obtain ⟨Mm68, hM68⟩ : ∃ M', memStore32 Mm63 (F + 0x110) v67 = M' := ⟨_, rfl⟩
  rw [hM68] at u68
  have hc68 : CodeIn Mm68 B ed25519VerifyCode := by rw [← hM68]; exact hc63.store32 (frm_sep' sFC (by decide))
  have fr68 : ∀ x, Sep F 0x128 x 1 → Mm68 x = M0 x := fun x hx => by
    rw [← hM68, memStore32_get_sep (frm_sep' hx (by decide)), fr63 x hx]
  obtain ⟨n69, v69, d69, hv69, u69⟩ := u68.aluG hc68 ev_at_260 (off' := 0x264) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv69
  obtain ⟨n70, v70, d70, hv70, u70⟩ := u69.aluG hc68 ev_at_264 (off' := 0x266) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv70
  obtain ⟨n71, v71, d71, hv71, u71⟩ := u70.aluG hc68 ev_at_266 (off' := 0x26A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv71
  obtain ⟨n72, v72, d72, hv72, u72⟩ := u71.aluG hc68 ev_at_26a (off' := 0x26C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv72
  obtain ⟨n73, v73, d73, hv73, u73⟩ := u72.luiG hc68 ev_at_26c (off' := 0x270) (by decide)
  obtain ⟨n74, v74, d74, hv74, u74⟩ := u73.aluG hc68 ev_at_270 (off' := 0x274) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv74
  obtain ⟨n75, v75, d75, hv75, u75⟩ := u74.aluImmG hc68 ev_at_274 (off' := 0x278) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv75
  obtain ⟨n76, v76, d76, hv76, u76⟩ := u75.aluG hc68 ev_at_278 (off' := 0x27C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv76
  obtain ⟨n77, v77, d77, hv77, u77⟩ := u76.aluG hc68 ev_at_27c (off' := 0x280) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv77
  obtain ⟨n78, v78, d78, hv78, u78⟩ := u77.aluG hc68 ev_at_280 (off' := 0x284) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv78
  obtain ⟨n79, v79, d79, hv79, u79⟩ := u78.aluG hc68 ev_at_284 (off' := 0x288) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30] at hv79
  have qo2 : reg n79 sp = F := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo3 : reg n79 (3 : Fin 32) = G3 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo4 : reg n79 (4 : Fin 32) = G4 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo5 : reg n79 (5 : Fin 32) = v19 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo6 : reg n79 (6 : Fin 32) = v37 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo7 : reg n79 (7 : Fin 32) = v16 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo8 : reg n79 (8 : Fin 32) = v74 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo9 : reg n79 (9 : Fin 32) = F + 0x990 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo10 : reg n79 a0 = v72 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo11 : reg n79 a1 = v78 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo12 : reg n79 a2 = v71 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo13 : reg n79 a3 = v15 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo14 : reg n79 a4 = v56 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo15 : reg n79 a5 = v79 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo16 : reg n79 a6 = v23 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo17 : reg n79 a7 = v30 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo18 : reg n79 (18 : Fin 32) = v75 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo19 : reg n79 (19 : Fin 32) = v53 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo20 : reg n79 (20 : Fin 32) = v76 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo21 : reg n79 (21 : Fin 32) = v36 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo22 : reg n79 (22 : Fin 32) = v69 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo23 : reg n79 (23 : Fin 32) = v77 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo24 : reg n79 (24 : Fin 32) = v8 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo28 : reg n79 (28 : Fin 32) = v22 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo29 : reg n79 (29 : Fin 32) = v7 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo30 : reg n79 (30 : Fin 32) = v54 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have qo31 : reg n79 (31 : Fin 32) = v42 := by rw [u79.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q20, q21, q24, q28, q29, q30]
  have soC : memLoad32 Mm68 (F + 0xC) = G21 := by
    rw [← hM68, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0xC) 4 from sep_offsets F (c := 272) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM63, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0xC) 4 from sep_offsets F (c := 260) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM52, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xC) 4 from sep_offsets F (c := 256) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM41, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xC) 4 from sep_offsets F (c := 252) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slC]
  have so10 : memLoad32 Mm68 (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [← hM68, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x10) 4 from sep_offsets F (c := 272) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM63, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x10) 4 from sep_offsets F (c := 260) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM52, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x10) 4 from sep_offsets F (c := 256) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM41, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x10) 4 from sep_offsets F (c := 252) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have soD0 : memLoad32 Mm68 (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [← hM68, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0xD0) 4 from sep_offsets F (c := 272) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM63, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0xD0) 4 from sep_offsets F (c := 260) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM52, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xD0) 4 from sep_offsets F (c := 256) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM41, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xD0) 4 from sep_offsets F (c := 252) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), slD0]
  have soEC : memLoad32 Mm68 (F + 0xEC) = v33 := by
    rw [← hM68, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0xEC) 4 from sep_offsets F (c := 272) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM63, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0xEC) 4 from sep_offsets F (c := 260) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM52, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xEC) 4 from sep_offsets F (c := 256) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM41, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xEC) 4 from sep_offsets F (c := 252) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soFC : memLoad32 Mm68 (F + 0xFC) = v40 := by
    rw [← hM68, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0xFC) 4 from sep_offsets F (c := 272) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM63, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0xFC) 4 from sep_offsets F (c := 260) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM52, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xFC) 4 from sep_offsets F (c := 256) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM41, memLoad32_store32_same]
  have so100 : memLoad32 Mm68 (F + 0x100) = v51 := by
    rw [← hM68, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x100) 4 from sep_offsets F (c := 272) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM63, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x100) 4 from sep_offsets F (c := 260) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM52, memLoad32_store32_same]
  have so104 : memLoad32 Mm68 (F + 0x104) = v62 := by
    rw [← hM68, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x104) 4 from sep_offsets F (c := 272) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM63, memLoad32_store32_same]
  have so10C : memLoad32 Mm68 (F + 0x10C) = v31 := by
    rw [← hM68, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x10C) 4 from sep_offsets F (c := 272) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM63, memLoad32_store32_sep (show Sep (F + 0x104) 4 (F + 0x10C) 4 from sep_offsets F (c := 260) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM52, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x10C) 4 from sep_offsets F (c := 256) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM41, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x10C) 4 from sep_offsets F (c := 252) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C]
  have so110 : memLoad32 Mm68 (F + 0x110) = v67 := by
    rw [← hM68, memLoad32_store32_same]
  exact ⟨n79, Mm68, v40, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v64, v65, v66, v67, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, (.cons d40 (.cons d41 (.cons d42 (.cons d43 (.cons d44 (.cons d45 (.cons d46 (.cons d47 (.cons d48 (.cons d49 (.cons d50 (.cons d51 (.cons d52 (.cons d53 (.cons d54 (.cons d55 (.cons d56 (.cons d57 (.cons d58 (.cons d59 (.cons d60 (.cons d61 (.cons d62 (.cons d63 (.cons d64 (.cons d65 (.cons d66 (.cons d67 (.cons d68 (.cons d69 (.cons d70 (.cons d71 (.cons d72 (.cons d73 (.cons d74 (.cons d75 (.cons d76 (.cons d77 (.cons d78 (.single d79)))))))))))))))))))))))))))))))))))))))), u79.self, hc68, fr68, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo28, qo29, qo30, qo31, soC, so10, soD0, soEC, soFC, so100, so104, so10C, so110, hv40, hv42, hv43, hv44, hv45, hv46, hv47, hv48, hv49, hv50, hv51, hv53, hv54, hv55, hv56, hv57, hv58, hv59, hv60, hv61, hv62, hv64, hv65, hv66, hv67, hv69, hv70, hv71, hv72, hv73, hv74, hv75, hv76, hv77, hv78, hv79⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g2 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v8 v15 v16 v19 v22 v23 v30 v31 v33 v36 v37 v40 v42 v51 v53 v54 v56 v62 v67 v69 v71 v72 v74 v75 v76 v77 v78 v79 : Word}
    (s : St Mi B n 0x288 (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v19)
    (q6 : reg n (6 : Fin 32) = v37)
    (q7 : reg n (7 : Fin 32) = v16)
    (q8 : reg n (8 : Fin 32) = v74)
    (q9 : reg n (9 : Fin 32) = F + 0x990)
    (q10 : reg n a0 = v72)
    (q11 : reg n a1 = v78)
    (q12 : reg n a2 = v71)
    (q13 : reg n a3 = v15)
    (q14 : reg n a4 = v56)
    (q15 : reg n a5 = v79)
    (q16 : reg n a6 = v23)
    (q17 : reg n a7 = v30)
    (q18 : reg n (18 : Fin 32) = v75)
    (q19 : reg n (19 : Fin 32) = v53)
    (q20 : reg n (20 : Fin 32) = v76)
    (q21 : reg n (21 : Fin 32) = v36)
    (q22 : reg n (22 : Fin 32) = v69)
    (q23 : reg n (23 : Fin 32) = v77)
    (q24 : reg n (24 : Fin 32) = v8)
    (q28 : reg n (28 : Fin 32) = v22)
    (q29 : reg n (29 : Fin 32) = v7)
    (q30 : reg n (30 : Fin 32) = v54)
    (q31 : reg n (31 : Fin 32) = v42)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slEC : memLoad32 Mi (F + 0xEC) = v33)
    (slFC : memLoad32 Mi (F + 0xFC) = v40)
    (sl100 : memLoad32 Mi (F + 0x100) = v51)
    (sl104 : memLoad32 Mi (F + 0x104) = v62)
    (sl10C : memLoad32 Mi (F + 0x10C) = v31)
    (sl110 : memLoad32 Mi (F + 0x110) = v67)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v107 v108 v109 v110 v111 v113 v114 v115 v116 v118 v119 : Word),
      Steps n n' ∧
      St M' B n' 0x30A (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v19 ∧
      reg n' (6 : Fin 32) = v87 ∧
      reg n' (7 : Fin 32) = v16 ∧
      reg n' (8 : Fin 32) = v108 ∧
      reg n' (9 : Fin 32) = v110 ∧
      reg n' a0 = v114 ∧
      reg n' a1 = v115 ∧
      reg n' a2 = v119 ∧
      reg n' a3 = v111 ∧
      reg n' a4 = v113 ∧
      reg n' a5 = v109 ∧
      reg n' a6 = v23 ∧
      reg n' a7 = v30 ∧
      reg n' (18 : Fin 32) = v75 ∧
      reg n' (19 : Fin 32) = v53 ∧
      reg n' (20 : Fin 32) = v107 ∧
      reg n' (21 : Fin 32) = v36 ∧
      reg n' (22 : Fin 32) = v118 ∧
      reg n' (23 : Fin 32) = v116 ∧
      reg n' (24 : Fin 32) = v8 ∧
      reg n' (25 : Fin 32) = v88 ∧
      reg n' (28 : Fin 32) = v22 ∧
      reg n' (29 : Fin 32) = v7 ∧
      reg n' (30 : Fin 32) = v54 ∧
      reg n' (31 : Fin 32) = v42 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0xB4) = v15 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xEC) = v33 ∧
      memLoad32 M' (F + 0xFC) = v40 ∧
      memLoad32 M' (F + 0x100) = v51 ∧
      memLoad32 M' (F + 0x104) = v62 ∧
      memLoad32 M' (F + 0x10C) = v31 ∧
      memLoad32 M' (F + 0x110) = v67 ∧
      memLoad32 M' (F + 0x114) = v111 ∧
      memLoad32 M' (F + 0x120) = v116 ∧
      aluEval .sltu v71 v56 = v80 ∧
      aluEval .add v69 v71 = v81 ∧
      aluEval .add v72 v80 = v82 ∧
      aluEval .mulhu v16 v42 = v83 ∧
      aluEval .sltu v81 v71 = v84 ∧
      aluEval .mul v16 v42 = v85 ∧
      aluEval .add v82 v84 = v86 ∧
      aluEval .and v37 v7 = v87 ∧
      aluEval .add v86 v74 = v88 ∧
      aluEval .mul v36 v23 = v89 ∧
      aluEval .add v79 v77 = v90 ∧
      aluEval .add v76 v78 = v91 ∧
      aluEval .mulhu v36 v23 = v92 ∧
      aluEval .mulhu v87 v22 = v93 ∧
      aluEval .add v83 v90 = v94 ∧
      aluEval .sltu v91 v78 = v95 ∧
      aluEval .add v85 v91 = v96 ∧
      aluEval .add v95 v94 = v97 ∧
      aluEval .mul v36 v22 = v98 ∧
      aluEval .sltu v96 v91 = v99 ∧
      aluEval .add v97 v99 = v100 ∧
      aluEval .add v89 v96 = v101 ∧
      aluEval .sltu v101 v96 = v102 ∧
      aluEval .mul v87 v22 = v103 ∧
      aluEval .add v100 v92 = v104 ∧
      aluEval .add v93 v102 = v105 ∧
      aluEval .mul v15 v75 = v107 ∧
      aluEval .mulhu v15 v75 = v108 ∧
      aluEval .mul v16 v53 = v109 ∧
      aluEval .mulhu v16 v53 = v110 ∧
      aluEval .add v81 v98 = v111 ∧
      aluEval .mulhu v36 v42 = v113 ∧
      aluEval .add v105 v104 = v114 ∧
      aluEval .sltu v111 v81 = v115 ∧
      aluEval .add v103 v101 = v116 ∧
      aluEval .mul v36 v42 = v118 ∧
      aluEval .sltu v116 v101 = v119 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n80, v80, d80, hv80, u80⟩ := s.aluG hc ev_at_288 (off' := 0x28C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv80
  obtain ⟨n81, v81, d81, hv81, u81⟩ := u80.aluG hc ev_at_28c (off' := 0x28E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv81
  obtain ⟨n82, v82, d82, hv82, u82⟩ := u81.aluG hc ev_at_28e (off' := 0x290) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv82
  obtain ⟨n83, v83, d83, hv83, u83⟩ := u82.aluG hc ev_at_290 (off' := 0x294) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv83
  obtain ⟨n84, v84, d84, hv84, u84⟩ := u83.aluG hc ev_at_294 (off' := 0x298) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv84
  obtain ⟨n85, v85, d85, hv85, u85⟩ := u84.aluG hc ev_at_298 (off' := 0x29C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv85
  obtain ⟨n86, v86, d86, hv86, u86⟩ := u85.aluG hc ev_at_29c (off' := 0x29E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv86
  obtain ⟨n87, v87, d87, hv87, u87⟩ := u86.aluG hc ev_at_29e (off' := 0x2A2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv87
  obtain ⟨n88, v88, d88, hv88, u88⟩ := u87.aluG hc ev_at_2a2 (off' := 0x2A6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv88
  obtain ⟨n89, v89, d89, hv89, u89⟩ := u88.aluG hc ev_at_2a6 (off' := 0x2AA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv89
  obtain ⟨n90, v90, d90, hv90, u90⟩ := u89.aluG hc ev_at_2aa (off' := 0x2AC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv90
  obtain ⟨n91, v91, d91, hv91, u91⟩ := u90.aluG hc ev_at_2ac (off' := 0x2AE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv91
  obtain ⟨n92, v92, d92, hv92, u92⟩ := u91.aluG hc ev_at_2ae (off' := 0x2B2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv92
  obtain ⟨n93, v93, d93, hv93, u93⟩ := u92.aluG hc ev_at_2b2 (off' := 0x2B6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv93
  obtain ⟨n94, v94, d94, hv94, u94⟩ := u93.aluG hc ev_at_2b6 (off' := 0x2B8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv94
  obtain ⟨n95, v95, d95, hv95, u95⟩ := u94.aluG hc ev_at_2b8 (off' := 0x2BC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv95
  obtain ⟨n96, v96, d96, hv96, u96⟩ := u95.aluG hc ev_at_2bc (off' := 0x2BE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv96
  obtain ⟨n97, v97, d97, hv97, u97⟩ := u96.aluG hc ev_at_2be (off' := 0x2C0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv97
  obtain ⟨n98, v98, d98, hv98, u98⟩ := u97.aluG hc ev_at_2c0 (off' := 0x2C4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv98
  obtain ⟨n99, v99, d99, hv99, u99⟩ := u98.aluG hc ev_at_2c4 (off' := 0x2C8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv99
  obtain ⟨n100, v100, d100, hv100, u100⟩ := u99.aluG hc ev_at_2c8 (off' := 0x2CA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv100
  obtain ⟨n101, v101, d101, hv101, u101⟩ := u100.aluG hc ev_at_2ca (off' := 0x2CC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv101
  obtain ⟨n102, v102, d102, hv102, u102⟩ := u101.aluG hc ev_at_2cc (off' := 0x2D0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv102
  obtain ⟨n103, v103, d103, hv103, u103⟩ := u102.aluG hc ev_at_2d0 (off' := 0x2D4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv103
  obtain ⟨n104, v104, d104, hv104, u104⟩ := u103.aluG hc ev_at_2d4 (off' := 0x2D6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv104
  obtain ⟨n105, v105, d105, hv105, u105⟩ := u104.aluG hc ev_at_2d6 (off' := 0x2D8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv105
  obtain ⟨n106, d106, u106⟩ := u105.swG hc ev_at_2d8 (off' := 0x2DA) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]; exact aligned_add hF (k := 180) (by decide)) (a := F + 0xB4) (v := v15)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31])
  obtain ⟨Mm106, hM106⟩ : ∃ M', memStore32 Mi (F + 0xB4) v15 = M' := ⟨_, rfl⟩
  rw [hM106] at u106
  have hc106 : CodeIn Mm106 B ed25519VerifyCode := by rw [← hM106]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr106 : ∀ x, Sep F 0x128 x 1 → Mm106 x = M0 x := fun x hx => by
    rw [← hM106, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n107, v107, d107, hv107, u107⟩ := u106.aluG hc106 ev_at_2da (off' := 0x2DE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv107
  obtain ⟨n108, v108, d108, hv108, u108⟩ := u107.aluG hc106 ev_at_2de (off' := 0x2E2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv108
  obtain ⟨n109, v109, d109, hv109, u109⟩ := u108.aluG hc106 ev_at_2e2 (off' := 0x2E6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv109
  obtain ⟨n110, v110, d110, hv110, u110⟩ := u109.aluG hc106 ev_at_2e6 (off' := 0x2EA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv110
  obtain ⟨n111, v111, d111, hv111, u111⟩ := u110.aluG hc106 ev_at_2ea (off' := 0x2EE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv111
  obtain ⟨n112, d112, u112⟩ := u111.swG hc106 ev_at_2ee (off' := 0x2F2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]; exact aligned_add hF (k := 276) (by decide)) (a := F + 0x114) (v := v111)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31])
  obtain ⟨Mm112, hM112⟩ : ∃ M', memStore32 Mm106 (F + 0x114) v111 = M' := ⟨_, rfl⟩
  rw [hM112] at u112
  have hc112 : CodeIn Mm112 B ed25519VerifyCode := by rw [← hM112]; exact hc106.store32 (frm_sep' sFC (by decide))
  have fr112 : ∀ x, Sep F 0x128 x 1 → Mm112 x = M0 x := fun x hx => by
    rw [← hM112, memStore32_get_sep (frm_sep' hx (by decide)), fr106 x hx]
  obtain ⟨n113, v113, d113, hv113, u113⟩ := u112.aluG hc112 ev_at_2f2 (off' := 0x2F6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv113
  obtain ⟨n114, v114, d114, hv114, u114⟩ := u113.aluG hc112 ev_at_2f6 (off' := 0x2F8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv114
  obtain ⟨n115, v115, d115, hv115, u115⟩ := u114.aluG hc112 ev_at_2f8 (off' := 0x2FC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv115
  obtain ⟨n116, v116, d116, hv116, u116⟩ := u115.aluG hc112 ev_at_2fc (off' := 0x2FE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv116
  obtain ⟨n117, d117, u117⟩ := u116.swG hc112 ev_at_2fe (off' := 0x302) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]; exact aligned_add hF (k := 288) (by decide)) (a := F + 0x120) (v := v116)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31])
  obtain ⟨Mm117, hM117⟩ : ∃ M', memStore32 Mm112 (F + 0x120) v116 = M' := ⟨_, rfl⟩
  rw [hM117] at u117
  have hc117 : CodeIn Mm117 B ed25519VerifyCode := by rw [← hM117]; exact hc112.store32 (frm_sep' sFC (by decide))
  have fr117 : ∀ x, Sep F 0x128 x 1 → Mm117 x = M0 x := fun x hx => by
    rw [← hM117, memStore32_get_sep (frm_sep' hx (by decide)), fr112 x hx]
  obtain ⟨n118, v118, d118, hv118, u118⟩ := u117.aluG hc117 ev_at_302 (off' := 0x306) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv118
  obtain ⟨n119, v119, d119, hv119, u119⟩ := u118.aluG hc117 ev_at_306 (off' := 0x30A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31] at hv119
  have qo2 : reg n119 sp = F := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo3 : reg n119 (3 : Fin 32) = G3 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo4 : reg n119 (4 : Fin 32) = G4 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo5 : reg n119 (5 : Fin 32) = v19 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo6 : reg n119 (6 : Fin 32) = v87 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo7 : reg n119 (7 : Fin 32) = v16 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo8 : reg n119 (8 : Fin 32) = v108 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo9 : reg n119 (9 : Fin 32) = v110 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo10 : reg n119 a0 = v114 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo11 : reg n119 a1 = v115 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo12 : reg n119 a2 = v119 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo13 : reg n119 a3 = v111 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo14 : reg n119 a4 = v113 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo15 : reg n119 a5 = v109 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo16 : reg n119 a6 = v23 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo17 : reg n119 a7 = v30 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo18 : reg n119 (18 : Fin 32) = v75 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo19 : reg n119 (19 : Fin 32) = v53 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo20 : reg n119 (20 : Fin 32) = v107 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo21 : reg n119 (21 : Fin 32) = v36 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo22 : reg n119 (22 : Fin 32) = v118 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo23 : reg n119 (23 : Fin 32) = v116 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo24 : reg n119 (24 : Fin 32) = v8 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo25 : reg n119 (25 : Fin 32) = v88 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo28 : reg n119 (28 : Fin 32) = v22 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo29 : reg n119 (29 : Fin 32) = v7 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo30 : reg n119 (30 : Fin 32) = v54 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have qo31 : reg n119 (31 : Fin 32) = v42 := by rw [u119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q28, q29, q30, q31]
  have soC : memLoad32 Mm117 (F + 0xC) = G21 := by
    rw [← hM117, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0xC) 4 from sep_offsets F (c := 288) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM112, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0xC) 4 from sep_offsets F (c := 276) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM106, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xC) 4 from sep_offsets F (c := 180) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slC]
  have so10 : memLoad32 Mm117 (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [← hM117, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x10) 4 from sep_offsets F (c := 288) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM112, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x10) 4 from sep_offsets F (c := 276) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM106, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x10) 4 from sep_offsets F (c := 180) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have soB4 : memLoad32 Mm117 (F + 0xB4) = v15 := by
    rw [← hM117, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0xB4) 4 from sep_offsets F (c := 288) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM112, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0xB4) 4 from sep_offsets F (c := 276) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM106, memLoad32_store32_same]
  have soD0 : memLoad32 Mm117 (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [← hM117, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0xD0) 4 from sep_offsets F (c := 288) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM112, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0xD0) 4 from sep_offsets F (c := 276) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM106, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xD0) 4 from sep_offsets F (c := 180) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), slD0]
  have soEC : memLoad32 Mm117 (F + 0xEC) = v33 := by
    rw [← hM117, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0xEC) 4 from sep_offsets F (c := 288) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM112, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0xEC) 4 from sep_offsets F (c := 276) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM106, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xEC) 4 from sep_offsets F (c := 180) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soFC : memLoad32 Mm117 (F + 0xFC) = v40 := by
    rw [← hM117, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0xFC) 4 from sep_offsets F (c := 288) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM112, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0xFC) 4 from sep_offsets F (c := 276) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM106, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xFC) 4 from sep_offsets F (c := 180) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), slFC]
  have so100 : memLoad32 Mm117 (F + 0x100) = v51 := by
    rw [← hM117, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x100) 4 from sep_offsets F (c := 288) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM112, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x100) 4 from sep_offsets F (c := 276) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM106, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x100) 4 from sep_offsets F (c := 180) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100]
  have so104 : memLoad32 Mm117 (F + 0x104) = v62 := by
    rw [← hM117, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x104) 4 from sep_offsets F (c := 288) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM112, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x104) 4 from sep_offsets F (c := 276) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM106, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x104) 4 from sep_offsets F (c := 180) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), sl104]
  have so10C : memLoad32 Mm117 (F + 0x10C) = v31 := by
    rw [← hM117, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x10C) 4 from sep_offsets F (c := 288) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM112, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x10C) 4 from sep_offsets F (c := 276) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM106, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x10C) 4 from sep_offsets F (c := 180) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C]
  have so110 : memLoad32 Mm117 (F + 0x110) = v67 := by
    rw [← hM117, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x110) 4 from sep_offsets F (c := 288) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM112, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x110) 4 from sep_offsets F (c := 276) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM106, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x110) 4 from sep_offsets F (c := 180) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so114 : memLoad32 Mm117 (F + 0x114) = v111 := by
    rw [← hM117, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x114) 4 from sep_offsets F (c := 288) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM112, memLoad32_store32_same]
  have so120 : memLoad32 Mm117 (F + 0x120) = v116 := by
    rw [← hM117, memLoad32_store32_same]
  exact ⟨n119, Mm117, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v107, v108, v109, v110, v111, v113, v114, v115, v116, v118, v119, (.cons d80 (.cons d81 (.cons d82 (.cons d83 (.cons d84 (.cons d85 (.cons d86 (.cons d87 (.cons d88 (.cons d89 (.cons d90 (.cons d91 (.cons d92 (.cons d93 (.cons d94 (.cons d95 (.cons d96 (.cons d97 (.cons d98 (.cons d99 (.cons d100 (.cons d101 (.cons d102 (.cons d103 (.cons d104 (.cons d105 (.cons d106 (.cons d107 (.cons d108 (.cons d109 (.cons d110 (.cons d111 (.cons d112 (.cons d113 (.cons d114 (.cons d115 (.cons d116 (.cons d117 (.cons d118 (.single d119)))))))))))))))))))))))))))))))))))))))), u119.self, hc117, fr117, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo28, qo29, qo30, qo31, soC, so10, soB4, soD0, soEC, soFC, so100, so104, so10C, so110, so114, so120, hv80, hv81, hv82, hv83, hv84, hv85, hv86, hv87, hv88, hv89, hv90, hv91, hv92, hv93, hv94, hv95, hv96, hv97, hv98, hv99, hv100, hv101, hv102, hv103, hv104, hv105, hv107, hv108, hv109, hv110, hv111, hv113, hv114, hv115, hv116, hv118, hv119⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g3 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v8 v15 v16 v19 v22 v23 v30 v31 v33 v36 v40 v42 v51 v53 v54 v62 v67 v75 v87 v88 v107 v108 v109 v110 v111 v113 v114 v115 v116 v118 v119 : Word}
    (s : St Mi B n 0x30A (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v19)
    (q6 : reg n (6 : Fin 32) = v87)
    (q7 : reg n (7 : Fin 32) = v16)
    (q8 : reg n (8 : Fin 32) = v108)
    (q9 : reg n (9 : Fin 32) = v110)
    (q10 : reg n a0 = v114)
    (q11 : reg n a1 = v115)
    (q12 : reg n a2 = v119)
    (q13 : reg n a3 = v111)
    (q14 : reg n a4 = v113)
    (q15 : reg n a5 = v109)
    (q16 : reg n a6 = v23)
    (q17 : reg n a7 = v30)
    (q18 : reg n (18 : Fin 32) = v75)
    (q19 : reg n (19 : Fin 32) = v53)
    (q20 : reg n (20 : Fin 32) = v107)
    (q21 : reg n (21 : Fin 32) = v36)
    (q22 : reg n (22 : Fin 32) = v118)
    (q23 : reg n (23 : Fin 32) = v116)
    (q24 : reg n (24 : Fin 32) = v8)
    (q25 : reg n (25 : Fin 32) = v88)
    (q28 : reg n (28 : Fin 32) = v22)
    (q29 : reg n (29 : Fin 32) = v7)
    (q30 : reg n (30 : Fin 32) = v54)
    (q31 : reg n (31 : Fin 32) = v42)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (slB4 : memLoad32 Mi (F + 0xB4) = v15)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slEC : memLoad32 Mi (F + 0xEC) = v33)
    (slFC : memLoad32 Mi (F + 0xFC) = v40)
    (sl100 : memLoad32 Mi (F + 0x100) = v51)
    (sl104 : memLoad32 Mi (F + 0x104) = v62)
    (sl10C : memLoad32 Mi (F + 0x10C) = v31)
    (sl110 : memLoad32 Mi (F + 0x110) = v67)
    (sl114 : memLoad32 Mi (F + 0x114) = v111)
    (sl120 : memLoad32 Mi (F + 0x120) = v116)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v120 v122 v124 v126 v127 v128 v129 v130 v131 v132 v133 v134 v136 v138 v140 v141 v142 v143 v144 v145 v146 v147 : Word),
      Steps n n' ∧
      St M' B n' 0x368 (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v132 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v19 ∧
      reg n' (6 : Fin 32) = v87 ∧
      reg n' (7 : Fin 32) = v146 ∧
      reg n' (8 : Fin 32) = v130 ∧
      reg n' (9 : Fin 32) = v110 ∧
      reg n' a0 = v145 ∧
      reg n' a1 = v144 ∧
      reg n' a2 = v136 ∧
      reg n' a3 = v120 ∧
      reg n' a4 = v147 ∧
      reg n' a5 = v143 ∧
      reg n' a6 = v23 ∧
      reg n' a7 = v30 ∧
      reg n' (18 : Fin 32) = v75 ∧
      reg n' (19 : Fin 32) = v53 ∧
      reg n' (20 : Fin 32) = v140 ∧
      reg n' (21 : Fin 32) = v36 ∧
      reg n' (22 : Fin 32) = v118 ∧
      reg n' (23 : Fin 32) = v138 ∧
      reg n' (24 : Fin 32) = v8 ∧
      reg n' (25 : Fin 32) = v141 ∧
      reg n' (26 : Fin 32) = v133 ∧
      reg n' (27 : Fin 32) = v142 ∧
      reg n' (28 : Fin 32) = v22 ∧
      reg n' (29 : Fin 32) = v7 ∧
      reg n' (30 : Fin 32) = v54 ∧
      reg n' (31 : Fin 32) = v42 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0xB0) = v16 ∧
      memLoad32 M' (F + 0xB4) = v15 ∧
      memLoad32 M' (F + 0xB8) = v136 ∧
      memLoad32 M' (F + 0xBC) = v120 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xE8) = v8 ∧
      memLoad32 M' (F + 0xEC) = v33 ∧
      memLoad32 M' (F + 0xFC) = v40 ∧
      memLoad32 M' (F + 0x100) = v51 ∧
      memLoad32 M' (F + 0x104) = v62 ∧
      memLoad32 M' (F + 0x10C) = v31 ∧
      memLoad32 M' (F + 0x110) = v67 ∧
      memLoad32 M' (F + 0x114) = v111 ∧
      memLoad32 M' (F + 0x118) = v122 ∧
      memLoad32 M' (F + 0x120) = v116 ∧
      memLoad32 M' (F + 0x124) = v124 ∧
      aluEval .mul v8 v22 = v120 ∧
      aluEval .add v115 v88 = v122 ∧
      aluEval .add v114 v119 = v124 ∧
      aluEval .add v108 v110 = v126 ∧
      aluEval .add v109 v107 = v127 ∧
      aluEval .add v113 v126 = v128 ∧
      aluEval .sltu v127 v109 = v129 ∧
      aluEval .add v128 v129 = v130 ∧
      (0x12548000 : Word) = v131 ∧
      aluEval .add v127 v118 = v132 ∧
      aluEval .add v131 0xFFFFFE1B = v133 ∧
      aluEval .sltu v132 v127 = v134 ∧
      aluEval .mul v120 v133 = v136 ∧
      aluEval .mulhu v87 v23 = v138 ∧
      aluEval .mul v16 v75 = v140 ∧
      aluEval .mulhu v16 v75 = v141 ∧
      aluEval .mulhu v36 v53 = v142 ∧
      aluEval .mul v36 v53 = v143 ∧
      aluEval .mulhu v87 v42 = v144 ∧
      aluEval .add v134 v130 = v145 ∧
      aluEval .mul v87 v42 = v146 ∧
      aluEval .mulhu v8 v22 = v147 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n120, v120, d120, hv120, u120⟩ := s.aluG hc ev_at_30a (off' := 0x30E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv120
  obtain ⟨n121, d121, u121⟩ := u120.swG hc ev_at_30e (off' := 0x310) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]; exact aligned_add hF (k := 232) (by decide)) (a := F + 0xE8) (v := v8)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31])
  obtain ⟨Mm121, hM121⟩ : ∃ M', memStore32 Mi (F + 0xE8) v8 = M' := ⟨_, rfl⟩
  rw [hM121] at u121
  have hc121 : CodeIn Mm121 B ed25519VerifyCode := by rw [← hM121]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr121 : ∀ x, Sep F 0x128 x 1 → Mm121 x = M0 x := fun x hx => by
    rw [← hM121, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n122, v122, d122, hv122, u122⟩ := u121.aluG hc121 ev_at_310 (off' := 0x312) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv122
  obtain ⟨n123, d123, u123⟩ := u122.swG hc121 ev_at_312 (off' := 0x316) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]; exact aligned_add hF (k := 280) (by decide)) (a := F + 0x118) (v := v122)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31])
  obtain ⟨Mm123, hM123⟩ : ∃ M', memStore32 Mm121 (F + 0x118) v122 = M' := ⟨_, rfl⟩
  rw [hM123] at u123
  have hc123 : CodeIn Mm123 B ed25519VerifyCode := by rw [← hM123]; exact hc121.store32 (frm_sep' sFC (by decide))
  have fr123 : ∀ x, Sep F 0x128 x 1 → Mm123 x = M0 x := fun x hx => by
    rw [← hM123, memStore32_get_sep (frm_sep' hx (by decide)), fr121 x hx]
  obtain ⟨n124, v124, d124, hv124, u124⟩ := u123.aluG hc123 ev_at_316 (off' := 0x318) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv124
  obtain ⟨n125, d125, u125⟩ := u124.swG hc123 ev_at_318 (off' := 0x31C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]; exact aligned_add hF (k := 292) (by decide)) (a := F + 0x124) (v := v124)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31])
  obtain ⟨Mm125, hM125⟩ : ∃ M', memStore32 Mm123 (F + 0x124) v124 = M' := ⟨_, rfl⟩
  rw [hM125] at u125
  have hc125 : CodeIn Mm125 B ed25519VerifyCode := by rw [← hM125]; exact hc123.store32 (frm_sep' sFC (by decide))
  have fr125 : ∀ x, Sep F 0x128 x 1 → Mm125 x = M0 x := fun x hx => by
    rw [← hM125, memStore32_get_sep (frm_sep' hx (by decide)), fr123 x hx]
  obtain ⟨n126, v126, d126, hv126, u126⟩ := u125.aluG hc125 ev_at_31c (off' := 0x31E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv126
  obtain ⟨n127, v127, d127, hv127, u127⟩ := u126.aluG hc125 ev_at_31e (off' := 0x322) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv127
  obtain ⟨n128, v128, d128, hv128, u128⟩ := u127.aluG hc125 ev_at_322 (off' := 0x324) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv128
  obtain ⟨n129, v129, d129, hv129, u129⟩ := u128.aluG hc125 ev_at_324 (off' := 0x328) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv129
  obtain ⟨n130, v130, d130, hv130, u130⟩ := u129.aluG hc125 ev_at_328 (off' := 0x32C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv130
  obtain ⟨n131, v131, d131, hv131, u131⟩ := u130.luiG hc125 ev_at_32c (off' := 0x330) (by decide)
  obtain ⟨n132, v132, d132, hv132, u132⟩ := u131.aluG hc125 ev_at_330 (off' := 0x334) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv132
  obtain ⟨n133, v133, d133, hv133, u133⟩ := u132.aluImmG hc125 ev_at_334 (off' := 0x338) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv133
  obtain ⟨n134, v134, d134, hv134, u134⟩ := u133.aluG hc125 ev_at_338 (off' := 0x33C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv134
  obtain ⟨n135, d135, u135⟩ := u134.swG hc125 ev_at_33c (off' := 0x33E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]; exact aligned_add hF (k := 188) (by decide)) (a := F + 0xBC) (v := v120)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31])
  obtain ⟨Mm135, hM135⟩ : ∃ M', memStore32 Mm125 (F + 0xBC) v120 = M' := ⟨_, rfl⟩
  rw [hM135] at u135
  have hc135 : CodeIn Mm135 B ed25519VerifyCode := by rw [← hM135]; exact hc125.store32 (frm_sep' sFC (by decide))
  have fr135 : ∀ x, Sep F 0x128 x 1 → Mm135 x = M0 x := fun x hx => by
    rw [← hM135, memStore32_get_sep (frm_sep' hx (by decide)), fr125 x hx]
  obtain ⟨n136, v136, d136, hv136, u136⟩ := u135.aluG hc135 ev_at_33e (off' := 0x342) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv136
  obtain ⟨n137, d137, u137⟩ := u136.swG hc135 ev_at_342 (off' := 0x344) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]; exact aligned_add hF (k := 184) (by decide)) (a := F + 0xB8) (v := v136)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31])
  obtain ⟨Mm137, hM137⟩ : ∃ M', memStore32 Mm135 (F + 0xB8) v136 = M' := ⟨_, rfl⟩
  rw [hM137] at u137
  have hc137 : CodeIn Mm137 B ed25519VerifyCode := by rw [← hM137]; exact hc135.store32 (frm_sep' sFC (by decide))
  have fr137 : ∀ x, Sep F 0x128 x 1 → Mm137 x = M0 x := fun x hx => by
    rw [← hM137, memStore32_get_sep (frm_sep' hx (by decide)), fr135 x hx]
  obtain ⟨n138, v138, d138, hv138, u138⟩ := u137.aluG hc137 ev_at_344 (off' := 0x348) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv138
  obtain ⟨n139, d139, u139⟩ := u138.swG hc137 ev_at_348 (off' := 0x34A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]; exact aligned_add hF (k := 176) (by decide)) (a := F + 0xB0) (v := v16)
    (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31])
  obtain ⟨Mm139, hM139⟩ : ∃ M', memStore32 Mm137 (F + 0xB0) v16 = M' := ⟨_, rfl⟩
  rw [hM139] at u139
  have hc139 : CodeIn Mm139 B ed25519VerifyCode := by rw [← hM139]; exact hc137.store32 (frm_sep' sFC (by decide))
  have fr139 : ∀ x, Sep F 0x128 x 1 → Mm139 x = M0 x := fun x hx => by
    rw [← hM139, memStore32_get_sep (frm_sep' hx (by decide)), fr137 x hx]
  obtain ⟨n140, v140, d140, hv140, u140⟩ := u139.aluG hc139 ev_at_34a (off' := 0x34E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv140
  obtain ⟨n141, v141, d141, hv141, u141⟩ := u140.aluG hc139 ev_at_34e (off' := 0x352) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv141
  obtain ⟨n142, v142, d142, hv142, u142⟩ := u141.aluG hc139 ev_at_352 (off' := 0x356) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv142
  obtain ⟨n143, v143, d143, hv143, u143⟩ := u142.aluG hc139 ev_at_356 (off' := 0x35A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv143
  obtain ⟨n144, v144, d144, hv144, u144⟩ := u143.aluG hc139 ev_at_35a (off' := 0x35E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv144
  obtain ⟨n145, v145, d145, hv145, u145⟩ := u144.aluG hc139 ev_at_35e (off' := 0x360) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv145
  obtain ⟨n146, v146, d146, hv146, u146⟩ := u145.aluG hc139 ev_at_360 (off' := 0x364) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv146
  obtain ⟨n147, v147, d147, hv147, u147⟩ := u146.aluG hc139 ev_at_364 (off' := 0x368) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31] at hv147
  have qo1 : reg n147 ra = v132 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo2 : reg n147 sp = F := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo3 : reg n147 (3 : Fin 32) = G3 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo4 : reg n147 (4 : Fin 32) = G4 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo5 : reg n147 (5 : Fin 32) = v19 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo6 : reg n147 (6 : Fin 32) = v87 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo7 : reg n147 (7 : Fin 32) = v146 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo8 : reg n147 (8 : Fin 32) = v130 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo9 : reg n147 (9 : Fin 32) = v110 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo10 : reg n147 a0 = v145 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo11 : reg n147 a1 = v144 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo12 : reg n147 a2 = v136 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo13 : reg n147 a3 = v120 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo14 : reg n147 a4 = v147 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo15 : reg n147 a5 = v143 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo16 : reg n147 a6 = v23 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo17 : reg n147 a7 = v30 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo18 : reg n147 (18 : Fin 32) = v75 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo19 : reg n147 (19 : Fin 32) = v53 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo20 : reg n147 (20 : Fin 32) = v140 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo21 : reg n147 (21 : Fin 32) = v36 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo22 : reg n147 (22 : Fin 32) = v118 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo23 : reg n147 (23 : Fin 32) = v138 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo24 : reg n147 (24 : Fin 32) = v8 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo25 : reg n147 (25 : Fin 32) = v141 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo26 : reg n147 (26 : Fin 32) = v133 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo27 : reg n147 (27 : Fin 32) = v142 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo28 : reg n147 (28 : Fin 32) = v22 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo29 : reg n147 (29 : Fin 32) = v7 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo30 : reg n147 (30 : Fin 32) = v54 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have qo31 : reg n147 (31 : Fin 32) = v42 := by rw [u147.regs]; simp +decide only [upd, ↓reduceIte, hz0, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q28, q29, q30, q31]
  have soC : memLoad32 Mm139 (F + 0xC) = G21 := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0xC) 4 from sep_offsets F (c := 176) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0xC) 4 from sep_offsets F (c := 184) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xC) 4 from sep_offsets F (c := 188) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM125, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0xC) 4 from sep_offsets F (c := 292) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xC) 4 from sep_offsets F (c := 280) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM121, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xC) 4 from sep_offsets F (c := 232) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slC]
  have so10 : memLoad32 Mm139 (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0x10) 4 from sep_offsets F (c := 176) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x10) 4 from sep_offsets F (c := 184) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x10) 4 from sep_offsets F (c := 188) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM125, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x10) 4 from sep_offsets F (c := 292) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x10) 4 from sep_offsets F (c := 280) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM121, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x10) 4 from sep_offsets F (c := 232) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have soB0 : memLoad32 Mm139 (F + 0xB0) = v16 := by
    rw [← hM139, memLoad32_store32_same]
  have soB4 : memLoad32 Mm139 (F + 0xB4) = v15 := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0xB4) 4 from sep_offsets F (c := 176) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0xB4) 4 from sep_offsets F (c := 184) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xB4) 4 from sep_offsets F (c := 188) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM125, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0xB4) 4 from sep_offsets F (c := 292) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xB4) 4 from sep_offsets F (c := 280) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM121, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xB4) 4 from sep_offsets F (c := 232) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), slB4]
  have soB8 : memLoad32 Mm139 (F + 0xB8) = v136 := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0xB8) 4 from sep_offsets F (c := 176) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_same]
  have soBC : memLoad32 Mm139 (F + 0xBC) = v120 := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0xBC) 4 from sep_offsets F (c := 176) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0xBC) 4 from sep_offsets F (c := 184) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_same]
  have soD0 : memLoad32 Mm139 (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0xD0) 4 from sep_offsets F (c := 176) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0xD0) 4 from sep_offsets F (c := 184) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xD0) 4 from sep_offsets F (c := 188) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM125, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0xD0) 4 from sep_offsets F (c := 292) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xD0) 4 from sep_offsets F (c := 280) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM121, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xD0) 4 from sep_offsets F (c := 232) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), slD0]
  have soE8 : memLoad32 Mm139 (F + 0xE8) = v8 := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0xE8) 4 from sep_offsets F (c := 176) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0xE8) 4 from sep_offsets F (c := 184) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xE8) 4 from sep_offsets F (c := 188) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM125, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0xE8) 4 from sep_offsets F (c := 292) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xE8) 4 from sep_offsets F (c := 280) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), ← hM121, memLoad32_store32_same]
  have soEC : memLoad32 Mm139 (F + 0xEC) = v33 := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0xEC) 4 from sep_offsets F (c := 176) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0xEC) 4 from sep_offsets F (c := 184) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xEC) 4 from sep_offsets F (c := 188) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM125, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0xEC) 4 from sep_offsets F (c := 292) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xEC) 4 from sep_offsets F (c := 280) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM121, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xEC) 4 from sep_offsets F (c := 232) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soFC : memLoad32 Mm139 (F + 0xFC) = v40 := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0xFC) 4 from sep_offsets F (c := 176) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0xFC) 4 from sep_offsets F (c := 184) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xFC) 4 from sep_offsets F (c := 188) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM125, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0xFC) 4 from sep_offsets F (c := 292) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xFC) 4 from sep_offsets F (c := 280) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM121, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xFC) 4 from sep_offsets F (c := 232) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), slFC]
  have so100 : memLoad32 Mm139 (F + 0x100) = v51 := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0x100) 4 from sep_offsets F (c := 176) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x100) 4 from sep_offsets F (c := 184) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x100) 4 from sep_offsets F (c := 188) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM125, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x100) 4 from sep_offsets F (c := 292) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x100) 4 from sep_offsets F (c := 280) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM121, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x100) 4 from sep_offsets F (c := 232) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100]
  have so104 : memLoad32 Mm139 (F + 0x104) = v62 := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0x104) 4 from sep_offsets F (c := 176) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x104) 4 from sep_offsets F (c := 184) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x104) 4 from sep_offsets F (c := 188) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM125, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x104) 4 from sep_offsets F (c := 292) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x104) 4 from sep_offsets F (c := 280) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM121, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x104) 4 from sep_offsets F (c := 232) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), sl104]
  have so10C : memLoad32 Mm139 (F + 0x10C) = v31 := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0x10C) 4 from sep_offsets F (c := 176) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x10C) 4 from sep_offsets F (c := 184) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x10C) 4 from sep_offsets F (c := 188) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM125, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x10C) 4 from sep_offsets F (c := 292) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x10C) 4 from sep_offsets F (c := 280) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM121, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x10C) 4 from sep_offsets F (c := 232) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C]
  have so110 : memLoad32 Mm139 (F + 0x110) = v67 := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0x110) 4 from sep_offsets F (c := 176) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x110) 4 from sep_offsets F (c := 184) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x110) 4 from sep_offsets F (c := 188) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM125, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x110) 4 from sep_offsets F (c := 292) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x110) 4 from sep_offsets F (c := 280) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM121, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x110) 4 from sep_offsets F (c := 232) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so114 : memLoad32 Mm139 (F + 0x114) = v111 := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0x114) 4 from sep_offsets F (c := 176) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x114) 4 from sep_offsets F (c := 184) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x114) 4 from sep_offsets F (c := 188) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM125, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x114) 4 from sep_offsets F (c := 292) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x114) 4 from sep_offsets F (c := 280) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM121, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x114) 4 from sep_offsets F (c := 232) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), sl114]
  have so118 : memLoad32 Mm139 (F + 0x118) = v122 := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0x118) 4 from sep_offsets F (c := 176) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x118) 4 from sep_offsets F (c := 184) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x118) 4 from sep_offsets F (c := 188) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM125, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x118) 4 from sep_offsets F (c := 292) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_same]
  have so120 : memLoad32 Mm139 (F + 0x120) = v116 := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0x120) 4 from sep_offsets F (c := 176) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x120) 4 from sep_offsets F (c := 184) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x120) 4 from sep_offsets F (c := 188) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM125, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x120) 4 from sep_offsets F (c := 292) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM123, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x120) 4 from sep_offsets F (c := 280) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM121, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x120) 4 from sep_offsets F (c := 232) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), sl120]
  have so124 : memLoad32 Mm139 (F + 0x124) = v124 := by
    rw [← hM139, memLoad32_store32_sep (show Sep (F + 0xB0) 4 (F + 0x124) 4 from sep_offsets F (c := 176) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM137, memLoad32_store32_sep (show Sep (F + 0xB8) 4 (F + 0x124) 4 from sep_offsets F (c := 184) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM135, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x124) 4 from sep_offsets F (c := 188) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM125, memLoad32_store32_same]
  exact ⟨n147, Mm139, v120, v122, v124, v126, v127, v128, v129, v130, v131, v132, v133, v134, v136, v138, v140, v141, v142, v143, v144, v145, v146, v147, (.cons d120 (.cons d121 (.cons d122 (.cons d123 (.cons d124 (.cons d125 (.cons d126 (.cons d127 (.cons d128 (.cons d129 (.cons d130 (.cons d131 (.cons d132 (.cons d133 (.cons d134 (.cons d135 (.cons d136 (.cons d137 (.cons d138 (.cons d139 (.cons d140 (.cons d141 (.cons d142 (.cons d143 (.cons d144 (.cons d145 (.cons d146 (.single d147)))))))))))))))))))))))))))), u147.self, hc139, fr139, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, soB0, soB4, soB8, soBC, soD0, soE8, soEC, soFC, so100, so104, so10C, so110, so114, so118, so120, so124, hv120, hv122, hv124, hv126, hv127, hv128, hv129, hv130, hv131, hv132, hv133, hv134, hv136, hv138, hv140, hv141, hv142, hv143, hv144, hv145, hv146, hv147⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g4 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v8 v15 v16 v19 v22 v23 v30 v31 v33 v36 v40 v42 v51 v53 v54 v62 v67 v75 v87 v110 v111 v116 v118 v120 v122 v124 v130 v132 v133 v136 v138 v140 v141 v142 v143 v144 v145 v146 v147 : Word}
    (s : St Mi B n 0x368 (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v132)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v19)
    (q6 : reg n (6 : Fin 32) = v87)
    (q7 : reg n (7 : Fin 32) = v146)
    (q8 : reg n (8 : Fin 32) = v130)
    (q9 : reg n (9 : Fin 32) = v110)
    (q10 : reg n a0 = v145)
    (q11 : reg n a1 = v144)
    (q12 : reg n a2 = v136)
    (q13 : reg n a3 = v120)
    (q14 : reg n a4 = v147)
    (q15 : reg n a5 = v143)
    (q16 : reg n a6 = v23)
    (q17 : reg n a7 = v30)
    (q18 : reg n (18 : Fin 32) = v75)
    (q19 : reg n (19 : Fin 32) = v53)
    (q20 : reg n (20 : Fin 32) = v140)
    (q21 : reg n (21 : Fin 32) = v36)
    (q22 : reg n (22 : Fin 32) = v118)
    (q23 : reg n (23 : Fin 32) = v138)
    (q24 : reg n (24 : Fin 32) = v8)
    (q25 : reg n (25 : Fin 32) = v141)
    (q26 : reg n (26 : Fin 32) = v133)
    (q27 : reg n (27 : Fin 32) = v142)
    (q28 : reg n (28 : Fin 32) = v22)
    (q29 : reg n (29 : Fin 32) = v7)
    (q30 : reg n (30 : Fin 32) = v54)
    (q31 : reg n (31 : Fin 32) = v42)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (slB0 : memLoad32 Mi (F + 0xB0) = v16)
    (slB4 : memLoad32 Mi (F + 0xB4) = v15)
    (slB8 : memLoad32 Mi (F + 0xB8) = v136)
    (slBC : memLoad32 Mi (F + 0xBC) = v120)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v149 v150 v151 v152 v153 v154 v155 v156 v157 v158 v159 : Word),
      Steps n n' ∧
      St M' B n' 0x38C (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v132 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v19 ∧
      reg n' (6 : Fin 32) = v87 ∧
      reg n' (7 : Fin 32) = v159 ∧
      reg n' (8 : Fin 32) = v153 ∧
      reg n' (9 : Fin 32) = v110 ∧
      reg n' a0 = v158 ∧
      reg n' a1 = v156 ∧
      reg n' a2 = v152 ∧
      reg n' a3 = v120 ∧
      reg n' a4 = v147 ∧
      reg n' a5 = v143 ∧
      reg n' a6 = v23 ∧
      reg n' a7 = v30 ∧
      reg n' (18 : Fin 32) = v75 ∧
      reg n' (19 : Fin 32) = v53 ∧
      reg n' (20 : Fin 32) = v157 ∧
      reg n' (21 : Fin 32) = v36 ∧
      reg n' (22 : Fin 32) = v118 ∧
      reg n' (23 : Fin 32) = v154 ∧
      reg n' (24 : Fin 32) = v8 ∧
      reg n' (25 : Fin 32) = v155 ∧
      reg n' (26 : Fin 32) = v133 ∧
      reg n' (27 : Fin 32) = v142 ∧
      reg n' (28 : Fin 32) = v22 ∧
      reg n' (29 : Fin 32) = v7 ∧
      reg n' (30 : Fin 32) = v151 ∧
      reg n' (31 : Fin 32) = v150 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0xB0) = v16 ∧
      memLoad32 M' (F + 0xB4) = v15 ∧
      memLoad32 M' (F + 0xB8) = v136 ∧
      memLoad32 M' (F + 0xBC) = v120 ∧
      memLoad32 M' (F + 0xC0) = v147 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xE8) = v8 ∧
      memLoad32 M' (F + 0xEC) = v33 ∧
      memLoad32 M' (F + 0xFC) = v40 ∧
      memLoad32 M' (F + 0x100) = v51 ∧
      memLoad32 M' (F + 0x104) = v62 ∧
      memLoad32 M' (F + 0x10C) = v31 ∧
      memLoad32 M' (F + 0x110) = v67 ∧
      memLoad32 M' (F + 0x114) = v111 ∧
      memLoad32 M' (F + 0x118) = v122 ∧
      memLoad32 M' (F + 0x120) = v116 ∧
      memLoad32 M' (F + 0x124) = v124 ∧
      (0x1CF5D000 : Word) = v149 ∧
      aluEval .add v149 0x3ED = v150 ∧
      aluEval .and v136 v7 = v151 ∧
      aluEval .mul v151 v150 = v152 ∧
      aluEval .mulhu v151 v150 = v153 ∧
      aluEval .add v138 v145 = v154 ∧
      aluEval .add v141 v142 = v155 ∧
      aluEval .add v144 v155 = v156 ∧
      aluEval .add v140 v143 = v157 ∧
      aluEval .sltu v157 v143 = v158 ∧
      aluEval .add v146 v157 = v159 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n148, d148, u148⟩ := s.swG hc ev_at_368 (off' := 0x36A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 192) (by decide)) (a := F + 0xC0) (v := v147)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm148, hM148⟩ : ∃ M', memStore32 Mi (F + 0xC0) v147 = M' := ⟨_, rfl⟩
  rw [hM148] at u148
  have hc148 : CodeIn Mm148 B ed25519VerifyCode := by rw [← hM148]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr148 : ∀ x, Sep F 0x128 x 1 → Mm148 x = M0 x := fun x hx => by
    rw [← hM148, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n149, v149, d149, hv149, u149⟩ := u148.luiG hc148 ev_at_36a (off' := 0x36E) (by decide)
  obtain ⟨n150, v150, d150, hv150, u150⟩ := u149.aluImmG hc148 ev_at_36e (off' := 0x372) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv150
  obtain ⟨n151, v151, d151, hv151, u151⟩ := u150.aluG hc148 ev_at_372 (off' := 0x376) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv151
  obtain ⟨n152, v152, d152, hv152, u152⟩ := u151.aluG hc148 ev_at_376 (off' := 0x37A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv152
  obtain ⟨n153, v153, d153, hv153, u153⟩ := u152.aluG hc148 ev_at_37a (off' := 0x37E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv153
  obtain ⟨n154, v154, d154, hv154, u154⟩ := u153.aluG hc148 ev_at_37e (off' := 0x380) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv154
  obtain ⟨n155, v155, d155, hv155, u155⟩ := u154.aluG hc148 ev_at_380 (off' := 0x382) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv155
  obtain ⟨n156, v156, d156, hv156, u156⟩ := u155.aluG hc148 ev_at_382 (off' := 0x384) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv156
  obtain ⟨n157, v157, d157, hv157, u157⟩ := u156.aluG hc148 ev_at_384 (off' := 0x386) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv157
  obtain ⟨n158, v158, d158, hv158, u158⟩ := u157.aluG hc148 ev_at_386 (off' := 0x38A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv158
  obtain ⟨n159, v159, d159, hv159, u159⟩ := u158.aluG hc148 ev_at_38a (off' := 0x38C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv159
  have qo1 : reg n159 ra = v132 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n159 sp = F := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n159 (3 : Fin 32) = G3 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n159 (4 : Fin 32) = G4 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n159 (5 : Fin 32) = v19 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n159 (6 : Fin 32) = v87 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n159 (7 : Fin 32) = v159 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n159 (8 : Fin 32) = v153 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n159 (9 : Fin 32) = v110 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n159 a0 = v158 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n159 a1 = v156 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n159 a2 = v152 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n159 a3 = v120 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n159 a4 = v147 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n159 a5 = v143 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n159 a6 = v23 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n159 a7 = v30 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n159 (18 : Fin 32) = v75 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n159 (19 : Fin 32) = v53 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n159 (20 : Fin 32) = v157 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n159 (21 : Fin 32) = v36 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n159 (22 : Fin 32) = v118 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n159 (23 : Fin 32) = v154 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n159 (24 : Fin 32) = v8 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n159 (25 : Fin 32) = v155 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n159 (26 : Fin 32) = v133 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n159 (27 : Fin 32) = v142 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n159 (28 : Fin 32) = v22 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n159 (29 : Fin 32) = v7 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n159 (30 : Fin 32) = v151 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n159 (31 : Fin 32) = v150 := by rw [u159.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mm148 (F + 0xC) = G21 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xC) 4 from sep_offsets F (c := 192) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slC]
  have so10 : memLoad32 Mm148 (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x10) 4 from sep_offsets F (c := 192) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have soB0 : memLoad32 Mm148 (F + 0xB0) = v16 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xB0) 4 from sep_offsets F (c := 192) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), slB0]
  have soB4 : memLoad32 Mm148 (F + 0xB4) = v15 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xB4) 4 from sep_offsets F (c := 192) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), slB4]
  have soB8 : memLoad32 Mm148 (F + 0xB8) = v136 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xB8) 4 from sep_offsets F (c := 192) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), slB8]
  have soBC : memLoad32 Mm148 (F + 0xBC) = v120 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xBC) 4 from sep_offsets F (c := 192) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), slBC]
  have soC0 : memLoad32 Mm148 (F + 0xC0) = v147 := by
    rw [← hM148, memLoad32_store32_same]
  have soD0 : memLoad32 Mm148 (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xD0) 4 from sep_offsets F (c := 192) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), slD0]
  have soE8 : memLoad32 Mm148 (F + 0xE8) = v8 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xE8) 4 from sep_offsets F (c := 192) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), slE8]
  have soEC : memLoad32 Mm148 (F + 0xEC) = v33 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xEC) 4 from sep_offsets F (c := 192) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soFC : memLoad32 Mm148 (F + 0xFC) = v40 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0xFC) 4 from sep_offsets F (c := 192) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), slFC]
  have so100 : memLoad32 Mm148 (F + 0x100) = v51 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x100) 4 from sep_offsets F (c := 192) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100]
  have so104 : memLoad32 Mm148 (F + 0x104) = v62 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x104) 4 from sep_offsets F (c := 192) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), sl104]
  have so10C : memLoad32 Mm148 (F + 0x10C) = v31 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x10C) 4 from sep_offsets F (c := 192) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C]
  have so110 : memLoad32 Mm148 (F + 0x110) = v67 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x110) 4 from sep_offsets F (c := 192) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so114 : memLoad32 Mm148 (F + 0x114) = v111 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x114) 4 from sep_offsets F (c := 192) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), sl114]
  have so118 : memLoad32 Mm148 (F + 0x118) = v122 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x118) 4 from sep_offsets F (c := 192) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), sl118]
  have so120 : memLoad32 Mm148 (F + 0x120) = v116 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x120) 4 from sep_offsets F (c := 192) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), sl120]
  have so124 : memLoad32 Mm148 (F + 0x124) = v124 := by
    rw [← hM148, memLoad32_store32_sep (show Sep (F + 0xC0) 4 (F + 0x124) 4 from sep_offsets F (c := 192) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), sl124]
  exact ⟨n159, Mm148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, (.cons d148 (.cons d149 (.cons d150 (.cons d151 (.cons d152 (.cons d153 (.cons d154 (.cons d155 (.cons d156 (.cons d157 (.cons d158 (.single d159)))))))))))), u159.self, hc148, fr148, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, soB0, soB4, soB8, soBC, soC0, soD0, soE8, soEC, soFC, so100, so104, so10C, so110, so114, so118, so120, so124, hv149, hv150, hv151, hv152, hv153, hv154, hv155, hv156, hv157, hv158, hv159⟩

end C3.RV32
