import C3BootProofs.Proofs.P256ScalarDecode

/-! # P-256's `Scalar::mul`, values, part 0

Each lemma proves one value the code holds in words from its instructions' facts. `scripts/gen-p256-scalar.py` writes this file. -/

namespace C3.RV32

open C3.Image

theorem psm_v_P1h {v0 v5 : Word}
    (t5 : v5.toNat = v0.toNat * 4007631870 / 2 ^ 32) :
    v5.toNat = (v0.toNat * 4007631870) / 2 ^ 32 := by
  have := v0.isLt; have := v5.isLt
  generalize v0.toNat = n0 at *
  generalize v5.toNat = n5 at *
  omega

theorem psm_v_P2 {v0 v5 v6 v14 v22 v24 v26 : Word}
    (t6 : v6.toNat = v0.toNat * 19922309 % 2 ^ 32)
    (t14 : v14.toNat = v0.toNat * 19922309 / 2 ^ 32)
    (t22 : v22.toNat = (v6.toNat + v5.toNat) % 2 ^ 32)
    (t24 : v22.toNat + 2 ^ 32 * v24.toNat = v6.toNat + v5.toNat)
    (t26 : v26.toNat = (v24.toNat + v14.toNat) % 2 ^ 32) :
    v22.toNat + 2 ^ 32 * v26.toNat = v0.toNat * 19922309 + v5.toNat := by
  have := v0.isLt; have := v5.isLt; have := v6.isLt; have := v14.isLt; have := v22.isLt; have := v24.isLt; have := v26.isLt
  generalize v0.toNat = n0 at *
  generalize v5.toNat = n5 at *
  generalize v6.toNat = n6 at *
  generalize v14.toNat = n14 at *
  generalize v22.toNat = n22 at *
  generalize v24.toNat = n24 at *
  generalize v26.toNat = n26 at *
  first
    | omega
    | (obtain ⟨qt6, et6⟩ := mod_q t6; clear t6; obtain ⟨qt22, et22⟩ := mod_q t22; clear t22; omega)

theorem psm_v_P2l {v0 v5 v6 v22 v26 : Word}
    (t6 : v6.toNat = v0.toNat * 19922309 % 2 ^ 32)
    (t22 : v22.toNat = (v6.toNat + v5.toNat) % 2 ^ 32)
    (wP2 : v22.toNat + 2 ^ 32 * v26.toNat = v0.toNat * 19922309 + v5.toNat) :
    v22.toNat = (v22.toNat + 2 ^ 32 * v26.toNat) % 2 ^ 32 := by
  have := v0.isLt; have := v5.isLt; have := v6.isLt; have := v22.isLt; have := v26.isLt
  generalize v0.toNat = n0 at *
  generalize v5.toNat = n5 at *
  generalize v6.toNat = n6 at *
  generalize v22.toNat = n22 at *
  generalize v26.toNat = n26 at *
  first
    | omega
    | (obtain ⟨qt6, et6⟩ := mod_q t6; clear t6; obtain ⟨qt22, et22⟩ := mod_q t22; clear t22; omega)

theorem psm_v_P2h {v0 v5 v6 v14 v22 v24 v26 : Word}
    (t14 : v14.toNat = v0.toNat * 19922309 / 2 ^ 32)
    (t24 : v22.toNat + 2 ^ 32 * v24.toNat = v6.toNat + v5.toNat)
    (t26 : v26.toNat = (v24.toNat + v14.toNat) % 2 ^ 32)
    (wP2 : v22.toNat + 2 ^ 32 * v26.toNat = v0.toNat * 19922309 + v5.toNat) :
    v26.toNat = (v22.toNat + 2 ^ 32 * v26.toNat) / 2 ^ 32 := by
  have := v0.isLt; have := v5.isLt; have := v6.isLt; have := v14.isLt; have := v22.isLt; have := v24.isLt; have := v26.isLt
  generalize v0.toNat = n0 at *
  generalize v5.toNat = n5 at *
  generalize v6.toNat = n6 at *
  generalize v14.toNat = n14 at *
  generalize v22.toNat = n22 at *
  generalize v24.toNat = n24 at *
  generalize v26.toNat = n26 at *
  first
    | omega
    | (obtain ⟨qt26, et26⟩ := mod_q t26; clear t26; omega)

theorem psm_v_P3 {v0 v16 v20 v26 v28 v30 v32 : Word}
    (t16 : v16.toNat = v0.toNat * 3743050785 % 2 ^ 32)
    (t20 : v20.toNat = v0.toNat * 3743050785 / 2 ^ 32)
    (t28 : v28.toNat = (v16.toNat + v26.toNat) % 2 ^ 32)
    (t30 : v28.toNat + 2 ^ 32 * v30.toNat = v16.toNat + v26.toNat)
    (t32 : v32.toNat = (v30.toNat + v20.toNat) % 2 ^ 32) :
    v28.toNat + 2 ^ 32 * v32.toNat = v0.toNat * 3743050785 + v26.toNat := by
  have := v0.isLt; have := v16.isLt; have := v20.isLt; have := v26.isLt; have := v28.isLt; have := v30.isLt; have := v32.isLt
  generalize v0.toNat = n0 at *
  generalize v16.toNat = n16 at *
  generalize v20.toNat = n20 at *
  generalize v26.toNat = n26 at *
  generalize v28.toNat = n28 at *
  generalize v30.toNat = n30 at *
  generalize v32.toNat = n32 at *
  first
    | omega
    | (obtain ⟨qt16, et16⟩ := mod_q t16; clear t16; obtain ⟨qt28, et28⟩ := mod_q t28; clear t28; omega)

theorem psm_v_P3l {v0 v16 v26 v28 v32 : Word}
    (t16 : v16.toNat = v0.toNat * 3743050785 % 2 ^ 32)
    (t28 : v28.toNat = (v16.toNat + v26.toNat) % 2 ^ 32)
    (wP3 : v28.toNat + 2 ^ 32 * v32.toNat = v0.toNat * 3743050785 + v26.toNat) :
    v28.toNat = (v28.toNat + 2 ^ 32 * v32.toNat) % 2 ^ 32 := by
  have := v0.isLt; have := v16.isLt; have := v26.isLt; have := v28.isLt; have := v32.isLt
  generalize v0.toNat = n0 at *
  generalize v16.toNat = n16 at *
  generalize v26.toNat = n26 at *
  generalize v28.toNat = n28 at *
  generalize v32.toNat = n32 at *
  first
    | omega
    | (obtain ⟨qt16, et16⟩ := mod_q t16; clear t16; obtain ⟨qt28, et28⟩ := mod_q t28; clear t28; omega)

theorem psm_v_P3h {v0 v16 v20 v26 v28 v30 v32 : Word}
    (t20 : v20.toNat = v0.toNat * 3743050785 / 2 ^ 32)
    (t30 : v28.toNat + 2 ^ 32 * v30.toNat = v16.toNat + v26.toNat)
    (t32 : v32.toNat = (v30.toNat + v20.toNat) % 2 ^ 32)
    (wP3 : v28.toNat + 2 ^ 32 * v32.toNat = v0.toNat * 3743050785 + v26.toNat) :
    v32.toNat = (v28.toNat + 2 ^ 32 * v32.toNat) / 2 ^ 32 := by
  have := v0.isLt; have := v16.isLt; have := v20.isLt; have := v26.isLt; have := v28.isLt; have := v30.isLt; have := v32.isLt
  generalize v0.toNat = n0 at *
  generalize v16.toNat = n16 at *
  generalize v20.toNat = n20 at *
  generalize v26.toNat = n26 at *
  generalize v28.toNat = n28 at *
  generalize v30.toNat = n30 at *
  generalize v32.toNat = n32 at *
  first
    | omega
    | (obtain ⟨qt32, et32⟩ := mod_q t32; clear t32; omega)

theorem psm_v_P4 {v0 v21 v23 v32 v34 v36 v38 : Word}
    (t21 : v21.toNat = v0.toNat * 1125713234 % 2 ^ 32)
    (t23 : v23.toNat = v0.toNat * 1125713234 / 2 ^ 32)
    (t34 : v34.toNat = (v21.toNat + v32.toNat) % 2 ^ 32)
    (t36 : v34.toNat + 2 ^ 32 * v36.toNat = v21.toNat + v32.toNat)
    (t38 : v38.toNat = (v36.toNat + v23.toNat) % 2 ^ 32) :
    v34.toNat + 2 ^ 32 * v38.toNat = v0.toNat * 1125713234 + v32.toNat := by
  have := v0.isLt; have := v21.isLt; have := v23.isLt; have := v32.isLt; have := v34.isLt; have := v36.isLt; have := v38.isLt
  generalize v0.toNat = n0 at *
  generalize v21.toNat = n21 at *
  generalize v23.toNat = n23 at *
  generalize v32.toNat = n32 at *
  generalize v34.toNat = n34 at *
  generalize v36.toNat = n36 at *
  generalize v38.toNat = n38 at *
  first
    | omega
    | (obtain ⟨qt21, et21⟩ := mod_q t21; clear t21; obtain ⟨qt34, et34⟩ := mod_q t34; clear t34; omega)

theorem psm_v_P4l {v0 v21 v32 v34 v38 : Word}
    (t21 : v21.toNat = v0.toNat * 1125713234 % 2 ^ 32)
    (t34 : v34.toNat = (v21.toNat + v32.toNat) % 2 ^ 32)
    (wP4 : v34.toNat + 2 ^ 32 * v38.toNat = v0.toNat * 1125713234 + v32.toNat) :
    v34.toNat = (v34.toNat + 2 ^ 32 * v38.toNat) % 2 ^ 32 := by
  have := v0.isLt; have := v21.isLt; have := v32.isLt; have := v34.isLt; have := v38.isLt
  generalize v0.toNat = n0 at *
  generalize v21.toNat = n21 at *
  generalize v32.toNat = n32 at *
  generalize v34.toNat = n34 at *
  generalize v38.toNat = n38 at *
  first
    | omega
    | (obtain ⟨qt21, et21⟩ := mod_q t21; clear t21; obtain ⟨qt34, et34⟩ := mod_q t34; clear t34; omega)

theorem psm_v_P4h {v0 v21 v23 v32 v34 v36 v38 : Word}
    (t23 : v23.toNat = v0.toNat * 1125713234 / 2 ^ 32)
    (t36 : v34.toNat + 2 ^ 32 * v36.toNat = v21.toNat + v32.toNat)
    (t38 : v38.toNat = (v36.toNat + v23.toNat) % 2 ^ 32)
    (wP4 : v34.toNat + 2 ^ 32 * v38.toNat = v0.toNat * 1125713234 + v32.toNat) :
    v38.toNat = (v34.toNat + 2 ^ 32 * v38.toNat) / 2 ^ 32 := by
  have := v0.isLt; have := v21.isLt; have := v23.isLt; have := v32.isLt; have := v34.isLt; have := v36.isLt; have := v38.isLt
  generalize v0.toNat = n0 at *
  generalize v21.toNat = n21 at *
  generalize v23.toNat = n23 at *
  generalize v32.toNat = n32 at *
  generalize v34.toNat = n34 at *
  generalize v36.toNat = n36 at *
  generalize v38.toNat = n38 at *
  first
    | omega
    | (obtain ⟨qt38, et38⟩ := mod_q t38; clear t38; omega)

theorem psm_v_P5 {v0 v25 v38 v40 v42 v44 : Word}
    (t25 : v25.toNat = v0.toNat * 4294967295 / 2 ^ 32 ∧ v25.toNat + (v0.toNat + 4294967295) / 4294967296 = v0.toNat)
    (t40 : v40.toNat = (v38.toNat + 2 ^ 32 - v0.toNat) % 2 ^ 32)
    (t42 : (v40.toNat < v38.toNat ∧ v42.toNat = 1) ∨ (v38.toNat ≤ v40.toNat ∧ v42.toNat = 0))
    (t44 : v44.toNat = (v42.toNat + v25.toNat) % 2 ^ 32) :
    v40.toNat + 2 ^ 32 * v44.toNat = v0.toNat * 4294967295 + v38.toNat := by
  have := v0.isLt; have := v25.isLt; have := v38.isLt; have := v40.isLt; have := v42.isLt; have := v44.isLt
  generalize v0.toNat = n0 at *
  generalize v25.toNat = n25 at *
  generalize v38.toNat = n38 at *
  generalize v40.toNat = n40 at *
  generalize v42.toNat = n42 at *
  generalize v44.toNat = n44 at *
  first
    | omega
    | (obtain ⟨t25a, t25b⟩ := t25; rcases Nat.eq_zero_or_pos n0 with _ | _ <;> rcases t42 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t25a, t25b⟩ := t25; obtain ⟨qt40, et40⟩ := mod_q t40; clear t40; omega)
    | (obtain ⟨t25a, t25b⟩ := t25; obtain ⟨qt40, et40⟩ := mod_q t40; clear t40; rcases Nat.eq_zero_or_pos n0 with _ | _ <;> rcases t42 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P5l {v0 v38 v40 v44 : Word}
    (t40 : v40.toNat = (v38.toNat + 2 ^ 32 - v0.toNat) % 2 ^ 32)
    (wP5 : v40.toNat + 2 ^ 32 * v44.toNat = v0.toNat * 4294967295 + v38.toNat) :
    v40.toNat = (v40.toNat + 2 ^ 32 * v44.toNat) % 2 ^ 32 := by
  have := v0.isLt; have := v38.isLt; have := v40.isLt; have := v44.isLt
  generalize v0.toNat = n0 at *
  generalize v38.toNat = n38 at *
  generalize v40.toNat = n40 at *
  generalize v44.toNat = n44 at *
  first
    | omega
    | (obtain ⟨qt40, et40⟩ := mod_q t40; clear t40; omega)

theorem psm_v_P5h {v0 v25 v38 v40 v42 v44 : Word}
    (t25 : v25.toNat = v0.toNat * 4294967295 / 2 ^ 32 ∧ v25.toNat + (v0.toNat + 4294967295) / 4294967296 = v0.toNat)
    (t42 : (v40.toNat < v38.toNat ∧ v42.toNat = 1) ∨ (v38.toNat ≤ v40.toNat ∧ v42.toNat = 0))
    (t44 : v44.toNat = (v42.toNat + v25.toNat) % 2 ^ 32)
    (wP5 : v40.toNat + 2 ^ 32 * v44.toNat = v0.toNat * 4294967295 + v38.toNat) :
    v44.toNat = (v40.toNat + 2 ^ 32 * v44.toNat) / 2 ^ 32 := by
  have := v0.isLt; have := v25.isLt; have := v38.isLt; have := v40.isLt; have := v42.isLt; have := v44.isLt
  generalize v0.toNat = n0 at *
  generalize v25.toNat = n25 at *
  generalize v38.toNat = n38 at *
  generalize v40.toNat = n40 at *
  generalize v42.toNat = n42 at *
  generalize v44.toNat = n44 at *
  first
    | omega
    | (obtain ⟨t25a, t25b⟩ := t25; rcases Nat.eq_zero_or_pos n0 with _ | _ <;> rcases t42 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t25a, t25b⟩ := t25; obtain ⟨qt44, et44⟩ := mod_q t44; clear t44; omega)
    | (obtain ⟨t25a, t25b⟩ := t25; obtain ⟨qt44, et44⟩ := mod_q t44; clear t44; rcases Nat.eq_zero_or_pos n0 with _ | _ <;> rcases t42 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P6 {v0 v27 v29 v44 v46 v48 v50 : Word}
    (t27 : v27.toNat = v0.toNat * 4294967294 / 2 ^ 32 ∧ v27.toNat + (2 * v0.toNat + 4294967295) / 4294967296 = v0.toNat)
    (t29 : v29.toNat = (v0.toNat + v0.toNat) % 2 ^ 32)
    (t46 : v46.toNat = (v44.toNat + 2 ^ 32 - v29.toNat) % 2 ^ 32)
    (t48 : (v46.toNat < v44.toNat ∧ v48.toNat = 1) ∨ (v44.toNat ≤ v46.toNat ∧ v48.toNat = 0))
    (t50 : v50.toNat = (v48.toNat + v27.toNat) % 2 ^ 32) :
    v46.toNat + 2 ^ 32 * v50.toNat = v0.toNat * 4294967294 + v44.toNat := by
  have := v0.isLt; have := v27.isLt; have := v29.isLt; have := v44.isLt; have := v46.isLt; have := v48.isLt; have := v50.isLt
  generalize v0.toNat = n0 at *
  generalize v27.toNat = n27 at *
  generalize v29.toNat = n29 at *
  generalize v44.toNat = n44 at *
  generalize v46.toNat = n46 at *
  generalize v48.toNat = n48 at *
  generalize v50.toNat = n50 at *
  first
    | omega
    | (obtain ⟨t27a, t27b⟩ := t27; rcases (by omega : n0 = 0 ∨ (0 < n0 ∧ n0 ≤ 2147483648) ∨ 2147483648 < n0) with _ | _ | _ <;> rcases t48 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t27a, t27b⟩ := t27; obtain ⟨qt29, et29⟩ := mod_q t29; clear t29; obtain ⟨qt46, et46⟩ := mod_q t46; clear t46; omega)
    | (obtain ⟨t27a, t27b⟩ := t27; obtain ⟨qt29, et29⟩ := mod_q t29; clear t29; obtain ⟨qt46, et46⟩ := mod_q t46; clear t46; rcases (by omega : n0 = 0 ∨ (0 < n0 ∧ n0 ≤ 2147483648) ∨ 2147483648 < n0) with _ | _ | _ <;> rcases t48 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P6l {v0 v29 v44 v46 v50 : Word}
    (t29 : v29.toNat = (v0.toNat + v0.toNat) % 2 ^ 32)
    (t46 : v46.toNat = (v44.toNat + 2 ^ 32 - v29.toNat) % 2 ^ 32)
    (wP6 : v46.toNat + 2 ^ 32 * v50.toNat = v0.toNat * 4294967294 + v44.toNat) :
    v46.toNat = (v46.toNat + 2 ^ 32 * v50.toNat) % 2 ^ 32 := by
  have := v0.isLt; have := v29.isLt; have := v44.isLt; have := v46.isLt; have := v50.isLt
  generalize v0.toNat = n0 at *
  generalize v29.toNat = n29 at *
  generalize v44.toNat = n44 at *
  generalize v46.toNat = n46 at *
  generalize v50.toNat = n50 at *
  first
    | omega
    | (obtain ⟨qt29, et29⟩ := mod_q t29; clear t29; obtain ⟨qt46, et46⟩ := mod_q t46; clear t46; omega)

theorem psm_v_P6h {v0 v27 v44 v46 v48 v50 : Word}
    (t27 : v27.toNat = v0.toNat * 4294967294 / 2 ^ 32 ∧ v27.toNat + (2 * v0.toNat + 4294967295) / 4294967296 = v0.toNat)
    (t48 : (v46.toNat < v44.toNat ∧ v48.toNat = 1) ∨ (v44.toNat ≤ v46.toNat ∧ v48.toNat = 0))
    (t50 : v50.toNat = (v48.toNat + v27.toNat) % 2 ^ 32)
    (wP6 : v46.toNat + 2 ^ 32 * v50.toNat = v0.toNat * 4294967294 + v44.toNat) :
    v50.toNat = (v46.toNat + 2 ^ 32 * v50.toNat) / 2 ^ 32 := by
  have := v0.isLt; have := v27.isLt; have := v44.isLt; have := v46.isLt; have := v48.isLt; have := v50.isLt
  generalize v0.toNat = n0 at *
  generalize v27.toNat = n27 at *
  generalize v44.toNat = n44 at *
  generalize v46.toNat = n46 at *
  generalize v48.toNat = n48 at *
  generalize v50.toNat = n50 at *
  first
    | omega
    | (obtain ⟨t27a, t27b⟩ := t27; rcases (by omega : n0 = 0 ∨ (0 < n0 ∧ n0 ≤ 2147483648) ∨ 2147483648 < n0) with _ | _ | _ <;> rcases t48 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t27a, t27b⟩ := t27; obtain ⟨qt50, et50⟩ := mod_q t50; clear t50; omega)
    | (obtain ⟨t27a, t27b⟩ := t27; obtain ⟨qt50, et50⟩ := mod_q t50; clear t50; rcases (by omega : n0 = 0 ∨ (0 < n0 ∧ n0 ≤ 2147483648) ∨ 2147483648 < n0) with _ | _ | _ <;> rcases t48 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P7 {v0 v25 v50 v52 v56 v58 : Word}
    (t25 : v25.toNat = v0.toNat * 4294967295 / 2 ^ 32 ∧ v25.toNat + (v0.toNat + 4294967295) / 4294967296 = v0.toNat)
    (t52 : v52.toNat = (v50.toNat + 2 ^ 32 - v0.toNat) % 2 ^ 32)
    (t56 : (v52.toNat < v50.toNat ∧ v56.toNat = 1) ∨ (v50.toNat ≤ v52.toNat ∧ v56.toNat = 0))
    (t58 : v58.toNat = (v25.toNat + v56.toNat) % 2 ^ 32) :
    v52.toNat + 2 ^ 32 * v58.toNat = v0.toNat * 4294967295 + v50.toNat := by
  have := v0.isLt; have := v25.isLt; have := v50.isLt; have := v52.isLt; have := v56.isLt; have := v58.isLt
  generalize v0.toNat = n0 at *
  generalize v25.toNat = n25 at *
  generalize v50.toNat = n50 at *
  generalize v52.toNat = n52 at *
  generalize v56.toNat = n56 at *
  generalize v58.toNat = n58 at *
  first
    | omega
    | (obtain ⟨t25a, t25b⟩ := t25; rcases Nat.eq_zero_or_pos n0 with _ | _ <;> rcases t56 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t25a, t25b⟩ := t25; obtain ⟨qt52, et52⟩ := mod_q t52; clear t52; omega)
    | (obtain ⟨t25a, t25b⟩ := t25; obtain ⟨qt52, et52⟩ := mod_q t52; clear t52; rcases Nat.eq_zero_or_pos n0 with _ | _ <;> rcases t56 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P7l {v0 v50 v52 v58 : Word}
    (t52 : v52.toNat = (v50.toNat + 2 ^ 32 - v0.toNat) % 2 ^ 32)
    (wP7 : v52.toNat + 2 ^ 32 * v58.toNat = v0.toNat * 4294967295 + v50.toNat) :
    v52.toNat = (v52.toNat + 2 ^ 32 * v58.toNat) % 2 ^ 32 := by
  have := v0.isLt; have := v50.isLt; have := v52.isLt; have := v58.isLt
  generalize v0.toNat = n0 at *
  generalize v50.toNat = n50 at *
  generalize v52.toNat = n52 at *
  generalize v58.toNat = n58 at *
  first
    | omega
    | (obtain ⟨qt52, et52⟩ := mod_q t52; clear t52; omega)

theorem psm_v_P7h {v0 v25 v50 v52 v56 v58 : Word}
    (t25 : v25.toNat = v0.toNat * 4294967295 / 2 ^ 32 ∧ v25.toNat + (v0.toNat + 4294967295) / 4294967296 = v0.toNat)
    (t56 : (v52.toNat < v50.toNat ∧ v56.toNat = 1) ∨ (v50.toNat ≤ v52.toNat ∧ v56.toNat = 0))
    (t58 : v58.toNat = (v25.toNat + v56.toNat) % 2 ^ 32)
    (wP7 : v52.toNat + 2 ^ 32 * v58.toNat = v0.toNat * 4294967295 + v50.toNat) :
    v58.toNat = (v52.toNat + 2 ^ 32 * v58.toNat) / 2 ^ 32 := by
  have := v0.isLt; have := v25.isLt; have := v50.isLt; have := v52.isLt; have := v56.isLt; have := v58.isLt
  generalize v0.toNat = n0 at *
  generalize v25.toNat = n25 at *
  generalize v50.toNat = n50 at *
  generalize v52.toNat = n52 at *
  generalize v56.toNat = n56 at *
  generalize v58.toNat = n58 at *
  first
    | omega
    | (obtain ⟨t25a, t25b⟩ := t25; rcases Nat.eq_zero_or_pos n0 with _ | _ <;> rcases t56 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t25a, t25b⟩ := t25; obtain ⟨qt58, et58⟩ := mod_q t58; clear t58; omega)
    | (obtain ⟨t25a, t25b⟩ := t25; obtain ⟨qt58, et58⟩ := mod_q t58; clear t58; rcases Nat.eq_zero_or_pos n0 with _ | _ <;> rcases t56 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P8h {v7 v22 v31 v33 v45 v47 v49 v51 : Word}
    (t31 : v31.toNat = v7.toNat * 4007631870 / 2 ^ 32)
    (t33 : v33.toNat = v7.toNat * 4007631870 % 2 ^ 32)
    (t45 : v45.toNat = v22.toNat / 2 * 2)
    (t47 : v47.toNat = (v33.toNat + v45.toNat) % 2 ^ 32)
    (t49 : v47.toNat + 2 ^ 32 * v49.toNat = v33.toNat + v45.toNat)
    (t51 : v51.toNat = (v49.toNat + v31.toNat) % 2 ^ 32) :
    v51.toNat = (v7.toNat * 4007631870 + v22.toNat) / 2 ^ 32 := by
  have := v7.isLt; have := v22.isLt; have := v31.isLt; have := v33.isLt; have := v45.isLt; have := v47.isLt; have := v49.isLt; have := v51.isLt
  generalize v7.toNat = n7 at *
  generalize v22.toNat = n22 at *
  generalize v31.toNat = n31 at *
  generalize v33.toNat = n33 at *
  generalize v45.toNat = n45 at *
  generalize v47.toNat = n47 at *
  generalize v49.toNat = n49 at *
  generalize v51.toNat = n51 at *
  first
    | omega
    | (obtain ⟨qt33, et33⟩ := mod_q t33; clear t33; obtain ⟨qt47, et47⟩ := mod_q t47; clear t47; omega)

theorem psm_v_P9 {v7 v28 v35 v37 v51 v55 v57 v59 v60 v63 v65 : Word}
    (t35 : v35.toNat = v7.toNat * 19922309 / 2 ^ 32)
    (t37 : v37.toNat = v7.toNat * 19922309 % 2 ^ 32)
    (t55 : v55.toNat = (v37.toNat + v28.toNat) % 2 ^ 32)
    (t57 : v55.toNat + 2 ^ 32 * v57.toNat = v37.toNat + v28.toNat)
    (t59 : v59.toNat = (v57.toNat + v35.toNat) % 2 ^ 32)
    (t60 : v60.toNat = (v55.toNat + v51.toNat) % 2 ^ 32)
    (t63 : v60.toNat + 2 ^ 32 * v63.toNat = v55.toNat + v51.toNat)
    (t65 : v65.toNat = (v63.toNat + v59.toNat) % 2 ^ 32) :
    v60.toNat + 2 ^ 32 * v65.toNat = v7.toNat * 19922309 + v28.toNat + v51.toNat := by
  have := v7.isLt; have := v28.isLt; have := v35.isLt; have := v37.isLt; have := v51.isLt; have := v55.isLt; have := v57.isLt; have := v59.isLt; have := v60.isLt; have := v63.isLt; have := v65.isLt
  generalize v7.toNat = n7 at *
  generalize v28.toNat = n28 at *
  generalize v35.toNat = n35 at *
  generalize v37.toNat = n37 at *
  generalize v51.toNat = n51 at *
  generalize v55.toNat = n55 at *
  generalize v57.toNat = n57 at *
  generalize v59.toNat = n59 at *
  generalize v60.toNat = n60 at *
  generalize v63.toNat = n63 at *
  generalize v65.toNat = n65 at *
  first
    | omega
    | (obtain ⟨qt37, et37⟩ := mod_q t37; clear t37; obtain ⟨qt55, et55⟩ := mod_q t55; clear t55; obtain ⟨qt59, et59⟩ := mod_q t59; clear t59; obtain ⟨qt60, et60⟩ := mod_q t60; clear t60; omega)

theorem psm_v_P9l {v7 v28 v37 v51 v55 v60 v65 : Word}
    (t37 : v37.toNat = v7.toNat * 19922309 % 2 ^ 32)
    (t55 : v55.toNat = (v37.toNat + v28.toNat) % 2 ^ 32)
    (t60 : v60.toNat = (v55.toNat + v51.toNat) % 2 ^ 32)
    (wP9 : v60.toNat + 2 ^ 32 * v65.toNat = v7.toNat * 19922309 + v28.toNat + v51.toNat) :
    v60.toNat = (v60.toNat + 2 ^ 32 * v65.toNat) % 2 ^ 32 := by
  have := v7.isLt; have := v28.isLt; have := v37.isLt; have := v51.isLt; have := v55.isLt; have := v60.isLt; have := v65.isLt
  generalize v7.toNat = n7 at *
  generalize v28.toNat = n28 at *
  generalize v37.toNat = n37 at *
  generalize v51.toNat = n51 at *
  generalize v55.toNat = n55 at *
  generalize v60.toNat = n60 at *
  generalize v65.toNat = n65 at *
  first
    | omega
    | (obtain ⟨qt37, et37⟩ := mod_q t37; clear t37; obtain ⟨qt55, et55⟩ := mod_q t55; clear t55; obtain ⟨qt60, et60⟩ := mod_q t60; clear t60; omega)

theorem psm_v_P9h {v7 v28 v35 v37 v51 v55 v57 v59 v60 v63 v65 : Word}
    (t35 : v35.toNat = v7.toNat * 19922309 / 2 ^ 32)
    (t37 : v37.toNat = v7.toNat * 19922309 % 2 ^ 32)
    (t55 : v55.toNat = (v37.toNat + v28.toNat) % 2 ^ 32)
    (t57 : v55.toNat + 2 ^ 32 * v57.toNat = v37.toNat + v28.toNat)
    (t59 : v59.toNat = (v57.toNat + v35.toNat) % 2 ^ 32)
    (t63 : v60.toNat + 2 ^ 32 * v63.toNat = v55.toNat + v51.toNat)
    (t65 : v65.toNat = (v63.toNat + v59.toNat) % 2 ^ 32)
    (wP9 : v60.toNat + 2 ^ 32 * v65.toNat = v7.toNat * 19922309 + v28.toNat + v51.toNat) :
    v65.toNat = (v60.toNat + 2 ^ 32 * v65.toNat) / 2 ^ 32 := by
  have := v7.isLt; have := v28.isLt; have := v35.isLt; have := v37.isLt; have := v51.isLt; have := v55.isLt; have := v57.isLt; have := v59.isLt; have := v60.isLt; have := v63.isLt; have := v65.isLt
  generalize v7.toNat = n7 at *
  generalize v28.toNat = n28 at *
  generalize v35.toNat = n35 at *
  generalize v37.toNat = n37 at *
  generalize v51.toNat = n51 at *
  generalize v55.toNat = n55 at *
  generalize v57.toNat = n57 at *
  generalize v59.toNat = n59 at *
  generalize v60.toNat = n60 at *
  generalize v63.toNat = n63 at *
  generalize v65.toNat = n65 at *
  first
    | omega
    | (obtain ⟨qt37, et37⟩ := mod_q t37; clear t37; obtain ⟨qt55, et55⟩ := mod_q t55; clear t55; obtain ⟨qt59, et59⟩ := mod_q t59; clear t59; obtain ⟨qt65, et65⟩ := mod_q t65; clear t65; omega)

theorem psm_v_P10 {v7 v34 v39 v41 v61 v64 v65 v66 v67 v70 v72 : Word}
    (t39 : v39.toNat = v7.toNat * 3743050785 / 2 ^ 32)
    (t41 : v41.toNat = v7.toNat * 3743050785 % 2 ^ 32)
    (t61 : v61.toNat = (v41.toNat + v34.toNat) % 2 ^ 32)
    (t64 : v61.toNat + 2 ^ 32 * v64.toNat = v41.toNat + v34.toNat)
    (t66 : v66.toNat = (v64.toNat + v39.toNat) % 2 ^ 32)
    (t67 : v67.toNat = (v61.toNat + v65.toNat) % 2 ^ 32)
    (t70 : v67.toNat + 2 ^ 32 * v70.toNat = v61.toNat + v65.toNat)
    (t72 : v72.toNat = (v66.toNat + v70.toNat) % 2 ^ 32) :
    v67.toNat + 2 ^ 32 * v72.toNat = v7.toNat * 3743050785 + v34.toNat + v65.toNat := by
  have := v7.isLt; have := v34.isLt; have := v39.isLt; have := v41.isLt; have := v61.isLt; have := v64.isLt; have := v65.isLt; have := v66.isLt; have := v67.isLt; have := v70.isLt; have := v72.isLt
  generalize v7.toNat = n7 at *
  generalize v34.toNat = n34 at *
  generalize v39.toNat = n39 at *
  generalize v41.toNat = n41 at *
  generalize v61.toNat = n61 at *
  generalize v64.toNat = n64 at *
  generalize v65.toNat = n65 at *
  generalize v66.toNat = n66 at *
  generalize v67.toNat = n67 at *
  generalize v70.toNat = n70 at *
  generalize v72.toNat = n72 at *
  first
    | omega
    | (obtain ⟨qt41, et41⟩ := mod_q t41; clear t41; obtain ⟨qt61, et61⟩ := mod_q t61; clear t61; obtain ⟨qt66, et66⟩ := mod_q t66; clear t66; obtain ⟨qt67, et67⟩ := mod_q t67; clear t67; omega)

theorem psm_v_P10l {v7 v34 v41 v61 v65 v67 v72 : Word}
    (t41 : v41.toNat = v7.toNat * 3743050785 % 2 ^ 32)
    (t61 : v61.toNat = (v41.toNat + v34.toNat) % 2 ^ 32)
    (t67 : v67.toNat = (v61.toNat + v65.toNat) % 2 ^ 32)
    (wP10 : v67.toNat + 2 ^ 32 * v72.toNat = v7.toNat * 3743050785 + v34.toNat + v65.toNat) :
    v67.toNat = (v67.toNat + 2 ^ 32 * v72.toNat) % 2 ^ 32 := by
  have := v7.isLt; have := v34.isLt; have := v41.isLt; have := v61.isLt; have := v65.isLt; have := v67.isLt; have := v72.isLt
  generalize v7.toNat = n7 at *
  generalize v34.toNat = n34 at *
  generalize v41.toNat = n41 at *
  generalize v61.toNat = n61 at *
  generalize v65.toNat = n65 at *
  generalize v67.toNat = n67 at *
  generalize v72.toNat = n72 at *
  first
    | omega
    | (obtain ⟨qt41, et41⟩ := mod_q t41; clear t41; obtain ⟨qt61, et61⟩ := mod_q t61; clear t61; obtain ⟨qt67, et67⟩ := mod_q t67; clear t67; omega)

theorem psm_v_P10h {v7 v34 v39 v41 v61 v64 v65 v66 v67 v70 v72 : Word}
    (t39 : v39.toNat = v7.toNat * 3743050785 / 2 ^ 32)
    (t41 : v41.toNat = v7.toNat * 3743050785 % 2 ^ 32)
    (t61 : v61.toNat = (v41.toNat + v34.toNat) % 2 ^ 32)
    (t64 : v61.toNat + 2 ^ 32 * v64.toNat = v41.toNat + v34.toNat)
    (t66 : v66.toNat = (v64.toNat + v39.toNat) % 2 ^ 32)
    (t70 : v67.toNat + 2 ^ 32 * v70.toNat = v61.toNat + v65.toNat)
    (t72 : v72.toNat = (v66.toNat + v70.toNat) % 2 ^ 32)
    (wP10 : v67.toNat + 2 ^ 32 * v72.toNat = v7.toNat * 3743050785 + v34.toNat + v65.toNat) :
    v72.toNat = (v67.toNat + 2 ^ 32 * v72.toNat) / 2 ^ 32 := by
  have := v7.isLt; have := v34.isLt; have := v39.isLt; have := v41.isLt; have := v61.isLt; have := v64.isLt; have := v65.isLt; have := v66.isLt; have := v67.isLt; have := v70.isLt; have := v72.isLt
  generalize v7.toNat = n7 at *
  generalize v34.toNat = n34 at *
  generalize v39.toNat = n39 at *
  generalize v41.toNat = n41 at *
  generalize v61.toNat = n61 at *
  generalize v64.toNat = n64 at *
  generalize v65.toNat = n65 at *
  generalize v66.toNat = n66 at *
  generalize v67.toNat = n67 at *
  generalize v70.toNat = n70 at *
  generalize v72.toNat = n72 at *
  first
    | omega
    | (obtain ⟨qt41, et41⟩ := mod_q t41; clear t41; obtain ⟨qt61, et61⟩ := mod_q t61; clear t61; obtain ⟨qt66, et66⟩ := mod_q t66; clear t66; obtain ⟨qt72, et72⟩ := mod_q t72; clear t72; omega)

theorem psm_v_P11 {v7 v40 v43 v62 v71 v72 v73 v74 v75 v78 v80 : Word}
    (t43 : v43.toNat = v7.toNat * 1125713234 % 2 ^ 32)
    (t62 : v62.toNat = v7.toNat * 1125713234 / 2 ^ 32)
    (t71 : v71.toNat = (v43.toNat + v40.toNat) % 2 ^ 32)
    (t73 : v71.toNat + 2 ^ 32 * v73.toNat = v43.toNat + v40.toNat)
    (t74 : v74.toNat = (v62.toNat + v73.toNat) % 2 ^ 32)
    (t75 : v75.toNat = (v71.toNat + v72.toNat) % 2 ^ 32)
    (t78 : v75.toNat + 2 ^ 32 * v78.toNat = v71.toNat + v72.toNat)
    (t80 : v80.toNat = (v74.toNat + v78.toNat) % 2 ^ 32) :
    v75.toNat + 2 ^ 32 * v80.toNat = v7.toNat * 1125713234 + v40.toNat + v72.toNat := by
  have := v7.isLt; have := v40.isLt; have := v43.isLt; have := v62.isLt; have := v71.isLt; have := v72.isLt; have := v73.isLt; have := v74.isLt; have := v75.isLt; have := v78.isLt; have := v80.isLt
  generalize v7.toNat = n7 at *
  generalize v40.toNat = n40 at *
  generalize v43.toNat = n43 at *
  generalize v62.toNat = n62 at *
  generalize v71.toNat = n71 at *
  generalize v72.toNat = n72 at *
  generalize v73.toNat = n73 at *
  generalize v74.toNat = n74 at *
  generalize v75.toNat = n75 at *
  generalize v78.toNat = n78 at *
  generalize v80.toNat = n80 at *
  first
    | omega
    | (obtain ⟨qt43, et43⟩ := mod_q t43; clear t43; obtain ⟨qt71, et71⟩ := mod_q t71; clear t71; obtain ⟨qt74, et74⟩ := mod_q t74; clear t74; obtain ⟨qt75, et75⟩ := mod_q t75; clear t75; omega)

theorem psm_v_P11l {v7 v40 v43 v71 v72 v75 v80 : Word}
    (t43 : v43.toNat = v7.toNat * 1125713234 % 2 ^ 32)
    (t71 : v71.toNat = (v43.toNat + v40.toNat) % 2 ^ 32)
    (t75 : v75.toNat = (v71.toNat + v72.toNat) % 2 ^ 32)
    (wP11 : v75.toNat + 2 ^ 32 * v80.toNat = v7.toNat * 1125713234 + v40.toNat + v72.toNat) :
    v75.toNat = (v75.toNat + 2 ^ 32 * v80.toNat) % 2 ^ 32 := by
  have := v7.isLt; have := v40.isLt; have := v43.isLt; have := v71.isLt; have := v72.isLt; have := v75.isLt; have := v80.isLt
  generalize v7.toNat = n7 at *
  generalize v40.toNat = n40 at *
  generalize v43.toNat = n43 at *
  generalize v71.toNat = n71 at *
  generalize v72.toNat = n72 at *
  generalize v75.toNat = n75 at *
  generalize v80.toNat = n80 at *
  first
    | omega
    | (obtain ⟨qt43, et43⟩ := mod_q t43; clear t43; obtain ⟨qt71, et71⟩ := mod_q t71; clear t71; obtain ⟨qt75, et75⟩ := mod_q t75; clear t75; omega)

theorem psm_v_P11h {v7 v40 v43 v62 v71 v72 v73 v74 v75 v78 v80 : Word}
    (t43 : v43.toNat = v7.toNat * 1125713234 % 2 ^ 32)
    (t62 : v62.toNat = v7.toNat * 1125713234 / 2 ^ 32)
    (t71 : v71.toNat = (v43.toNat + v40.toNat) % 2 ^ 32)
    (t73 : v71.toNat + 2 ^ 32 * v73.toNat = v43.toNat + v40.toNat)
    (t74 : v74.toNat = (v62.toNat + v73.toNat) % 2 ^ 32)
    (t78 : v75.toNat + 2 ^ 32 * v78.toNat = v71.toNat + v72.toNat)
    (t80 : v80.toNat = (v74.toNat + v78.toNat) % 2 ^ 32)
    (wP11 : v75.toNat + 2 ^ 32 * v80.toNat = v7.toNat * 1125713234 + v40.toNat + v72.toNat) :
    v80.toNat = (v75.toNat + 2 ^ 32 * v80.toNat) / 2 ^ 32 := by
  have := v7.isLt; have := v40.isLt; have := v43.isLt; have := v62.isLt; have := v71.isLt; have := v72.isLt; have := v73.isLt; have := v74.isLt; have := v75.isLt; have := v78.isLt; have := v80.isLt
  generalize v7.toNat = n7 at *
  generalize v40.toNat = n40 at *
  generalize v43.toNat = n43 at *
  generalize v62.toNat = n62 at *
  generalize v71.toNat = n71 at *
  generalize v72.toNat = n72 at *
  generalize v73.toNat = n73 at *
  generalize v74.toNat = n74 at *
  generalize v75.toNat = n75 at *
  generalize v78.toNat = n78 at *
  generalize v80.toNat = n80 at *
  first
    | omega
    | (obtain ⟨qt43, et43⟩ := mod_q t43; clear t43; obtain ⟨qt71, et71⟩ := mod_q t71; clear t71; obtain ⟨qt74, et74⟩ := mod_q t74; clear t74; obtain ⟨qt80, et80⟩ := mod_q t80; clear t80; omega)

theorem psm_v_P12 {v7 v46 v69 v76 v79 v80 v81 v82 v84 v86 : Word}
    (t69 : v69.toNat = v7.toNat * 4294967295 / 2 ^ 32 ∧ v69.toNat + (v7.toNat + 4294967295) / 4294967296 = v7.toNat)
    (t76 : v76.toNat = (v46.toNat + 2 ^ 32 - v7.toNat) % 2 ^ 32)
    (t79 : (v76.toNat < v46.toNat ∧ v79.toNat = 1) ∨ (v46.toNat ≤ v76.toNat ∧ v79.toNat = 0))
    (t81 : v81.toNat = (v69.toNat + v79.toNat) % 2 ^ 32)
    (t82 : v82.toNat = (v76.toNat + v80.toNat) % 2 ^ 32)
    (t84 : v82.toNat + 2 ^ 32 * v84.toNat = v76.toNat + v80.toNat)
    (t86 : v86.toNat = (v81.toNat + v84.toNat) % 2 ^ 32) :
    v82.toNat + 2 ^ 32 * v86.toNat = v7.toNat * 4294967295 + v46.toNat + v80.toNat := by
  have := v7.isLt; have := v46.isLt; have := v69.isLt; have := v76.isLt; have := v79.isLt; have := v80.isLt; have := v81.isLt; have := v82.isLt; have := v84.isLt; have := v86.isLt
  generalize v7.toNat = n7 at *
  generalize v46.toNat = n46 at *
  generalize v69.toNat = n69 at *
  generalize v76.toNat = n76 at *
  generalize v79.toNat = n79 at *
  generalize v80.toNat = n80 at *
  generalize v81.toNat = n81 at *
  generalize v82.toNat = n82 at *
  generalize v84.toNat = n84 at *
  generalize v86.toNat = n86 at *
  first
    | omega
    | (obtain ⟨t69a, t69b⟩ := t69; rcases Nat.eq_zero_or_pos n7 with _ | _ <;> rcases t79 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t69a, t69b⟩ := t69; obtain ⟨qt76, et76⟩ := mod_q t76; clear t76; obtain ⟨qt81, et81⟩ := mod_q t81; clear t81; obtain ⟨qt82, et82⟩ := mod_q t82; clear t82; omega)
    | (obtain ⟨t69a, t69b⟩ := t69; obtain ⟨qt76, et76⟩ := mod_q t76; clear t76; obtain ⟨qt81, et81⟩ := mod_q t81; clear t81; obtain ⟨qt82, et82⟩ := mod_q t82; clear t82; rcases Nat.eq_zero_or_pos n7 with _ | _ <;> rcases t79 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P12l {v7 v46 v76 v80 v82 v86 : Word}
    (t76 : v76.toNat = (v46.toNat + 2 ^ 32 - v7.toNat) % 2 ^ 32)
    (t82 : v82.toNat = (v76.toNat + v80.toNat) % 2 ^ 32)
    (wP12 : v82.toNat + 2 ^ 32 * v86.toNat = v7.toNat * 4294967295 + v46.toNat + v80.toNat) :
    v82.toNat = (v82.toNat + 2 ^ 32 * v86.toNat) % 2 ^ 32 := by
  have := v7.isLt; have := v46.isLt; have := v76.isLt; have := v80.isLt; have := v82.isLt; have := v86.isLt
  generalize v7.toNat = n7 at *
  generalize v46.toNat = n46 at *
  generalize v76.toNat = n76 at *
  generalize v80.toNat = n80 at *
  generalize v82.toNat = n82 at *
  generalize v86.toNat = n86 at *
  first
    | omega
    | (obtain ⟨qt76, et76⟩ := mod_q t76; clear t76; obtain ⟨qt82, et82⟩ := mod_q t82; clear t82; omega)

theorem psm_v_P12h {v7 v46 v69 v76 v79 v80 v81 v82 v84 v86 : Word}
    (t69 : v69.toNat = v7.toNat * 4294967295 / 2 ^ 32 ∧ v69.toNat + (v7.toNat + 4294967295) / 4294967296 = v7.toNat)
    (t76 : v76.toNat = (v46.toNat + 2 ^ 32 - v7.toNat) % 2 ^ 32)
    (t79 : (v76.toNat < v46.toNat ∧ v79.toNat = 1) ∨ (v46.toNat ≤ v76.toNat ∧ v79.toNat = 0))
    (t81 : v81.toNat = (v69.toNat + v79.toNat) % 2 ^ 32)
    (t84 : v82.toNat + 2 ^ 32 * v84.toNat = v76.toNat + v80.toNat)
    (t86 : v86.toNat = (v81.toNat + v84.toNat) % 2 ^ 32)
    (wP12 : v82.toNat + 2 ^ 32 * v86.toNat = v7.toNat * 4294967295 + v46.toNat + v80.toNat) :
    v86.toNat = (v82.toNat + 2 ^ 32 * v86.toNat) / 2 ^ 32 := by
  have := v7.isLt; have := v46.isLt; have := v69.isLt; have := v76.isLt; have := v79.isLt; have := v80.isLt; have := v81.isLt; have := v82.isLt; have := v84.isLt; have := v86.isLt
  generalize v7.toNat = n7 at *
  generalize v46.toNat = n46 at *
  generalize v69.toNat = n69 at *
  generalize v76.toNat = n76 at *
  generalize v79.toNat = n79 at *
  generalize v80.toNat = n80 at *
  generalize v81.toNat = n81 at *
  generalize v82.toNat = n82 at *
  generalize v84.toNat = n84 at *
  generalize v86.toNat = n86 at *
  first
    | omega
    | (obtain ⟨t69a, t69b⟩ := t69; rcases Nat.eq_zero_or_pos n7 with _ | _ <;> rcases t79 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t69a, t69b⟩ := t69; obtain ⟨qt76, et76⟩ := mod_q t76; clear t76; obtain ⟨qt81, et81⟩ := mod_q t81; clear t81; obtain ⟨qt86, et86⟩ := mod_q t86; clear t86; omega)
    | (obtain ⟨t69a, t69b⟩ := t69; obtain ⟨qt76, et76⟩ := mod_q t76; clear t76; obtain ⟨qt81, et81⟩ := mod_q t81; clear t81; obtain ⟨qt86, et86⟩ := mod_q t86; clear t86; rcases Nat.eq_zero_or_pos n7 with _ | _ <;> rcases t79 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P13 {v7 v52 v77 v83 v85 v86 v87 v88 v89 v90 v93 : Word}
    (t77 : v77.toNat = v7.toNat * 4294967294 / 2 ^ 32 ∧ v77.toNat + (2 * v7.toNat + 4294967295) / 4294967296 = v7.toNat)
    (t83 : v83.toNat = (v7.toNat + v7.toNat) % 2 ^ 32)
    (t85 : v85.toNat = (v52.toNat + 2 ^ 32 - v83.toNat) % 2 ^ 32)
    (t87 : (v85.toNat < v52.toNat ∧ v87.toNat = 1) ∨ (v52.toNat ≤ v85.toNat ∧ v87.toNat = 0))
    (t88 : v88.toNat = (v77.toNat + v87.toNat) % 2 ^ 32)
    (t89 : v89.toNat = (v85.toNat + v86.toNat) % 2 ^ 32)
    (t90 : v89.toNat + 2 ^ 32 * v90.toNat = v85.toNat + v86.toNat)
    (t93 : v93.toNat = (v90.toNat + v88.toNat) % 2 ^ 32) :
    v89.toNat + 2 ^ 32 * v93.toNat = v7.toNat * 4294967294 + v52.toNat + v86.toNat := by
  have := v7.isLt; have := v52.isLt; have := v77.isLt; have := v83.isLt; have := v85.isLt; have := v86.isLt; have := v87.isLt; have := v88.isLt; have := v89.isLt; have := v90.isLt; have := v93.isLt
  generalize v7.toNat = n7 at *
  generalize v52.toNat = n52 at *
  generalize v77.toNat = n77 at *
  generalize v83.toNat = n83 at *
  generalize v85.toNat = n85 at *
  generalize v86.toNat = n86 at *
  generalize v87.toNat = n87 at *
  generalize v88.toNat = n88 at *
  generalize v89.toNat = n89 at *
  generalize v90.toNat = n90 at *
  generalize v93.toNat = n93 at *
  first
    | omega
    | (obtain ⟨t77a, t77b⟩ := t77; rcases (by omega : n7 = 0 ∨ (0 < n7 ∧ n7 ≤ 2147483648) ∨ 2147483648 < n7) with _ | _ | _ <;> rcases t87 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t77a, t77b⟩ := t77; obtain ⟨qt83, et83⟩ := mod_q t83; clear t83; obtain ⟨qt85, et85⟩ := mod_q t85; clear t85; obtain ⟨qt88, et88⟩ := mod_q t88; clear t88; obtain ⟨qt89, et89⟩ := mod_q t89; clear t89; omega)
    | (obtain ⟨t77a, t77b⟩ := t77; obtain ⟨qt83, et83⟩ := mod_q t83; clear t83; obtain ⟨qt85, et85⟩ := mod_q t85; clear t85; obtain ⟨qt88, et88⟩ := mod_q t88; clear t88; obtain ⟨qt89, et89⟩ := mod_q t89; clear t89; rcases (by omega : n7 = 0 ∨ (0 < n7 ∧ n7 ≤ 2147483648) ∨ 2147483648 < n7) with _ | _ | _ <;> rcases t87 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P13l {v7 v52 v83 v85 v86 v89 v93 : Word}
    (t83 : v83.toNat = (v7.toNat + v7.toNat) % 2 ^ 32)
    (t85 : v85.toNat = (v52.toNat + 2 ^ 32 - v83.toNat) % 2 ^ 32)
    (t89 : v89.toNat = (v85.toNat + v86.toNat) % 2 ^ 32)
    (wP13 : v89.toNat + 2 ^ 32 * v93.toNat = v7.toNat * 4294967294 + v52.toNat + v86.toNat) :
    v89.toNat = (v89.toNat + 2 ^ 32 * v93.toNat) % 2 ^ 32 := by
  have := v7.isLt; have := v52.isLt; have := v83.isLt; have := v85.isLt; have := v86.isLt; have := v89.isLt; have := v93.isLt
  generalize v7.toNat = n7 at *
  generalize v52.toNat = n52 at *
  generalize v83.toNat = n83 at *
  generalize v85.toNat = n85 at *
  generalize v86.toNat = n86 at *
  generalize v89.toNat = n89 at *
  generalize v93.toNat = n93 at *
  first
    | omega
    | (obtain ⟨qt83, et83⟩ := mod_q t83; clear t83; obtain ⟨qt85, et85⟩ := mod_q t85; clear t85; obtain ⟨qt89, et89⟩ := mod_q t89; clear t89; omega)

theorem psm_v_P13h {v7 v52 v77 v83 v85 v86 v87 v88 v89 v90 v93 : Word}
    (t77 : v77.toNat = v7.toNat * 4294967294 / 2 ^ 32 ∧ v77.toNat + (2 * v7.toNat + 4294967295) / 4294967296 = v7.toNat)
    (t83 : v83.toNat = (v7.toNat + v7.toNat) % 2 ^ 32)
    (t85 : v85.toNat = (v52.toNat + 2 ^ 32 - v83.toNat) % 2 ^ 32)
    (t87 : (v85.toNat < v52.toNat ∧ v87.toNat = 1) ∨ (v52.toNat ≤ v85.toNat ∧ v87.toNat = 0))
    (t88 : v88.toNat = (v77.toNat + v87.toNat) % 2 ^ 32)
    (t90 : v89.toNat + 2 ^ 32 * v90.toNat = v85.toNat + v86.toNat)
    (t93 : v93.toNat = (v90.toNat + v88.toNat) % 2 ^ 32)
    (wP13 : v89.toNat + 2 ^ 32 * v93.toNat = v7.toNat * 4294967294 + v52.toNat + v86.toNat) :
    v93.toNat = (v89.toNat + 2 ^ 32 * v93.toNat) / 2 ^ 32 := by
  have := v7.isLt; have := v52.isLt; have := v77.isLt; have := v83.isLt; have := v85.isLt; have := v86.isLt; have := v87.isLt; have := v88.isLt; have := v89.isLt; have := v90.isLt; have := v93.isLt
  generalize v7.toNat = n7 at *
  generalize v52.toNat = n52 at *
  generalize v77.toNat = n77 at *
  generalize v83.toNat = n83 at *
  generalize v85.toNat = n85 at *
  generalize v86.toNat = n86 at *
  generalize v87.toNat = n87 at *
  generalize v88.toNat = n88 at *
  generalize v89.toNat = n89 at *
  generalize v90.toNat = n90 at *
  generalize v93.toNat = n93 at *
  first
    | omega
    | (obtain ⟨t77a, t77b⟩ := t77; rcases (by omega : n7 = 0 ∨ (0 < n7 ∧ n7 ≤ 2147483648) ∨ 2147483648 < n7) with _ | _ | _ <;> rcases t87 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t77a, t77b⟩ := t77; obtain ⟨qt83, et83⟩ := mod_q t83; clear t83; obtain ⟨qt85, et85⟩ := mod_q t85; clear t85; obtain ⟨qt88, et88⟩ := mod_q t88; clear t88; obtain ⟨qt93, et93⟩ := mod_q t93; clear t93; omega)
    | (obtain ⟨t77a, t77b⟩ := t77; obtain ⟨qt83, et83⟩ := mod_q t83; clear t83; obtain ⟨qt85, et85⟩ := mod_q t85; clear t85; obtain ⟨qt88, et88⟩ := mod_q t88; clear t88; obtain ⟨qt93, et93⟩ := mod_q t93; clear t93; rcases (by omega : n7 = 0 ∨ (0 < n7 ∧ n7 ≤ 2147483648) ∨ 2147483648 < n7) with _ | _ | _ <;> rcases t87 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P14 {v7 v58 v69 v91 v93 v94 v95 v97 v98 v99 : Word}
    (t69 : v69.toNat = v7.toNat * 4294967295 / 2 ^ 32 ∧ v69.toNat + (v7.toNat + 4294967295) / 4294967296 = v7.toNat)
    (t91 : v91.toNat = (v58.toNat + 2 ^ 32 - v7.toNat) % 2 ^ 32)
    (t94 : (v91.toNat < v58.toNat ∧ v94.toNat = 1) ∨ (v58.toNat ≤ v91.toNat ∧ v94.toNat = 0))
    (t95 : v95.toNat = (v91.toNat + v93.toNat) % 2 ^ 32)
    (t97 : v97.toNat = (v69.toNat + v94.toNat) % 2 ^ 32)
    (t98 : v95.toNat + 2 ^ 32 * v98.toNat = v91.toNat + v93.toNat)
    (t99 : v99.toNat = (v97.toNat + v98.toNat) % 2 ^ 32) :
    v95.toNat + 2 ^ 32 * v99.toNat = v7.toNat * 4294967295 + v58.toNat + v93.toNat := by
  have := v7.isLt; have := v58.isLt; have := v69.isLt; have := v91.isLt; have := v93.isLt; have := v94.isLt; have := v95.isLt; have := v97.isLt; have := v98.isLt; have := v99.isLt
  generalize v7.toNat = n7 at *
  generalize v58.toNat = n58 at *
  generalize v69.toNat = n69 at *
  generalize v91.toNat = n91 at *
  generalize v93.toNat = n93 at *
  generalize v94.toNat = n94 at *
  generalize v95.toNat = n95 at *
  generalize v97.toNat = n97 at *
  generalize v98.toNat = n98 at *
  generalize v99.toNat = n99 at *
  first
    | omega
    | (obtain ⟨t69a, t69b⟩ := t69; rcases Nat.eq_zero_or_pos n7 with _ | _ <;> rcases t94 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t69a, t69b⟩ := t69; obtain ⟨qt91, et91⟩ := mod_q t91; clear t91; obtain ⟨qt95, et95⟩ := mod_q t95; clear t95; obtain ⟨qt97, et97⟩ := mod_q t97; clear t97; omega)
    | (obtain ⟨t69a, t69b⟩ := t69; obtain ⟨qt91, et91⟩ := mod_q t91; clear t91; obtain ⟨qt95, et95⟩ := mod_q t95; clear t95; obtain ⟨qt97, et97⟩ := mod_q t97; clear t97; rcases Nat.eq_zero_or_pos n7 with _ | _ <;> rcases t94 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P14l {v7 v58 v91 v93 v95 v99 : Word}
    (t91 : v91.toNat = (v58.toNat + 2 ^ 32 - v7.toNat) % 2 ^ 32)
    (t95 : v95.toNat = (v91.toNat + v93.toNat) % 2 ^ 32)
    (wP14 : v95.toNat + 2 ^ 32 * v99.toNat = v7.toNat * 4294967295 + v58.toNat + v93.toNat) :
    v95.toNat = (v95.toNat + 2 ^ 32 * v99.toNat) % 2 ^ 32 := by
  have := v7.isLt; have := v58.isLt; have := v91.isLt; have := v93.isLt; have := v95.isLt; have := v99.isLt
  generalize v7.toNat = n7 at *
  generalize v58.toNat = n58 at *
  generalize v91.toNat = n91 at *
  generalize v93.toNat = n93 at *
  generalize v95.toNat = n95 at *
  generalize v99.toNat = n99 at *
  first
    | omega
    | (obtain ⟨qt91, et91⟩ := mod_q t91; clear t91; obtain ⟨qt95, et95⟩ := mod_q t95; clear t95; omega)

theorem psm_v_P14h {v7 v58 v69 v91 v93 v94 v95 v97 v98 v99 : Word}
    (t69 : v69.toNat = v7.toNat * 4294967295 / 2 ^ 32 ∧ v69.toNat + (v7.toNat + 4294967295) / 4294967296 = v7.toNat)
    (t91 : v91.toNat = (v58.toNat + 2 ^ 32 - v7.toNat) % 2 ^ 32)
    (t94 : (v91.toNat < v58.toNat ∧ v94.toNat = 1) ∨ (v58.toNat ≤ v91.toNat ∧ v94.toNat = 0))
    (t97 : v97.toNat = (v69.toNat + v94.toNat) % 2 ^ 32)
    (t98 : v95.toNat + 2 ^ 32 * v98.toNat = v91.toNat + v93.toNat)
    (t99 : v99.toNat = (v97.toNat + v98.toNat) % 2 ^ 32)
    (wP14 : v95.toNat + 2 ^ 32 * v99.toNat = v7.toNat * 4294967295 + v58.toNat + v93.toNat) :
    v99.toNat = (v95.toNat + 2 ^ 32 * v99.toNat) / 2 ^ 32 := by
  have := v7.isLt; have := v58.isLt; have := v69.isLt; have := v91.isLt; have := v93.isLt; have := v94.isLt; have := v95.isLt; have := v97.isLt; have := v98.isLt; have := v99.isLt
  generalize v7.toNat = n7 at *
  generalize v58.toNat = n58 at *
  generalize v69.toNat = n69 at *
  generalize v91.toNat = n91 at *
  generalize v93.toNat = n93 at *
  generalize v94.toNat = n94 at *
  generalize v95.toNat = n95 at *
  generalize v97.toNat = n97 at *
  generalize v98.toNat = n98 at *
  generalize v99.toNat = n99 at *
  first
    | omega
    | (obtain ⟨t69a, t69b⟩ := t69; rcases Nat.eq_zero_or_pos n7 with _ | _ <;> rcases t94 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t69a, t69b⟩ := t69; obtain ⟨qt91, et91⟩ := mod_q t91; clear t91; obtain ⟨qt97, et97⟩ := mod_q t97; clear t97; obtain ⟨qt99, et99⟩ := mod_q t99; clear t99; omega)
    | (obtain ⟨t69a, t69b⟩ := t69; obtain ⟨qt91, et91⟩ := mod_q t91; clear t91; obtain ⟨qt97, et97⟩ := mod_q t97; clear t97; obtain ⟨qt99, et99⟩ := mod_q t99; clear t99; rcases Nat.eq_zero_or_pos n7 with _ | _ <;> rcases t94 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_S15 {v0 v99 v101 v103 : Word}
    (t101 : v101.toNat = (v99.toNat + v0.toNat) % 2 ^ 32)
    (t103 : v101.toNat + 2 ^ 32 * v103.toNat = v99.toNat + v0.toNat) :
    v101.toNat + 2 ^ 32 * v103.toNat = v0.toNat + v99.toNat := by
  have := v0.isLt; have := v99.isLt; have := v101.isLt; have := v103.isLt
  generalize v0.toNat = n0 at *
  generalize v99.toNat = n99 at *
  generalize v101.toNat = n101 at *
  generalize v103.toNat = n103 at *
  first
    | omega
    | (obtain ⟨qt101, et101⟩ := mod_q t101; clear t101; omega)

theorem psm_v_S15l {v0 v99 v101 v103 : Word}
    (t101 : v101.toNat = (v99.toNat + v0.toNat) % 2 ^ 32)
    (wS15 : v101.toNat + 2 ^ 32 * v103.toNat = v0.toNat + v99.toNat) :
    v101.toNat = (v101.toNat + 2 ^ 32 * v103.toNat) % 2 ^ 32 := by
  have := v0.isLt; have := v99.isLt; have := v101.isLt; have := v103.isLt
  generalize v0.toNat = n0 at *
  generalize v99.toNat = n99 at *
  generalize v101.toNat = n101 at *
  generalize v103.toNat = n103 at *
  first
    | omega
    | (obtain ⟨qt101, et101⟩ := mod_q t101; clear t101; omega)

theorem psm_v_S15h {v0 v99 v101 v103 : Word}
    (t103 : v101.toNat + 2 ^ 32 * v103.toNat = v99.toNat + v0.toNat)
    (wS15 : v101.toNat + 2 ^ 32 * v103.toNat = v0.toNat + v99.toNat) :
    v103.toNat = (v101.toNat + 2 ^ 32 * v103.toNat) / 2 ^ 32 := by
  have := v0.isLt; have := v99.isLt; have := v101.isLt; have := v103.isLt
  generalize v0.toNat = n0 at *
  generalize v99.toNat = n99 at *
  generalize v101.toNat = n101 at *
  generalize v103.toNat = n103 at *
  omega

theorem psm_v_S16 {v7 v103 v108 v152 : Word}
    (t108 : v108.toNat = (v103.toNat + v7.toNat) % 2 ^ 32)
    (t152 : v108.toNat + 2 ^ 32 * v152.toNat = v103.toNat + v7.toNat) :
    v108.toNat + 2 ^ 32 * v152.toNat = v7.toNat + v103.toNat := by
  have := v7.isLt; have := v103.isLt; have := v108.isLt; have := v152.isLt
  generalize v7.toNat = n7 at *
  generalize v103.toNat = n103 at *
  generalize v108.toNat = n108 at *
  generalize v152.toNat = n152 at *
  first
    | omega
    | (obtain ⟨qt108, et108⟩ := mod_q t108; clear t108; omega)

theorem psm_v_S16l {v7 v103 v108 v152 : Word}
    (t108 : v108.toNat = (v103.toNat + v7.toNat) % 2 ^ 32)
    (wS16 : v108.toNat + 2 ^ 32 * v152.toNat = v7.toNat + v103.toNat) :
    v108.toNat = (v108.toNat + 2 ^ 32 * v152.toNat) % 2 ^ 32 := by
  have := v7.isLt; have := v103.isLt; have := v108.isLt; have := v152.isLt
  generalize v7.toNat = n7 at *
  generalize v103.toNat = n103 at *
  generalize v108.toNat = n108 at *
  generalize v152.toNat = n152 at *
  first
    | omega
    | (obtain ⟨qt108, et108⟩ := mod_q t108; clear t108; omega)

theorem psm_v_S16h {v7 v103 v108 v152 : Word}
    (t152 : v108.toNat + 2 ^ 32 * v152.toNat = v103.toNat + v7.toNat)
    (wS16 : v108.toNat + 2 ^ 32 * v152.toNat = v7.toNat + v103.toNat) :
    v152.toNat = (v108.toNat + 2 ^ 32 * v152.toNat) / 2 ^ 32 := by
  have := v7.isLt; have := v103.isLt; have := v108.isLt; have := v152.isLt
  generalize v7.toNat = n7 at *
  generalize v103.toNat = n103 at *
  generalize v108.toNat = n108 at *
  generalize v152.toNat = n152 at *
  omega

theorem psm_v_P17h {v8 v60 v96 v102 v104 v106 v109 v112 : Word}
    (t96 : v96.toNat = v8.toNat * 4007631870 % 2 ^ 32)
    (t102 : v102.toNat = v8.toNat * 4007631870 / 2 ^ 32)
    (t104 : v104.toNat = v60.toNat / 2 * 2)
    (t106 : v106.toNat = (v96.toNat + v104.toNat) % 2 ^ 32)
    (t109 : v106.toNat + 2 ^ 32 * v109.toNat = v96.toNat + v104.toNat)
    (t112 : v112.toNat = (v109.toNat + v102.toNat) % 2 ^ 32) :
    v112.toNat = (v8.toNat * 4007631870 + v60.toNat) / 2 ^ 32 := by
  have := v8.isLt; have := v60.isLt; have := v96.isLt; have := v102.isLt; have := v104.isLt; have := v106.isLt; have := v109.isLt; have := v112.isLt
  generalize v8.toNat = n8 at *
  generalize v60.toNat = n60 at *
  generalize v96.toNat = n96 at *
  generalize v102.toNat = n102 at *
  generalize v104.toNat = n104 at *
  generalize v106.toNat = n106 at *
  generalize v109.toNat = n109 at *
  generalize v112.toNat = n112 at *
  first
    | omega
    | (obtain ⟨qt96, et96⟩ := mod_q t96; clear t96; obtain ⟨qt106, et106⟩ := mod_q t106; clear t106; omega)

theorem psm_v_P18 {v8 v67 v100 v105 v110 v112 v113 v114 v116 v117 v120 : Word}
    (t100 : v100.toNat = v8.toNat * 19922309 % 2 ^ 32)
    (t105 : v105.toNat = v8.toNat * 19922309 / 2 ^ 32)
    (t110 : v110.toNat = (v100.toNat + v67.toNat) % 2 ^ 32)
    (t113 : v110.toNat + 2 ^ 32 * v113.toNat = v100.toNat + v67.toNat)
    (t114 : v114.toNat = (v110.toNat + v112.toNat) % 2 ^ 32)
    (t116 : v116.toNat = (v105.toNat + v113.toNat) % 2 ^ 32)
    (t117 : v114.toNat + 2 ^ 32 * v117.toNat = v110.toNat + v112.toNat)
    (t120 : v120.toNat = (v117.toNat + v116.toNat) % 2 ^ 32) :
    v114.toNat + 2 ^ 32 * v120.toNat = v8.toNat * 19922309 + v67.toNat + v112.toNat := by
  have := v8.isLt; have := v67.isLt; have := v100.isLt; have := v105.isLt; have := v110.isLt; have := v112.isLt; have := v113.isLt; have := v114.isLt; have := v116.isLt; have := v117.isLt; have := v120.isLt
  generalize v8.toNat = n8 at *
  generalize v67.toNat = n67 at *
  generalize v100.toNat = n100 at *
  generalize v105.toNat = n105 at *
  generalize v110.toNat = n110 at *
  generalize v112.toNat = n112 at *
  generalize v113.toNat = n113 at *
  generalize v114.toNat = n114 at *
  generalize v116.toNat = n116 at *
  generalize v117.toNat = n117 at *
  generalize v120.toNat = n120 at *
  first
    | omega
    | (obtain ⟨qt100, et100⟩ := mod_q t100; clear t100; obtain ⟨qt110, et110⟩ := mod_q t110; clear t110; obtain ⟨qt114, et114⟩ := mod_q t114; clear t114; obtain ⟨qt116, et116⟩ := mod_q t116; clear t116; omega)

theorem psm_v_P18l {v8 v67 v100 v110 v112 v114 v120 : Word}
    (t100 : v100.toNat = v8.toNat * 19922309 % 2 ^ 32)
    (t110 : v110.toNat = (v100.toNat + v67.toNat) % 2 ^ 32)
    (t114 : v114.toNat = (v110.toNat + v112.toNat) % 2 ^ 32)
    (wP18 : v114.toNat + 2 ^ 32 * v120.toNat = v8.toNat * 19922309 + v67.toNat + v112.toNat) :
    v114.toNat = (v114.toNat + 2 ^ 32 * v120.toNat) % 2 ^ 32 := by
  have := v8.isLt; have := v67.isLt; have := v100.isLt; have := v110.isLt; have := v112.isLt; have := v114.isLt; have := v120.isLt
  generalize v8.toNat = n8 at *
  generalize v67.toNat = n67 at *
  generalize v100.toNat = n100 at *
  generalize v110.toNat = n110 at *
  generalize v112.toNat = n112 at *
  generalize v114.toNat = n114 at *
  generalize v120.toNat = n120 at *
  first
    | omega
    | (obtain ⟨qt100, et100⟩ := mod_q t100; clear t100; obtain ⟨qt110, et110⟩ := mod_q t110; clear t110; obtain ⟨qt114, et114⟩ := mod_q t114; clear t114; omega)

theorem psm_v_P18h {v8 v67 v100 v105 v110 v112 v113 v114 v116 v117 v120 : Word}
    (t100 : v100.toNat = v8.toNat * 19922309 % 2 ^ 32)
    (t105 : v105.toNat = v8.toNat * 19922309 / 2 ^ 32)
    (t110 : v110.toNat = (v100.toNat + v67.toNat) % 2 ^ 32)
    (t113 : v110.toNat + 2 ^ 32 * v113.toNat = v100.toNat + v67.toNat)
    (t116 : v116.toNat = (v105.toNat + v113.toNat) % 2 ^ 32)
    (t117 : v114.toNat + 2 ^ 32 * v117.toNat = v110.toNat + v112.toNat)
    (t120 : v120.toNat = (v117.toNat + v116.toNat) % 2 ^ 32)
    (wP18 : v114.toNat + 2 ^ 32 * v120.toNat = v8.toNat * 19922309 + v67.toNat + v112.toNat) :
    v120.toNat = (v114.toNat + 2 ^ 32 * v120.toNat) / 2 ^ 32 := by
  have := v8.isLt; have := v67.isLt; have := v100.isLt; have := v105.isLt; have := v110.isLt; have := v112.isLt; have := v113.isLt; have := v114.isLt; have := v116.isLt; have := v117.isLt; have := v120.isLt
  generalize v8.toNat = n8 at *
  generalize v67.toNat = n67 at *
  generalize v100.toNat = n100 at *
  generalize v105.toNat = n105 at *
  generalize v110.toNat = n110 at *
  generalize v112.toNat = n112 at *
  generalize v113.toNat = n113 at *
  generalize v114.toNat = n114 at *
  generalize v116.toNat = n116 at *
  generalize v117.toNat = n117 at *
  generalize v120.toNat = n120 at *
  first
    | omega
    | (obtain ⟨qt100, et100⟩ := mod_q t100; clear t100; obtain ⟨qt110, et110⟩ := mod_q t110; clear t110; obtain ⟨qt116, et116⟩ := mod_q t116; clear t116; obtain ⟨qt120, et120⟩ := mod_q t120; clear t120; omega)

theorem psm_v_P19 {v8 v75 v107 v111 v118 v120 v121 v122 v123 v124 v126 : Word}
    (t107 : v107.toNat = v8.toNat * 3743050785 % 2 ^ 32)
    (t111 : v111.toNat = v8.toNat * 3743050785 / 2 ^ 32)
    (t118 : v118.toNat = (v107.toNat + v75.toNat) % 2 ^ 32)
    (t121 : v118.toNat + 2 ^ 32 * v121.toNat = v107.toNat + v75.toNat)
    (t122 : v122.toNat = (v111.toNat + v121.toNat) % 2 ^ 32)
    (t123 : v123.toNat = (v118.toNat + v120.toNat) % 2 ^ 32)
    (t124 : v123.toNat + 2 ^ 32 * v124.toNat = v118.toNat + v120.toNat)
    (t126 : v126.toNat = (v122.toNat + v124.toNat) % 2 ^ 32) :
    v123.toNat + 2 ^ 32 * v126.toNat = v8.toNat * 3743050785 + v75.toNat + v120.toNat := by
  have := v8.isLt; have := v75.isLt; have := v107.isLt; have := v111.isLt; have := v118.isLt; have := v120.isLt; have := v121.isLt; have := v122.isLt; have := v123.isLt; have := v124.isLt; have := v126.isLt
  generalize v8.toNat = n8 at *
  generalize v75.toNat = n75 at *
  generalize v107.toNat = n107 at *
  generalize v111.toNat = n111 at *
  generalize v118.toNat = n118 at *
  generalize v120.toNat = n120 at *
  generalize v121.toNat = n121 at *
  generalize v122.toNat = n122 at *
  generalize v123.toNat = n123 at *
  generalize v124.toNat = n124 at *
  generalize v126.toNat = n126 at *
  first
    | omega
    | (obtain ⟨qt107, et107⟩ := mod_q t107; clear t107; obtain ⟨qt118, et118⟩ := mod_q t118; clear t118; obtain ⟨qt122, et122⟩ := mod_q t122; clear t122; obtain ⟨qt123, et123⟩ := mod_q t123; clear t123; omega)

theorem psm_v_P19l {v8 v75 v107 v118 v120 v123 v126 : Word}
    (t107 : v107.toNat = v8.toNat * 3743050785 % 2 ^ 32)
    (t118 : v118.toNat = (v107.toNat + v75.toNat) % 2 ^ 32)
    (t123 : v123.toNat = (v118.toNat + v120.toNat) % 2 ^ 32)
    (wP19 : v123.toNat + 2 ^ 32 * v126.toNat = v8.toNat * 3743050785 + v75.toNat + v120.toNat) :
    v123.toNat = (v123.toNat + 2 ^ 32 * v126.toNat) % 2 ^ 32 := by
  have := v8.isLt; have := v75.isLt; have := v107.isLt; have := v118.isLt; have := v120.isLt; have := v123.isLt; have := v126.isLt
  generalize v8.toNat = n8 at *
  generalize v75.toNat = n75 at *
  generalize v107.toNat = n107 at *
  generalize v118.toNat = n118 at *
  generalize v120.toNat = n120 at *
  generalize v123.toNat = n123 at *
  generalize v126.toNat = n126 at *
  first
    | omega
    | (obtain ⟨qt107, et107⟩ := mod_q t107; clear t107; obtain ⟨qt118, et118⟩ := mod_q t118; clear t118; obtain ⟨qt123, et123⟩ := mod_q t123; clear t123; omega)

theorem psm_v_P19h {v8 v75 v107 v111 v118 v120 v121 v122 v123 v124 v126 : Word}
    (t107 : v107.toNat = v8.toNat * 3743050785 % 2 ^ 32)
    (t111 : v111.toNat = v8.toNat * 3743050785 / 2 ^ 32)
    (t118 : v118.toNat = (v107.toNat + v75.toNat) % 2 ^ 32)
    (t121 : v118.toNat + 2 ^ 32 * v121.toNat = v107.toNat + v75.toNat)
    (t122 : v122.toNat = (v111.toNat + v121.toNat) % 2 ^ 32)
    (t124 : v123.toNat + 2 ^ 32 * v124.toNat = v118.toNat + v120.toNat)
    (t126 : v126.toNat = (v122.toNat + v124.toNat) % 2 ^ 32)
    (wP19 : v123.toNat + 2 ^ 32 * v126.toNat = v8.toNat * 3743050785 + v75.toNat + v120.toNat) :
    v126.toNat = (v123.toNat + 2 ^ 32 * v126.toNat) / 2 ^ 32 := by
  have := v8.isLt; have := v75.isLt; have := v107.isLt; have := v111.isLt; have := v118.isLt; have := v120.isLt; have := v121.isLt; have := v122.isLt; have := v123.isLt; have := v124.isLt; have := v126.isLt
  generalize v8.toNat = n8 at *
  generalize v75.toNat = n75 at *
  generalize v107.toNat = n107 at *
  generalize v111.toNat = n111 at *
  generalize v118.toNat = n118 at *
  generalize v120.toNat = n120 at *
  generalize v121.toNat = n121 at *
  generalize v122.toNat = n122 at *
  generalize v123.toNat = n123 at *
  generalize v124.toNat = n124 at *
  generalize v126.toNat = n126 at *
  first
    | omega
    | (obtain ⟨qt107, et107⟩ := mod_q t107; clear t107; obtain ⟨qt118, et118⟩ := mod_q t118; clear t118; obtain ⟨qt122, et122⟩ := mod_q t122; clear t122; obtain ⟨qt126, et126⟩ := mod_q t126; clear t126; omega)

theorem psm_v_P20 {v8 v82 v115 v119 v126 v127 v128 v129 v130 v131 v134 : Word}
    (t115 : v115.toNat = v8.toNat * 1125713234 % 2 ^ 32)
    (t119 : v119.toNat = v8.toNat * 1125713234 / 2 ^ 32)
    (t127 : v127.toNat = (v115.toNat + v82.toNat) % 2 ^ 32)
    (t128 : v127.toNat + 2 ^ 32 * v128.toNat = v115.toNat + v82.toNat)
    (t129 : v129.toNat = (v127.toNat + v126.toNat) % 2 ^ 32)
    (t130 : v130.toNat = (v128.toNat + v119.toNat) % 2 ^ 32)
    (t131 : v129.toNat + 2 ^ 32 * v131.toNat = v127.toNat + v126.toNat)
    (t134 : v134.toNat = (v131.toNat + v130.toNat) % 2 ^ 32) :
    v129.toNat + 2 ^ 32 * v134.toNat = v8.toNat * 1125713234 + v82.toNat + v126.toNat := by
  have := v8.isLt; have := v82.isLt; have := v115.isLt; have := v119.isLt; have := v126.isLt; have := v127.isLt; have := v128.isLt; have := v129.isLt; have := v130.isLt; have := v131.isLt; have := v134.isLt
  generalize v8.toNat = n8 at *
  generalize v82.toNat = n82 at *
  generalize v115.toNat = n115 at *
  generalize v119.toNat = n119 at *
  generalize v126.toNat = n126 at *
  generalize v127.toNat = n127 at *
  generalize v128.toNat = n128 at *
  generalize v129.toNat = n129 at *
  generalize v130.toNat = n130 at *
  generalize v131.toNat = n131 at *
  generalize v134.toNat = n134 at *
  first
    | omega
    | (obtain ⟨qt115, et115⟩ := mod_q t115; clear t115; obtain ⟨qt127, et127⟩ := mod_q t127; clear t127; obtain ⟨qt129, et129⟩ := mod_q t129; clear t129; obtain ⟨qt130, et130⟩ := mod_q t130; clear t130; omega)

theorem psm_v_P20l {v8 v82 v115 v126 v127 v129 v134 : Word}
    (t115 : v115.toNat = v8.toNat * 1125713234 % 2 ^ 32)
    (t127 : v127.toNat = (v115.toNat + v82.toNat) % 2 ^ 32)
    (t129 : v129.toNat = (v127.toNat + v126.toNat) % 2 ^ 32)
    (wP20 : v129.toNat + 2 ^ 32 * v134.toNat = v8.toNat * 1125713234 + v82.toNat + v126.toNat) :
    v129.toNat = (v129.toNat + 2 ^ 32 * v134.toNat) % 2 ^ 32 := by
  have := v8.isLt; have := v82.isLt; have := v115.isLt; have := v126.isLt; have := v127.isLt; have := v129.isLt; have := v134.isLt
  generalize v8.toNat = n8 at *
  generalize v82.toNat = n82 at *
  generalize v115.toNat = n115 at *
  generalize v126.toNat = n126 at *
  generalize v127.toNat = n127 at *
  generalize v129.toNat = n129 at *
  generalize v134.toNat = n134 at *
  first
    | omega
    | (obtain ⟨qt115, et115⟩ := mod_q t115; clear t115; obtain ⟨qt127, et127⟩ := mod_q t127; clear t127; obtain ⟨qt129, et129⟩ := mod_q t129; clear t129; omega)

theorem psm_v_P20h {v8 v82 v115 v119 v126 v127 v128 v129 v130 v131 v134 : Word}
    (t115 : v115.toNat = v8.toNat * 1125713234 % 2 ^ 32)
    (t119 : v119.toNat = v8.toNat * 1125713234 / 2 ^ 32)
    (t127 : v127.toNat = (v115.toNat + v82.toNat) % 2 ^ 32)
    (t128 : v127.toNat + 2 ^ 32 * v128.toNat = v115.toNat + v82.toNat)
    (t130 : v130.toNat = (v128.toNat + v119.toNat) % 2 ^ 32)
    (t131 : v129.toNat + 2 ^ 32 * v131.toNat = v127.toNat + v126.toNat)
    (t134 : v134.toNat = (v131.toNat + v130.toNat) % 2 ^ 32)
    (wP20 : v129.toNat + 2 ^ 32 * v134.toNat = v8.toNat * 1125713234 + v82.toNat + v126.toNat) :
    v134.toNat = (v129.toNat + 2 ^ 32 * v134.toNat) / 2 ^ 32 := by
  have := v8.isLt; have := v82.isLt; have := v115.isLt; have := v119.isLt; have := v126.isLt; have := v127.isLt; have := v128.isLt; have := v129.isLt; have := v130.isLt; have := v131.isLt; have := v134.isLt
  generalize v8.toNat = n8 at *
  generalize v82.toNat = n82 at *
  generalize v115.toNat = n115 at *
  generalize v119.toNat = n119 at *
  generalize v126.toNat = n126 at *
  generalize v127.toNat = n127 at *
  generalize v128.toNat = n128 at *
  generalize v129.toNat = n129 at *
  generalize v130.toNat = n130 at *
  generalize v131.toNat = n131 at *
  generalize v134.toNat = n134 at *
  first
    | omega
    | (obtain ⟨qt115, et115⟩ := mod_q t115; clear t115; obtain ⟨qt127, et127⟩ := mod_q t127; clear t127; obtain ⟨qt130, et130⟩ := mod_q t130; clear t130; obtain ⟨qt134, et134⟩ := mod_q t134; clear t134; omega)

theorem psm_v_P21 {v8 v89 v125 v132 v134 v135 v136 v137 v138 v140 : Word}
    (t125 : v125.toNat = v8.toNat * 4294967295 / 2 ^ 32 ∧ v125.toNat + (v8.toNat + 4294967295) / 4294967296 = v8.toNat)
    (t132 : v132.toNat = (v89.toNat + 2 ^ 32 - v8.toNat) % 2 ^ 32)
    (t135 : (v132.toNat < v89.toNat ∧ v135.toNat = 1) ∨ (v89.toNat ≤ v132.toNat ∧ v135.toNat = 0))
    (t136 : v136.toNat = (v135.toNat + v125.toNat) % 2 ^ 32)
    (t137 : v137.toNat = (v132.toNat + v134.toNat) % 2 ^ 32)
    (t138 : v137.toNat + 2 ^ 32 * v138.toNat = v132.toNat + v134.toNat)
    (t140 : v140.toNat = (v138.toNat + v136.toNat) % 2 ^ 32) :
    v137.toNat + 2 ^ 32 * v140.toNat = v8.toNat * 4294967295 + v89.toNat + v134.toNat := by
  have := v8.isLt; have := v89.isLt; have := v125.isLt; have := v132.isLt; have := v134.isLt; have := v135.isLt; have := v136.isLt; have := v137.isLt; have := v138.isLt; have := v140.isLt
  generalize v8.toNat = n8 at *
  generalize v89.toNat = n89 at *
  generalize v125.toNat = n125 at *
  generalize v132.toNat = n132 at *
  generalize v134.toNat = n134 at *
  generalize v135.toNat = n135 at *
  generalize v136.toNat = n136 at *
  generalize v137.toNat = n137 at *
  generalize v138.toNat = n138 at *
  generalize v140.toNat = n140 at *
  first
    | omega
    | (obtain ⟨t125a, t125b⟩ := t125; rcases Nat.eq_zero_or_pos n8 with _ | _ <;> rcases t135 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t125a, t125b⟩ := t125; obtain ⟨qt132, et132⟩ := mod_q t132; clear t132; obtain ⟨qt136, et136⟩ := mod_q t136; clear t136; obtain ⟨qt137, et137⟩ := mod_q t137; clear t137; omega)
    | (obtain ⟨t125a, t125b⟩ := t125; obtain ⟨qt132, et132⟩ := mod_q t132; clear t132; obtain ⟨qt136, et136⟩ := mod_q t136; clear t136; obtain ⟨qt137, et137⟩ := mod_q t137; clear t137; rcases Nat.eq_zero_or_pos n8 with _ | _ <;> rcases t135 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P21l {v8 v89 v132 v134 v137 v140 : Word}
    (t132 : v132.toNat = (v89.toNat + 2 ^ 32 - v8.toNat) % 2 ^ 32)
    (t137 : v137.toNat = (v132.toNat + v134.toNat) % 2 ^ 32)
    (wP21 : v137.toNat + 2 ^ 32 * v140.toNat = v8.toNat * 4294967295 + v89.toNat + v134.toNat) :
    v137.toNat = (v137.toNat + 2 ^ 32 * v140.toNat) % 2 ^ 32 := by
  have := v8.isLt; have := v89.isLt; have := v132.isLt; have := v134.isLt; have := v137.isLt; have := v140.isLt
  generalize v8.toNat = n8 at *
  generalize v89.toNat = n89 at *
  generalize v132.toNat = n132 at *
  generalize v134.toNat = n134 at *
  generalize v137.toNat = n137 at *
  generalize v140.toNat = n140 at *
  first
    | omega
    | (obtain ⟨qt132, et132⟩ := mod_q t132; clear t132; obtain ⟨qt137, et137⟩ := mod_q t137; clear t137; omega)

theorem psm_v_P21h {v8 v89 v125 v132 v134 v135 v136 v137 v138 v140 : Word}
    (t125 : v125.toNat = v8.toNat * 4294967295 / 2 ^ 32 ∧ v125.toNat + (v8.toNat + 4294967295) / 4294967296 = v8.toNat)
    (t132 : v132.toNat = (v89.toNat + 2 ^ 32 - v8.toNat) % 2 ^ 32)
    (t135 : (v132.toNat < v89.toNat ∧ v135.toNat = 1) ∨ (v89.toNat ≤ v132.toNat ∧ v135.toNat = 0))
    (t136 : v136.toNat = (v135.toNat + v125.toNat) % 2 ^ 32)
    (t138 : v137.toNat + 2 ^ 32 * v138.toNat = v132.toNat + v134.toNat)
    (t140 : v140.toNat = (v138.toNat + v136.toNat) % 2 ^ 32)
    (wP21 : v137.toNat + 2 ^ 32 * v140.toNat = v8.toNat * 4294967295 + v89.toNat + v134.toNat) :
    v140.toNat = (v137.toNat + 2 ^ 32 * v140.toNat) / 2 ^ 32 := by
  have := v8.isLt; have := v89.isLt; have := v125.isLt; have := v132.isLt; have := v134.isLt; have := v135.isLt; have := v136.isLt; have := v137.isLt; have := v138.isLt; have := v140.isLt
  generalize v8.toNat = n8 at *
  generalize v89.toNat = n89 at *
  generalize v125.toNat = n125 at *
  generalize v132.toNat = n132 at *
  generalize v134.toNat = n134 at *
  generalize v135.toNat = n135 at *
  generalize v136.toNat = n136 at *
  generalize v137.toNat = n137 at *
  generalize v138.toNat = n138 at *
  generalize v140.toNat = n140 at *
  first
    | omega
    | (obtain ⟨t125a, t125b⟩ := t125; rcases Nat.eq_zero_or_pos n8 with _ | _ <;> rcases t135 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t125a, t125b⟩ := t125; obtain ⟨qt132, et132⟩ := mod_q t132; clear t132; obtain ⟨qt136, et136⟩ := mod_q t136; clear t136; obtain ⟨qt140, et140⟩ := mod_q t140; clear t140; omega)
    | (obtain ⟨t125a, t125b⟩ := t125; obtain ⟨qt132, et132⟩ := mod_q t132; clear t132; obtain ⟨qt136, et136⟩ := mod_q t136; clear t136; obtain ⟨qt140, et140⟩ := mod_q t140; clear t140; rcases Nat.eq_zero_or_pos n8 with _ | _ <;> rcases t135 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P22 {v8 v95 v133 v139 v140 v141 v142 v143 v144 v145 v146 : Word}
    (t133 : v133.toNat = v8.toNat * 4294967294 / 2 ^ 32 ∧ v133.toNat + (2 * v8.toNat + 4294967295) / 4294967296 = v8.toNat)
    (t139 : v139.toNat = (v8.toNat + v8.toNat) % 2 ^ 32)
    (t141 : v141.toNat = (v95.toNat + 2 ^ 32 - v139.toNat) % 2 ^ 32)
    (t142 : (v141.toNat < v95.toNat ∧ v142.toNat = 1) ∨ (v95.toNat ≤ v141.toNat ∧ v142.toNat = 0))
    (t143 : v143.toNat = (v141.toNat + v140.toNat) % 2 ^ 32)
    (t144 : v144.toNat = (v142.toNat + v133.toNat) % 2 ^ 32)
    (t145 : v143.toNat + 2 ^ 32 * v145.toNat = v141.toNat + v140.toNat)
    (t146 : v146.toNat = (v145.toNat + v144.toNat) % 2 ^ 32) :
    v143.toNat + 2 ^ 32 * v146.toNat = v8.toNat * 4294967294 + v95.toNat + v140.toNat := by
  have := v8.isLt; have := v95.isLt; have := v133.isLt; have := v139.isLt; have := v140.isLt; have := v141.isLt; have := v142.isLt; have := v143.isLt; have := v144.isLt; have := v145.isLt; have := v146.isLt
  generalize v8.toNat = n8 at *
  generalize v95.toNat = n95 at *
  generalize v133.toNat = n133 at *
  generalize v139.toNat = n139 at *
  generalize v140.toNat = n140 at *
  generalize v141.toNat = n141 at *
  generalize v142.toNat = n142 at *
  generalize v143.toNat = n143 at *
  generalize v144.toNat = n144 at *
  generalize v145.toNat = n145 at *
  generalize v146.toNat = n146 at *
  first
    | omega
    | (obtain ⟨t133a, t133b⟩ := t133; rcases (by omega : n8 = 0 ∨ (0 < n8 ∧ n8 ≤ 2147483648) ∨ 2147483648 < n8) with _ | _ | _ <;> rcases t142 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t133a, t133b⟩ := t133; obtain ⟨qt139, et139⟩ := mod_q t139; clear t139; obtain ⟨qt141, et141⟩ := mod_q t141; clear t141; obtain ⟨qt143, et143⟩ := mod_q t143; clear t143; obtain ⟨qt144, et144⟩ := mod_q t144; clear t144; omega)
    | (obtain ⟨t133a, t133b⟩ := t133; obtain ⟨qt139, et139⟩ := mod_q t139; clear t139; obtain ⟨qt141, et141⟩ := mod_q t141; clear t141; obtain ⟨qt143, et143⟩ := mod_q t143; clear t143; obtain ⟨qt144, et144⟩ := mod_q t144; clear t144; rcases (by omega : n8 = 0 ∨ (0 < n8 ∧ n8 ≤ 2147483648) ∨ 2147483648 < n8) with _ | _ | _ <;> rcases t142 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P22l {v8 v95 v139 v140 v141 v143 v146 : Word}
    (t139 : v139.toNat = (v8.toNat + v8.toNat) % 2 ^ 32)
    (t141 : v141.toNat = (v95.toNat + 2 ^ 32 - v139.toNat) % 2 ^ 32)
    (t143 : v143.toNat = (v141.toNat + v140.toNat) % 2 ^ 32)
    (wP22 : v143.toNat + 2 ^ 32 * v146.toNat = v8.toNat * 4294967294 + v95.toNat + v140.toNat) :
    v143.toNat = (v143.toNat + 2 ^ 32 * v146.toNat) % 2 ^ 32 := by
  have := v8.isLt; have := v95.isLt; have := v139.isLt; have := v140.isLt; have := v141.isLt; have := v143.isLt; have := v146.isLt
  generalize v8.toNat = n8 at *
  generalize v95.toNat = n95 at *
  generalize v139.toNat = n139 at *
  generalize v140.toNat = n140 at *
  generalize v141.toNat = n141 at *
  generalize v143.toNat = n143 at *
  generalize v146.toNat = n146 at *
  first
    | omega
    | (obtain ⟨qt139, et139⟩ := mod_q t139; clear t139; obtain ⟨qt141, et141⟩ := mod_q t141; clear t141; obtain ⟨qt143, et143⟩ := mod_q t143; clear t143; omega)

theorem psm_v_P22h {v8 v95 v133 v139 v140 v141 v142 v143 v144 v145 v146 : Word}
    (t133 : v133.toNat = v8.toNat * 4294967294 / 2 ^ 32 ∧ v133.toNat + (2 * v8.toNat + 4294967295) / 4294967296 = v8.toNat)
    (t139 : v139.toNat = (v8.toNat + v8.toNat) % 2 ^ 32)
    (t141 : v141.toNat = (v95.toNat + 2 ^ 32 - v139.toNat) % 2 ^ 32)
    (t142 : (v141.toNat < v95.toNat ∧ v142.toNat = 1) ∨ (v95.toNat ≤ v141.toNat ∧ v142.toNat = 0))
    (t144 : v144.toNat = (v142.toNat + v133.toNat) % 2 ^ 32)
    (t145 : v143.toNat + 2 ^ 32 * v145.toNat = v141.toNat + v140.toNat)
    (t146 : v146.toNat = (v145.toNat + v144.toNat) % 2 ^ 32)
    (wP22 : v143.toNat + 2 ^ 32 * v146.toNat = v8.toNat * 4294967294 + v95.toNat + v140.toNat) :
    v146.toNat = (v143.toNat + 2 ^ 32 * v146.toNat) / 2 ^ 32 := by
  have := v8.isLt; have := v95.isLt; have := v133.isLt; have := v139.isLt; have := v140.isLt; have := v141.isLt; have := v142.isLt; have := v143.isLt; have := v144.isLt; have := v145.isLt; have := v146.isLt
  generalize v8.toNat = n8 at *
  generalize v95.toNat = n95 at *
  generalize v133.toNat = n133 at *
  generalize v139.toNat = n139 at *
  generalize v140.toNat = n140 at *
  generalize v141.toNat = n141 at *
  generalize v142.toNat = n142 at *
  generalize v143.toNat = n143 at *
  generalize v144.toNat = n144 at *
  generalize v145.toNat = n145 at *
  generalize v146.toNat = n146 at *
  first
    | omega
    | (obtain ⟨t133a, t133b⟩ := t133; rcases (by omega : n8 = 0 ∨ (0 < n8 ∧ n8 ≤ 2147483648) ∨ 2147483648 < n8) with _ | _ | _ <;> rcases t142 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t133a, t133b⟩ := t133; obtain ⟨qt139, et139⟩ := mod_q t139; clear t139; obtain ⟨qt141, et141⟩ := mod_q t141; clear t141; obtain ⟨qt144, et144⟩ := mod_q t144; clear t144; obtain ⟨qt146, et146⟩ := mod_q t146; clear t146; omega)
    | (obtain ⟨t133a, t133b⟩ := t133; obtain ⟨qt139, et139⟩ := mod_q t139; clear t139; obtain ⟨qt141, et141⟩ := mod_q t141; clear t141; obtain ⟨qt144, et144⟩ := mod_q t144; clear t144; obtain ⟨qt146, et146⟩ := mod_q t146; clear t146; rcases (by omega : n8 = 0 ∨ (0 < n8 ∧ n8 ≤ 2147483648) ∨ 2147483648 < n8) with _ | _ | _ <;> rcases t142 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P23 {v8 v101 v125 v146 v147 v148 v149 v150 v151 v153 : Word}
    (t125 : v125.toNat = v8.toNat * 4294967295 / 2 ^ 32 ∧ v125.toNat + (v8.toNat + 4294967295) / 4294967296 = v8.toNat)
    (t147 : v147.toNat = (v101.toNat + 2 ^ 32 - v8.toNat) % 2 ^ 32)
    (t148 : (v147.toNat < v101.toNat ∧ v148.toNat = 1) ∨ (v101.toNat ≤ v147.toNat ∧ v148.toNat = 0))
    (t149 : v149.toNat = (v147.toNat + v146.toNat) % 2 ^ 32)
    (t150 : v150.toNat = (v148.toNat + v125.toNat) % 2 ^ 32)
    (t151 : v149.toNat + 2 ^ 32 * v151.toNat = v147.toNat + v146.toNat)
    (t153 : v153.toNat = (v151.toNat + v150.toNat) % 2 ^ 32) :
    v149.toNat + 2 ^ 32 * v153.toNat = v8.toNat * 4294967295 + v101.toNat + v146.toNat := by
  have := v8.isLt; have := v101.isLt; have := v125.isLt; have := v146.isLt; have := v147.isLt; have := v148.isLt; have := v149.isLt; have := v150.isLt; have := v151.isLt; have := v153.isLt
  generalize v8.toNat = n8 at *
  generalize v101.toNat = n101 at *
  generalize v125.toNat = n125 at *
  generalize v146.toNat = n146 at *
  generalize v147.toNat = n147 at *
  generalize v148.toNat = n148 at *
  generalize v149.toNat = n149 at *
  generalize v150.toNat = n150 at *
  generalize v151.toNat = n151 at *
  generalize v153.toNat = n153 at *
  first
    | omega
    | (obtain ⟨t125a, t125b⟩ := t125; rcases Nat.eq_zero_or_pos n8 with _ | _ <;> rcases t148 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t125a, t125b⟩ := t125; obtain ⟨qt147, et147⟩ := mod_q t147; clear t147; obtain ⟨qt149, et149⟩ := mod_q t149; clear t149; obtain ⟨qt150, et150⟩ := mod_q t150; clear t150; omega)
    | (obtain ⟨t125a, t125b⟩ := t125; obtain ⟨qt147, et147⟩ := mod_q t147; clear t147; obtain ⟨qt149, et149⟩ := mod_q t149; clear t149; obtain ⟨qt150, et150⟩ := mod_q t150; clear t150; rcases Nat.eq_zero_or_pos n8 with _ | _ <;> rcases t148 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_P23l {v8 v101 v146 v147 v149 v153 : Word}
    (t147 : v147.toNat = (v101.toNat + 2 ^ 32 - v8.toNat) % 2 ^ 32)
    (t149 : v149.toNat = (v147.toNat + v146.toNat) % 2 ^ 32)
    (wP23 : v149.toNat + 2 ^ 32 * v153.toNat = v8.toNat * 4294967295 + v101.toNat + v146.toNat) :
    v149.toNat = (v149.toNat + 2 ^ 32 * v153.toNat) % 2 ^ 32 := by
  have := v8.isLt; have := v101.isLt; have := v146.isLt; have := v147.isLt; have := v149.isLt; have := v153.isLt
  generalize v8.toNat = n8 at *
  generalize v101.toNat = n101 at *
  generalize v146.toNat = n146 at *
  generalize v147.toNat = n147 at *
  generalize v149.toNat = n149 at *
  generalize v153.toNat = n153 at *
  first
    | omega
    | (obtain ⟨qt147, et147⟩ := mod_q t147; clear t147; obtain ⟨qt149, et149⟩ := mod_q t149; clear t149; omega)

theorem psm_v_P23h {v8 v101 v125 v146 v147 v148 v149 v150 v151 v153 : Word}
    (t125 : v125.toNat = v8.toNat * 4294967295 / 2 ^ 32 ∧ v125.toNat + (v8.toNat + 4294967295) / 4294967296 = v8.toNat)
    (t147 : v147.toNat = (v101.toNat + 2 ^ 32 - v8.toNat) % 2 ^ 32)
    (t148 : (v147.toNat < v101.toNat ∧ v148.toNat = 1) ∨ (v101.toNat ≤ v147.toNat ∧ v148.toNat = 0))
    (t150 : v150.toNat = (v148.toNat + v125.toNat) % 2 ^ 32)
    (t151 : v149.toNat + 2 ^ 32 * v151.toNat = v147.toNat + v146.toNat)
    (t153 : v153.toNat = (v151.toNat + v150.toNat) % 2 ^ 32)
    (wP23 : v149.toNat + 2 ^ 32 * v153.toNat = v8.toNat * 4294967295 + v101.toNat + v146.toNat) :
    v153.toNat = (v149.toNat + 2 ^ 32 * v153.toNat) / 2 ^ 32 := by
  have := v8.isLt; have := v101.isLt; have := v125.isLt; have := v146.isLt; have := v147.isLt; have := v148.isLt; have := v149.isLt; have := v150.isLt; have := v151.isLt; have := v153.isLt
  generalize v8.toNat = n8 at *
  generalize v101.toNat = n101 at *
  generalize v125.toNat = n125 at *
  generalize v146.toNat = n146 at *
  generalize v147.toNat = n147 at *
  generalize v148.toNat = n148 at *
  generalize v149.toNat = n149 at *
  generalize v150.toNat = n150 at *
  generalize v151.toNat = n151 at *
  generalize v153.toNat = n153 at *
  first
    | omega
    | (obtain ⟨t125a, t125b⟩ := t125; rcases Nat.eq_zero_or_pos n8 with _ | _ <;> rcases t148 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    | (obtain ⟨t125a, t125b⟩ := t125; obtain ⟨qt147, et147⟩ := mod_q t147; clear t147; obtain ⟨qt150, et150⟩ := mod_q t150; clear t150; obtain ⟨qt153, et153⟩ := mod_q t153; clear t153; omega)
    | (obtain ⟨t125a, t125b⟩ := t125; obtain ⟨qt147, et147⟩ := mod_q t147; clear t147; obtain ⟨qt150, et150⟩ := mod_q t150; clear t150; obtain ⟨qt153, et153⟩ := mod_q t153; clear t153; rcases Nat.eq_zero_or_pos n8 with _ | _ <;> rcases t148 with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

theorem psm_v_S24 {v108 v153 v154 v156 : Word}
    (t154 : v154.toNat = (v108.toNat + v153.toNat) % 2 ^ 32)
    (t156 : v154.toNat + 2 ^ 32 * v156.toNat = v108.toNat + v153.toNat) :
    v154.toNat + 2 ^ 32 * v156.toNat = v108.toNat + v153.toNat := by
  have := v108.isLt; have := v153.isLt; have := v154.isLt; have := v156.isLt
  generalize v108.toNat = n108 at *
  generalize v153.toNat = n153 at *
  generalize v154.toNat = n154 at *
  generalize v156.toNat = n156 at *
  first
    | omega
    | (obtain ⟨qt154, et154⟩ := mod_q t154; clear t154; omega)

theorem psm_v_S24l {v108 v153 v154 v156 : Word}
    (t154 : v154.toNat = (v108.toNat + v153.toNat) % 2 ^ 32)
    (wS24 : v154.toNat + 2 ^ 32 * v156.toNat = v108.toNat + v153.toNat) :
    v154.toNat = (v154.toNat + 2 ^ 32 * v156.toNat) % 2 ^ 32 := by
  have := v108.isLt; have := v153.isLt; have := v154.isLt; have := v156.isLt
  generalize v108.toNat = n108 at *
  generalize v153.toNat = n153 at *
  generalize v154.toNat = n154 at *
  generalize v156.toNat = n156 at *
  first
    | omega
    | (obtain ⟨qt154, et154⟩ := mod_q t154; clear t154; omega)

theorem psm_v_S24h {v108 v153 v154 v156 : Word}
    (t156 : v154.toNat + 2 ^ 32 * v156.toNat = v108.toNat + v153.toNat)
    (wS24 : v154.toNat + 2 ^ 32 * v156.toNat = v108.toNat + v153.toNat) :
    v156.toNat = (v154.toNat + 2 ^ 32 * v156.toNat) / 2 ^ 32 := by
  have := v108.isLt; have := v153.isLt; have := v154.isLt; have := v156.isLt
  generalize v108.toNat = n108 at *
  generalize v153.toNat = n153 at *
  generalize v154.toNat = n154 at *
  generalize v156.toNat = n156 at *
  omega

theorem psm_v_S25 {v8 v152 v156 v157 v158 v159 v160 v161 : Word}
    (t157 : v157.toNat = (v8.toNat + v152.toNat) % 2 ^ 32)
    (t158 : v158.toNat = (v156.toNat + v157.toNat) % 2 ^ 32)
    (t159 : v157.toNat + 2 ^ 32 * v159.toNat = v8.toNat + v152.toNat)
    (t160 : v158.toNat + 2 ^ 32 * v160.toNat = v156.toNat + v157.toNat)
    (t161 : v161.toNat = (v159.toNat + v160.toNat) % 2 ^ 32) :
    v158.toNat + 2 ^ 32 * v161.toNat = v152.toNat + v8.toNat + v156.toNat := by
  have := v8.isLt; have := v152.isLt; have := v156.isLt; have := v157.isLt; have := v158.isLt; have := v159.isLt; have := v160.isLt; have := v161.isLt
  generalize v8.toNat = n8 at *
  generalize v152.toNat = n152 at *
  generalize v156.toNat = n156 at *
  generalize v157.toNat = n157 at *
  generalize v158.toNat = n158 at *
  generalize v159.toNat = n159 at *
  generalize v160.toNat = n160 at *
  generalize v161.toNat = n161 at *
  first
    | omega
    | (obtain ⟨qt157, et157⟩ := mod_q t157; clear t157; obtain ⟨qt158, et158⟩ := mod_q t158; clear t158; omega)

theorem psm_v_S25l {v8 v152 v156 v157 v158 v161 : Word}
    (t157 : v157.toNat = (v8.toNat + v152.toNat) % 2 ^ 32)
    (t158 : v158.toNat = (v156.toNat + v157.toNat) % 2 ^ 32)
    (wS25 : v158.toNat + 2 ^ 32 * v161.toNat = v152.toNat + v8.toNat + v156.toNat) :
    v158.toNat = (v158.toNat + 2 ^ 32 * v161.toNat) % 2 ^ 32 := by
  have := v8.isLt; have := v152.isLt; have := v156.isLt; have := v157.isLt; have := v158.isLt; have := v161.isLt
  generalize v8.toNat = n8 at *
  generalize v152.toNat = n152 at *
  generalize v156.toNat = n156 at *
  generalize v157.toNat = n157 at *
  generalize v158.toNat = n158 at *
  generalize v161.toNat = n161 at *
  first
    | omega
    | (obtain ⟨qt157, et157⟩ := mod_q t157; clear t157; obtain ⟨qt158, et158⟩ := mod_q t158; clear t158; omega)

theorem psm_v_S25h {v8 v152 v156 v157 v158 v159 v160 v161 : Word}
    (t157 : v157.toNat = (v8.toNat + v152.toNat) % 2 ^ 32)
    (t159 : v157.toNat + 2 ^ 32 * v159.toNat = v8.toNat + v152.toNat)
    (t160 : v158.toNat + 2 ^ 32 * v160.toNat = v156.toNat + v157.toNat)
    (t161 : v161.toNat = (v159.toNat + v160.toNat) % 2 ^ 32)
    (wS25 : v158.toNat + 2 ^ 32 * v161.toNat = v152.toNat + v8.toNat + v156.toNat) :
    v161.toNat = (v158.toNat + 2 ^ 32 * v161.toNat) / 2 ^ 32 := by
  have := v8.isLt; have := v152.isLt; have := v156.isLt; have := v157.isLt; have := v158.isLt; have := v159.isLt; have := v160.isLt; have := v161.isLt
  generalize v8.toNat = n8 at *
  generalize v152.toNat = n152 at *
  generalize v156.toNat = n156 at *
  generalize v157.toNat = n157 at *
  generalize v158.toNat = n158 at *
  generalize v159.toNat = n159 at *
  generalize v160.toNat = n160 at *
  generalize v161.toNat = n161 at *
  first
    | omega
    | (obtain ⟨qt157, et157⟩ := mod_q t157; clear t157; obtain ⟨qt161, et161⟩ := mod_q t161; clear t161; omega)

theorem psm_v_P26h {v9 v114 v155 v163 v164 v165 v172 v175 : Word}
    (t155 : v155.toNat = v9.toNat * 4007631870 % 2 ^ 32)
    (t163 : v163.toNat = v114.toNat / 2 * 2)
    (t164 : v164.toNat = v9.toNat * 4007631870 / 2 ^ 32)
    (t165 : v165.toNat = (v155.toNat + v163.toNat) % 2 ^ 32)
    (t172 : v165.toNat + 2 ^ 32 * v172.toNat = v155.toNat + v163.toNat)
    (t175 : v175.toNat = (v172.toNat + v164.toNat) % 2 ^ 32) :
    v175.toNat = (v9.toNat * 4007631870 + v114.toNat) / 2 ^ 32 := by
  have := v9.isLt; have := v114.isLt; have := v155.isLt; have := v163.isLt; have := v164.isLt; have := v165.isLt; have := v172.isLt; have := v175.isLt
  generalize v9.toNat = n9 at *
  generalize v114.toNat = n114 at *
  generalize v155.toNat = n155 at *
  generalize v163.toNat = n163 at *
  generalize v164.toNat = n164 at *
  generalize v165.toNat = n165 at *
  generalize v172.toNat = n172 at *
  generalize v175.toNat = n175 at *
  first
    | omega
    | (obtain ⟨qt155, et155⟩ := mod_q t155; clear t155; obtain ⟨qt165, et165⟩ := mod_q t165; clear t165; omega)

end C3.RV32
