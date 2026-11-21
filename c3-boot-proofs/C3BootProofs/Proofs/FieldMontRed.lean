import C3BootProofs.Proofs.FieldMont

/-! # The Montgomery reduction in `FieldElement::multiply`, as compiled

`scripts/gen-mont-red.py` writes this file from the decoded instructions. -/

namespace C3.RV32

open C3.Image

/-- The registers the reduction block leaves alone. -/
def fmRedKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 28, 29, 30, 31]

theorem wordsAt16 (M : Word → BitVec 8) (b : Word) :
    wordsAt M b 16 = [memLoad32 M (b + 0x0), memLoad32 M (b + 0x4), memLoad32 M (b + 0x8), memLoad32 M (b + 0xC),
      memLoad32 M (b + 0x10), memLoad32 M (b + 0x14), memLoad32 M (b + 0x18), memLoad32 M (b + 0x1C),
      memLoad32 M (b + 0x20), memLoad32 M (b + 0x24), memLoad32 M (b + 0x28), memLoad32 M (b + 0x2C),
      memLoad32 M (b + 0x30), memLoad32 M (b + 0x34), memLoad32 M (b + 0x38), memLoad32 M (b + 0x3C)] := rfl

theorem limbFlat9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Word) :
    limbVal [a0, a1, a2, a3, a4, a5, a6, a7, a8] =
      2 ^ 0 * a0.toNat + 2 ^ 32 * a1.toNat + 2 ^ 64 * a2.toNat + 2 ^ 96 * a3.toNat + 2 ^ 128 * a4.toNat + 2 ^ 160 * a5.toNat + 2 ^ 192 * a6.toNat + 2 ^ 224 * a7.toNat + 2 ^ 256 * a8.toNat := by
  simp only [limbVal, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add, Nat.mul_zero, Nat.add_zero]
  omega

theorem limbFlat16 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Word) :
    limbVal [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] =
      2 ^ 0 * a0.toNat + 2 ^ 32 * a1.toNat + 2 ^ 64 * a2.toNat + 2 ^ 96 * a3.toNat + 2 ^ 128 * a4.toNat + 2 ^ 160 * a5.toNat + 2 ^ 192 * a6.toNat + 2 ^ 224 * a7.toNat + 2 ^ 256 * a8.toNat + 2 ^ 288 * a9.toNat + 2 ^ 320 * a10.toNat + 2 ^ 352 * a11.toNat + 2 ^ 384 * a12.toNat + 2 ^ 416 * a13.toNat + 2 ^ 448 * a14.toNat + 2 ^ 480 * a15.toNat := by
  simp only [limbVal, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add, Nat.mul_zero, Nat.add_zero]
  omega

set_option maxHeartbeats 4000000 in
/-- The eight rounds summed: the reduction's output words times `2^256` are
the product plus `q · p`. -/
theorem mont_tele (v0 v1 v2 v3 v4 v5 v6 v7 v8 v10 v11 v12 v13 v14 v18 v19 v20 v21 v22 v26 v33 v34 v38 v39 v41 v45 v46 v52 v56 v60 v61 v63 v68 v74 v77 v80 v83 v84 v87 v91 v92 v98 v102 v106 v107 v109 v114 v120 v123 v126 v129 v130 v133 v137 v138 v144 v148 v152 v153 v155 v160 v166 v169 v172 v175 v176 v179 v183 v184 v190 v195 v198 : Word)
    (R0 : v8.toNat + 2 ^ 32 * v14.toNat + 2 ^ 64 * v22.toNat + 2 ^ 96 * v26.toNat + 2 ^ 128 * v33.toNat + 2 ^ 160 * v39.toNat + 2 ^ 192 * v45.toNat + 2 ^ 128 * v0.toNat = v1.toNat + 2 ^ 32 * v4.toNat + 2 ^ 64 * v5.toNat + 2 ^ 96 * v6.toNat + 2 ^ 128 * v7.toNat + 2 ^ 160 * v10.toNat + 2 ^ 160 * 0 + v0.toNat * (1 + 2 ^ 96 + 2 ^ 160))
    (R1 : v34.toNat + 2 ^ 32 * v38.toNat + 2 ^ 64 * v41.toNat + 2 ^ 96 * v46.toNat + 2 ^ 128 * v52.toNat + 2 ^ 160 * v61.toNat + 2 ^ 192 * v77.toNat + 2 ^ 128 * v2.toNat = v14.toNat + 2 ^ 32 * v22.toNat + 2 ^ 64 * v26.toNat + 2 ^ 96 * v33.toNat + 2 ^ 128 * v39.toNat + 2 ^ 160 * v11.toNat + 2 ^ 160 * v45.toNat + v2.toNat * (1 + 2 ^ 96 + 2 ^ 160))
    (R2 : v56.toNat + 2 ^ 32 * v60.toNat + 2 ^ 64 * v63.toNat + 2 ^ 96 * v68.toNat + 2 ^ 128 * v74.toNat + 2 ^ 160 * v83.toNat + 2 ^ 192 * v91.toNat + 2 ^ 128 * v3.toNat = v38.toNat + 2 ^ 32 * v41.toNat + 2 ^ 64 * v46.toNat + 2 ^ 96 * v52.toNat + 2 ^ 128 * v61.toNat + 2 ^ 160 * v12.toNat + 2 ^ 160 * v77.toNat + v3.toNat * (1 + 2 ^ 96 + 2 ^ 160))
    (R3 : v80.toNat + 2 ^ 32 * v84.toNat + 2 ^ 64 * v87.toNat + 2 ^ 96 * v92.toNat + 2 ^ 128 * v98.toNat + 2 ^ 160 * v107.toNat + 2 ^ 192 * v123.toNat + 2 ^ 128 * v8.toNat = v60.toNat + 2 ^ 32 * v63.toNat + 2 ^ 64 * v68.toNat + 2 ^ 96 * v74.toNat + 2 ^ 128 * v83.toNat + 2 ^ 160 * v13.toNat + 2 ^ 160 * v91.toNat + v8.toNat * (1 + 2 ^ 96 + 2 ^ 160))
    (R4 : v102.toNat + 2 ^ 32 * v106.toNat + 2 ^ 64 * v109.toNat + 2 ^ 96 * v114.toNat + 2 ^ 128 * v120.toNat + 2 ^ 160 * v129.toNat + 2 ^ 192 * v137.toNat + 2 ^ 128 * v34.toNat = v84.toNat + 2 ^ 32 * v87.toNat + 2 ^ 64 * v92.toNat + 2 ^ 96 * v98.toNat + 2 ^ 128 * v107.toNat + 2 ^ 160 * v18.toNat + 2 ^ 160 * v123.toNat + v34.toNat * (1 + 2 ^ 96 + 2 ^ 160))
    (R5 : v126.toNat + 2 ^ 32 * v130.toNat + 2 ^ 64 * v133.toNat + 2 ^ 96 * v138.toNat + 2 ^ 128 * v144.toNat + 2 ^ 160 * v153.toNat + 2 ^ 192 * v169.toNat + 2 ^ 128 * v56.toNat = v106.toNat + 2 ^ 32 * v109.toNat + 2 ^ 64 * v114.toNat + 2 ^ 96 * v120.toNat + 2 ^ 128 * v129.toNat + 2 ^ 160 * v19.toNat + 2 ^ 160 * v137.toNat + v56.toNat * (1 + 2 ^ 96 + 2 ^ 160))
    (R6 : v148.toNat + 2 ^ 32 * v152.toNat + 2 ^ 64 * v155.toNat + 2 ^ 96 * v160.toNat + 2 ^ 128 * v166.toNat + 2 ^ 160 * v175.toNat + 2 ^ 192 * v183.toNat + 2 ^ 128 * v80.toNat = v130.toNat + 2 ^ 32 * v133.toNat + 2 ^ 64 * v138.toNat + 2 ^ 96 * v144.toNat + 2 ^ 128 * v153.toNat + 2 ^ 160 * v20.toNat + 2 ^ 160 * v169.toNat + v80.toNat * (1 + 2 ^ 96 + 2 ^ 160))
    (R7 : v172.toNat + 2 ^ 32 * v176.toNat + 2 ^ 64 * v179.toNat + 2 ^ 96 * v184.toNat + 2 ^ 128 * v190.toNat + 2 ^ 160 * v195.toNat + 2 ^ 192 * v198.toNat + 2 ^ 128 * v102.toNat = v152.toNat + 2 ^ 32 * v155.toNat + 2 ^ 64 * v160.toNat + 2 ^ 96 * v166.toNat + 2 ^ 128 * v175.toNat + 2 ^ 160 * v21.toNat + 2 ^ 160 * v183.toNat + v102.toNat * (1 + 2 ^ 96 + 2 ^ 160))
    : limbVal [v126, v148, v172, v176, v179, v184, v190, v195, v198] * 2 ^ 256 =
      limbVal [v0, v2, v3, v1, v4, v5, v6, v7, v10, v11, v12, v13, v18, v19, v20, v21] +
        (2 ^ 0 * v0.toNat + 2 ^ 32 * v2.toNat + 2 ^ 64 * v3.toNat + 2 ^ 96 * v8.toNat + 2 ^ 128 * v34.toNat + 2 ^ 160 * v56.toNat + 2 ^ 192 * v80.toNat + 2 ^ 224 * v102.toNat) * p256 := by
  rw [limbFlat9, limbFlat16, show p256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951 from rfl]
  omega

theorem mq_bound (a0 a1 a2 a3 a4 a5 a6 a7 : Word) :
    2 ^ 0 * a0.toNat + 2 ^ 32 * a1.toNat + 2 ^ 64 * a2.toNat + 2 ^ 96 * a3.toNat + 2 ^ 128 * a4.toNat +
      2 ^ 160 * a5.toNat + 2 ^ 192 * a6.toNat + 2 ^ 224 * a7.toNat < 2 ^ 256 := by
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt
  have := a4.isLt; have := a5.isLt; have := a6.isLt; have := a7.isLt
  omega

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **The compiled Montgomery reduction**, the straight-line block from 0x20 to 0x28C
of `FieldElement::multiply`: from the 16-word product at `G`, the nine words it
leaves for `sub_inner` times `2^256` are the product plus `q · p` for some
`q < 2^256`. -/
theorem fm_red {M : Word → BitVec 8} {B G : Word} {n : Machine} (s : St M B n 0x20 (reg n))
    (hc : CodeIn M B fieldMulCode) (hsp : reg n sp = G) (hG : G.toNat % 4 = 0) :
    ∃ n', Steps n n' ∧ St M B n' 0x28C (reg n') ∧
      (∃ q, q < 2 ^ 256 ∧ limbVal [reg n' (7 : Fin 32), reg n' (6 : Fin 32), reg n' (5 : Fin 32), reg n' a5,
        reg n' a4, reg n' a0, reg n' a1, reg n' a2, reg n' a3] * 2 ^ 256 = limbVal (wordsAt M G 16) + q * p256) ∧
      reg n' (19 : Fin 32) = 0xFFFFFFFF ∧ ∀ q, fmRedKeep q = true → reg n' q = reg n q := by
  obtain ⟨n0, v0, d0, hv0, u0⟩ := s.lwG hc fm_at_20 (off' := 0x22) (by decide)
    (by rw [hsp]; exact aligned_add hG (k := 0) (by decide))
  rw [hsp] at hv0
  obtain ⟨n1, v1, d1, hv1, u1⟩ := u0.lwG hc fm_at_22 (off' := 0x24) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := 12) (by decide))
  simp +decide only [upd, ↓reduceIte, hsp] at hv1
  obtain ⟨n2, v2, d2, hv2, u2⟩ := u1.lwG hc fm_at_24 (off' := 0x26) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := 4) (by decide))
  simp +decide only [upd, ↓reduceIte, hsp] at hv2
  obtain ⟨n3, v3, d3, hv3, u3⟩ := u2.lwG hc fm_at_26 (off' := 0x28) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := 8) (by decide))
  simp +decide only [upd, ↓reduceIte, hsp] at hv3
  obtain ⟨n4, v4, d4, hv4, u4⟩ := u3.lwG hc fm_at_28 (off' := 0x2A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := 16) (by decide))
  simp +decide only [upd, ↓reduceIte, hsp] at hv4
  obtain ⟨n5, v5, d5, hv5, u5⟩ := u4.lwG hc fm_at_2a (off' := 0x2C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := 20) (by decide))
  simp +decide only [upd, ↓reduceIte, hsp] at hv5
  obtain ⟨n6, v6, d6, hv6, u6⟩ := u5.lwG hc fm_at_2c (off' := 0x2E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := 24) (by decide))
  simp +decide only [upd, ↓reduceIte, hsp] at hv6
  obtain ⟨n7, v7, d7, hv7, u7⟩ := u6.lwG hc fm_at_2e (off' := 0x30) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := 28) (by decide))
  simp +decide only [upd, ↓reduceIte, hsp] at hv7
  obtain ⟨n8, v8, d8, hv8, u8⟩ := u7.aluG hc fm_at_30 (off' := 0x34) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv8
  obtain ⟨n9, v9, d9, hv9, u9⟩ := u8.aluG hc fm_at_34 (off' := 0x38) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv9
  obtain ⟨n10, v10, d10, hv10, u10⟩ := u9.lwG hc fm_at_38 (off' := 0x3A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := 32) (by decide))
  simp +decide only [upd, ↓reduceIte, hsp] at hv10
  obtain ⟨n11, v11, d11, hv11, u11⟩ := u10.lwG hc fm_at_3a (off' := 0x3C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := 36) (by decide))
  simp +decide only [upd, ↓reduceIte, hsp] at hv11
  obtain ⟨n12, v12, d12, hv12, u12⟩ := u11.lwG hc fm_at_3c (off' := 0x3E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := 40) (by decide))
  simp +decide only [upd, ↓reduceIte, hsp] at hv12
  obtain ⟨n13, v13, d13, hv13, u13⟩ := u12.lwG hc fm_at_3e (off' := 0x40) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := 44) (by decide))
  simp +decide only [upd, ↓reduceIte, hsp] at hv13
  obtain ⟨n14, v14, d14, hv14, u14⟩ := u13.aluG hc fm_at_40 (off' := 0x42) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv14
  obtain ⟨n15, v15, d15, hv15, u15⟩ := u14.aluG hc fm_at_42 (off' := 0x46) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv15
  obtain ⟨n16, v16, d16, hv16, u16⟩ := u15.aluImmG hc fm_at_46 (off' := 0x48) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv16
  obtain ⟨n17, v17, d17, hv17, u17⟩ := u16.aluG hc fm_at_48 (off' := 0x4C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv17
  obtain ⟨n18, v18, d18, hv18, u18⟩ := u17.lwG hc fm_at_4c (off' := 0x4E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := 48) (by decide))
  simp +decide only [upd, ↓reduceIte, hsp] at hv18
  obtain ⟨n19, v19, d19, hv19, u19⟩ := u18.lwG hc fm_at_4e (off' := 0x50) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := 52) (by decide))
  simp +decide only [upd, ↓reduceIte, hsp] at hv19
  obtain ⟨n20, v20, d20, hv20, u20⟩ := u19.lwG hc fm_at_50 (off' := 0x52) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := 56) (by decide))
  simp +decide only [upd, ↓reduceIte, hsp] at hv20
  obtain ⟨n21, v21, d21, hv21, u21⟩ := u20.lwG hc fm_at_52 (off' := 0x54) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := 60) (by decide))
  simp +decide only [upd, ↓reduceIte, hsp] at hv21
  obtain ⟨n22, v22, d22, hv22, u22⟩ := u21.aluG hc fm_at_54 (off' := 0x56) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv22
  obtain ⟨n23, v23, d23, hv23, u23⟩ := u22.aluG hc fm_at_56 (off' := 0x5A) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv23
  obtain ⟨n24, v24, d24, hv24, u24⟩ := u23.aluG hc fm_at_5a (off' := 0x5E) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv24
  obtain ⟨n25, v25, d25, hv25, u25⟩ := u24.aluG hc fm_at_5e (off' := 0x62) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv25
  obtain ⟨n26, v26, d26, hv26, u26⟩ := u25.aluG hc fm_at_62 (off' := 0x64) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv26
  obtain ⟨n27, v27, d27, hv27, u27⟩ := u26.aluG hc fm_at_64 (off' := 0x68) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv27
  obtain ⟨n28, v28, d28, hv28, u28⟩ := u27.aluG hc fm_at_68 (off' := 0x6C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv28
  obtain ⟨n29, v29, d29, hv29, u29⟩ := u28.aluG hc fm_at_6c (off' := 0x70) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv29
  obtain ⟨n30, v30, d30, hv30, u30⟩ := u29.aluG hc fm_at_70 (off' := 0x74) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv30
  obtain ⟨n31, v31, d31, hv31, u31⟩ := u30.aluG hc fm_at_74 (off' := 0x76) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv31
  obtain ⟨n32, v32, d32, hv32, u32⟩ := u31.aluG hc fm_at_76 (off' := 0x78) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv32
  obtain ⟨n33, v33, d33, hv33, u33⟩ := u32.aluG hc fm_at_78 (off' := 0x7C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv33
  obtain ⟨n34, v34, d34, hv34, u34⟩ := u33.aluG hc fm_at_7c (off' := 0x80) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv34
  obtain ⟨n35, v35, d35, hv35, u35⟩ := u34.aluG hc fm_at_80 (off' := 0x84) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv35
  obtain ⟨n36, v36, d36, hv36, u36⟩ := u35.aluG hc fm_at_84 (off' := 0x88) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv36
  obtain ⟨n37, v37, d37, hv37, u37⟩ := u36.aluG hc fm_at_88 (off' := 0x8A) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv37
  obtain ⟨n38, v38, d38, hv38, u38⟩ := u37.aluG hc fm_at_8a (off' := 0x8C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv38
  obtain ⟨n39, v39, d39, hv39, u39⟩ := u38.aluG hc fm_at_8c (off' := 0x8E) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv39
  obtain ⟨n40, v40, d40, hv40, u40⟩ := u39.aluG hc fm_at_8e (off' := 0x92) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv40
  obtain ⟨n41, v41, d41, hv41, u41⟩ := u40.aluG hc fm_at_92 (off' := 0x94) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv41
  obtain ⟨n42, v42, d42, hv42, u42⟩ := u41.aluG hc fm_at_94 (off' := 0x98) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv42
  obtain ⟨n43, v43, d43, hv43, u43⟩ := u42.aluG hc fm_at_98 (off' := 0x9C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv43
  obtain ⟨n44, v44, d44, hv44, u44⟩ := u43.aluG hc fm_at_9c (off' := 0xA0) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv44
  obtain ⟨n45, v45, d45, hv45, u45⟩ := u44.aluG hc fm_at_a0 (off' := 0xA4) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv45
  obtain ⟨n46, v46, d46, hv46, u46⟩ := u45.aluG hc fm_at_a4 (off' := 0xA6) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv46
  obtain ⟨n47, v47, d47, hv47, u47⟩ := u46.aluG hc fm_at_a6 (off' := 0xAA) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv47
  obtain ⟨n48, v48, d48, hv48, u48⟩ := u47.aluG hc fm_at_aa (off' := 0xAE) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv48
  obtain ⟨n49, v49, d49, hv49, u49⟩ := u48.aluG hc fm_at_ae (off' := 0xB0) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv49
  obtain ⟨n50, v50, d50, hv50, u50⟩ := u49.aluG hc fm_at_b0 (off' := 0xB4) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv50
  obtain ⟨n51, v51, d51, hv51, u51⟩ := u50.aluG hc fm_at_b4 (off' := 0xB8) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv51
  obtain ⟨n52, v52, d52, hv52, u52⟩ := u51.aluG hc fm_at_b8 (off' := 0xBC) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv52
  obtain ⟨n53, v53, d53, hv53, u53⟩ := u52.aluG hc fm_at_bc (off' := 0xBE) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv53
  obtain ⟨n54, v54, d54, hv54, u54⟩ := u53.aluG hc fm_at_be (off' := 0xC2) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv54
  obtain ⟨n55, v55, d55, hv55, u55⟩ := u54.aluG hc fm_at_c2 (off' := 0xC4) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv55
  obtain ⟨n56, v56, d56, hv56, u56⟩ := u55.aluG hc fm_at_c4 (off' := 0xC8) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv56
  obtain ⟨n57, v57, d57, hv57, u57⟩ := u56.aluG hc fm_at_c8 (off' := 0xCA) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv57
  obtain ⟨n58, v58, d58, hv58, u58⟩ := u57.aluG hc fm_at_ca (off' := 0xCE) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv58
  obtain ⟨n59, v59, d59, hv59, u59⟩ := u58.aluG hc fm_at_ce (off' := 0xD2) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv59
  obtain ⟨n60, v60, d60, hv60, u60⟩ := u59.aluG hc fm_at_d2 (off' := 0xD4) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv60
  obtain ⟨n61, v61, d61, hv61, u61⟩ := u60.aluG hc fm_at_d4 (off' := 0xD6) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv61
  obtain ⟨n62, v62, d62, hv62, u62⟩ := u61.aluG hc fm_at_d6 (off' := 0xDA) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv62
  obtain ⟨n63, v63, d63, hv63, u63⟩ := u62.aluG hc fm_at_da (off' := 0xDC) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv63
  obtain ⟨n64, v64, d64, hv64, u64⟩ := u63.aluG hc fm_at_dc (off' := 0xE0) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv64
  obtain ⟨n65, v65, d65, hv65, u65⟩ := u64.aluG hc fm_at_e0 (off' := 0xE4) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv65
  obtain ⟨n66, v66, d66, hv66, u66⟩ := u65.aluG hc fm_at_e4 (off' := 0xE8) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv66
  obtain ⟨n67, v67, d67, hv67, u67⟩ := u66.aluG hc fm_at_e8 (off' := 0xEC) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv67
  obtain ⟨n68, v68, d68, hv68, u68⟩ := u67.aluG hc fm_at_ec (off' := 0xEE) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv68
  obtain ⟨n69, v69, d69, hv69, u69⟩ := u68.aluG hc fm_at_ee (off' := 0xF2) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv69
  obtain ⟨n70, v70, d70, hv70, u70⟩ := u69.aluG hc fm_at_f2 (off' := 0xF6) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv70
  obtain ⟨n71, v71, d71, hv71, u71⟩ := u70.aluG hc fm_at_f6 (off' := 0xF8) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv71
  obtain ⟨n72, v72, d72, hv72, u72⟩ := u71.aluG hc fm_at_f8 (off' := 0xFC) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv72
  obtain ⟨n73, v73, d73, hv73, u73⟩ := u72.aluG hc fm_at_fc (off' := 0x100) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv73
  obtain ⟨n74, v74, d74, hv74, u74⟩ := u73.aluG hc fm_at_100 (off' := 0x104) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv74
  obtain ⟨n75, v75, d75, hv75, u75⟩ := u74.aluG hc fm_at_104 (off' := 0x106) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv75
  obtain ⟨n76, v76, d76, hv76, u76⟩ := u75.aluG hc fm_at_106 (off' := 0x10A) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv76
  obtain ⟨n77, v77, d77, hv77, u77⟩ := u76.aluG hc fm_at_10a (off' := 0x10C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv77
  obtain ⟨n78, v78, d78, hv78, u78⟩ := u77.aluG hc fm_at_10c (off' := 0x10E) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv78
  obtain ⟨n79, v79, d79, hv79, u79⟩ := u78.aluG hc fm_at_10e (off' := 0x110) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv79
  obtain ⟨n80, v80, d80, hv80, u80⟩ := u79.aluG hc fm_at_110 (off' := 0x114) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv80
  obtain ⟨n81, v81, d81, hv81, u81⟩ := u80.aluG hc fm_at_114 (off' := 0x118) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv81
  obtain ⟨n82, v82, d82, hv82, u82⟩ := u81.aluG hc fm_at_118 (off' := 0x11C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv82
  obtain ⟨n83, v83, d83, hv83, u83⟩ := u82.aluG hc fm_at_11c (off' := 0x11E) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv83
  obtain ⟨n84, v84, d84, hv84, u84⟩ := u83.aluG hc fm_at_11e (off' := 0x120) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv84
  obtain ⟨n85, v85, d85, hv85, u85⟩ := u84.aluG hc fm_at_120 (off' := 0x124) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv85
  obtain ⟨n86, v86, d86, hv86, u86⟩ := u85.aluG hc fm_at_124 (off' := 0x128) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv86
  obtain ⟨n87, v87, d87, hv87, u87⟩ := u86.aluG hc fm_at_128 (off' := 0x12A) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv87
  obtain ⟨n88, v88, d88, hv88, u88⟩ := u87.aluG hc fm_at_12a (off' := 0x12E) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv88
  obtain ⟨n89, v89, d89, hv89, u89⟩ := u88.aluG hc fm_at_12e (off' := 0x132) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv89
  obtain ⟨n90, v90, d90, hv90, u90⟩ := u89.aluG hc fm_at_132 (off' := 0x136) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv90
  obtain ⟨n91, v91, d91, hv91, u91⟩ := u90.aluG hc fm_at_136 (off' := 0x138) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv91
  obtain ⟨n92, v92, d92, hv92, u92⟩ := u91.aluG hc fm_at_138 (off' := 0x13A) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv92
  obtain ⟨n93, v93, d93, hv93, u93⟩ := u92.aluG hc fm_at_13a (off' := 0x13E) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv93
  obtain ⟨n94, v94, d94, hv94, u94⟩ := u93.aluG hc fm_at_13e (off' := 0x142) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv94
  obtain ⟨n95, v95, d95, hv95, u95⟩ := u94.aluG hc fm_at_142 (off' := 0x144) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv95
  obtain ⟨n96, v96, d96, hv96, u96⟩ := u95.aluG hc fm_at_144 (off' := 0x148) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv96
  obtain ⟨n97, v97, d97, hv97, u97⟩ := u96.aluG hc fm_at_148 (off' := 0x14C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv97
  obtain ⟨n98, v98, d98, hv98, u98⟩ := u97.aluG hc fm_at_14c (off' := 0x150) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv98
  obtain ⟨n99, v99, d99, hv99, u99⟩ := u98.aluG hc fm_at_150 (off' := 0x152) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv99
  obtain ⟨n100, v100, d100, hv100, u100⟩ := u99.aluG hc fm_at_152 (off' := 0x156) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv100
  obtain ⟨n101, v101, d101, hv101, u101⟩ := u100.aluG hc fm_at_156 (off' := 0x158) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv101
  obtain ⟨n102, v102, d102, hv102, u102⟩ := u101.aluG hc fm_at_158 (off' := 0x15C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv102
  obtain ⟨n103, v103, d103, hv103, u103⟩ := u102.aluG hc fm_at_15c (off' := 0x15E) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv103
  obtain ⟨n104, v104, d104, hv104, u104⟩ := u103.aluG hc fm_at_15e (off' := 0x162) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv104
  obtain ⟨n105, v105, d105, hv105, u105⟩ := u104.aluG hc fm_at_162 (off' := 0x166) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv105
  obtain ⟨n106, v106, d106, hv106, u106⟩ := u105.aluG hc fm_at_166 (off' := 0x168) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv106
  obtain ⟨n107, v107, d107, hv107, u107⟩ := u106.aluG hc fm_at_168 (off' := 0x16A) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv107
  obtain ⟨n108, v108, d108, hv108, u108⟩ := u107.aluG hc fm_at_16a (off' := 0x16E) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv108
  obtain ⟨n109, v109, d109, hv109, u109⟩ := u108.aluG hc fm_at_16e (off' := 0x170) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv109
  obtain ⟨n110, v110, d110, hv110, u110⟩ := u109.aluG hc fm_at_170 (off' := 0x174) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv110
  obtain ⟨n111, v111, d111, hv111, u111⟩ := u110.aluG hc fm_at_174 (off' := 0x178) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv111
  obtain ⟨n112, v112, d112, hv112, u112⟩ := u111.aluG hc fm_at_178 (off' := 0x17C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv112
  obtain ⟨n113, v113, d113, hv113, u113⟩ := u112.aluG hc fm_at_17c (off' := 0x180) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv113
  obtain ⟨n114, v114, d114, hv114, u114⟩ := u113.aluG hc fm_at_180 (off' := 0x182) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv114
  obtain ⟨n115, v115, d115, hv115, u115⟩ := u114.aluG hc fm_at_182 (off' := 0x186) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv115
  obtain ⟨n116, v116, d116, hv116, u116⟩ := u115.aluG hc fm_at_186 (off' := 0x18A) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv116
  obtain ⟨n117, v117, d117, hv117, u117⟩ := u116.aluG hc fm_at_18a (off' := 0x18C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv117
  obtain ⟨n118, v118, d118, hv118, u118⟩ := u117.aluG hc fm_at_18c (off' := 0x190) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv118
  obtain ⟨n119, v119, d119, hv119, u119⟩ := u118.aluG hc fm_at_190 (off' := 0x194) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv119
  obtain ⟨n120, v120, d120, hv120, u120⟩ := u119.aluG hc fm_at_194 (off' := 0x198) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv120
  obtain ⟨n121, v121, d121, hv121, u121⟩ := u120.aluG hc fm_at_198 (off' := 0x19A) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv121
  obtain ⟨n122, v122, d122, hv122, u122⟩ := u121.aluG hc fm_at_19a (off' := 0x19E) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv122
  obtain ⟨n123, v123, d123, hv123, u123⟩ := u122.aluG hc fm_at_19e (off' := 0x1A0) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv123
  obtain ⟨n124, v124, d124, hv124, u124⟩ := u123.aluG hc fm_at_1a0 (off' := 0x1A2) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv124
  obtain ⟨n125, v125, d125, hv125, u125⟩ := u124.aluG hc fm_at_1a2 (off' := 0x1A4) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv125
  obtain ⟨n126, v126, d126, hv126, u126⟩ := u125.aluG hc fm_at_1a4 (off' := 0x1A8) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv126
  obtain ⟨n127, v127, d127, hv127, u127⟩ := u126.aluG hc fm_at_1a8 (off' := 0x1AC) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv127
  obtain ⟨n128, v128, d128, hv128, u128⟩ := u127.aluG hc fm_at_1ac (off' := 0x1B0) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv128
  obtain ⟨n129, v129, d129, hv129, u129⟩ := u128.aluG hc fm_at_1b0 (off' := 0x1B2) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv129
  obtain ⟨n130, v130, d130, hv130, u130⟩ := u129.aluG hc fm_at_1b2 (off' := 0x1B4) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv130
  obtain ⟨n131, v131, d131, hv131, u131⟩ := u130.aluG hc fm_at_1b4 (off' := 0x1B8) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv131
  obtain ⟨n132, v132, d132, hv132, u132⟩ := u131.aluG hc fm_at_1b8 (off' := 0x1BC) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv132
  obtain ⟨n133, v133, d133, hv133, u133⟩ := u132.aluG hc fm_at_1bc (off' := 0x1BE) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv133
  obtain ⟨n134, v134, d134, hv134, u134⟩ := u133.aluG hc fm_at_1be (off' := 0x1C2) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv134
  obtain ⟨n135, v135, d135, hv135, u135⟩ := u134.aluG hc fm_at_1c2 (off' := 0x1C6) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv135
  obtain ⟨n136, v136, d136, hv136, u136⟩ := u135.aluG hc fm_at_1c6 (off' := 0x1CA) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv136
  obtain ⟨n137, v137, d137, hv137, u137⟩ := u136.aluG hc fm_at_1ca (off' := 0x1CC) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv137
  obtain ⟨n138, v138, d138, hv138, u138⟩ := u137.aluG hc fm_at_1cc (off' := 0x1CE) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv138
  obtain ⟨n139, v139, d139, hv139, u139⟩ := u138.aluG hc fm_at_1ce (off' := 0x1D2) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv139
  obtain ⟨n140, v140, d140, hv140, u140⟩ := u139.aluG hc fm_at_1d2 (off' := 0x1D6) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv140
  obtain ⟨n141, v141, d141, hv141, u141⟩ := u140.aluG hc fm_at_1d6 (off' := 0x1D8) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv141
  obtain ⟨n142, v142, d142, hv142, u142⟩ := u141.aluG hc fm_at_1d8 (off' := 0x1DC) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv142
  obtain ⟨n143, v143, d143, hv143, u143⟩ := u142.aluG hc fm_at_1dc (off' := 0x1E0) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv143
  obtain ⟨n144, v144, d144, hv144, u144⟩ := u143.aluG hc fm_at_1e0 (off' := 0x1E4) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv144
  obtain ⟨n145, v145, d145, hv145, u145⟩ := u144.aluG hc fm_at_1e4 (off' := 0x1E6) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv145
  obtain ⟨n146, v146, d146, hv146, u146⟩ := u145.aluG hc fm_at_1e6 (off' := 0x1EA) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv146
  obtain ⟨n147, v147, d147, hv147, u147⟩ := u146.aluG hc fm_at_1ea (off' := 0x1EC) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv147
  obtain ⟨n148, v148, d148, hv148, u148⟩ := u147.aluG hc fm_at_1ec (off' := 0x1F0) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv148
  obtain ⟨n149, v149, d149, hv149, u149⟩ := u148.aluG hc fm_at_1f0 (off' := 0x1F2) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv149
  obtain ⟨n150, v150, d150, hv150, u150⟩ := u149.aluG hc fm_at_1f2 (off' := 0x1F6) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv150
  obtain ⟨n151, v151, d151, hv151, u151⟩ := u150.aluG hc fm_at_1f6 (off' := 0x1FA) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv151
  obtain ⟨n152, v152, d152, hv152, u152⟩ := u151.aluG hc fm_at_1fa (off' := 0x1FC) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv152
  obtain ⟨n153, v153, d153, hv153, u153⟩ := u152.aluG hc fm_at_1fc (off' := 0x1FE) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv153
  obtain ⟨n154, v154, d154, hv154, u154⟩ := u153.aluG hc fm_at_1fe (off' := 0x202) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv154
  obtain ⟨n155, v155, d155, hv155, u155⟩ := u154.aluG hc fm_at_202 (off' := 0x204) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv155
  obtain ⟨n156, v156, d156, hv156, u156⟩ := u155.aluG hc fm_at_204 (off' := 0x208) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv156
  obtain ⟨n157, v157, d157, hv157, u157⟩ := u156.aluG hc fm_at_208 (off' := 0x20C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv157
  obtain ⟨n158, v158, d158, hv158, u158⟩ := u157.aluG hc fm_at_20c (off' := 0x210) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv158
  obtain ⟨n159, v159, d159, hv159, u159⟩ := u158.aluG hc fm_at_210 (off' := 0x214) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv159
  obtain ⟨n160, v160, d160, hv160, u160⟩ := u159.aluG hc fm_at_214 (off' := 0x216) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv160
  obtain ⟨n161, v161, d161, hv161, u161⟩ := u160.aluG hc fm_at_216 (off' := 0x21A) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv161
  obtain ⟨n162, v162, d162, hv162, u162⟩ := u161.aluG hc fm_at_21a (off' := 0x21E) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv162
  obtain ⟨n163, v163, d163, hv163, u163⟩ := u162.aluG hc fm_at_21e (off' := 0x220) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv163
  obtain ⟨n164, v164, d164, hv164, u164⟩ := u163.aluG hc fm_at_220 (off' := 0x224) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv164
  obtain ⟨n165, v165, d165, hv165, u165⟩ := u164.aluG hc fm_at_224 (off' := 0x228) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv165
  obtain ⟨n166, v166, d166, hv166, u166⟩ := u165.aluG hc fm_at_228 (off' := 0x22C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv166
  obtain ⟨n167, v167, d167, hv167, u167⟩ := u166.aluG hc fm_at_22c (off' := 0x22E) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv167
  obtain ⟨n168, v168, d168, hv168, u168⟩ := u167.aluG hc fm_at_22e (off' := 0x232) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv168
  obtain ⟨n169, v169, d169, hv169, u169⟩ := u168.aluG hc fm_at_232 (off' := 0x234) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv169
  obtain ⟨n170, v170, d170, hv170, u170⟩ := u169.aluG hc fm_at_234 (off' := 0x236) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv170
  obtain ⟨n171, v171, d171, hv171, u171⟩ := u170.aluG hc fm_at_236 (off' := 0x238) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv171
  obtain ⟨n172, v172, d172, hv172, u172⟩ := u171.aluG hc fm_at_238 (off' := 0x23C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv172
  obtain ⟨n173, v173, d173, hv173, u173⟩ := u172.aluG hc fm_at_23c (off' := 0x240) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv173
  obtain ⟨n174, v174, d174, hv174, u174⟩ := u173.aluG hc fm_at_240 (off' := 0x244) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv174
  obtain ⟨n175, v175, d175, hv175, u175⟩ := u174.aluG hc fm_at_244 (off' := 0x246) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv175
  obtain ⟨n176, v176, d176, hv176, u176⟩ := u175.aluG hc fm_at_246 (off' := 0x248) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv176
  obtain ⟨n177, v177, d177, hv177, u177⟩ := u176.aluG hc fm_at_248 (off' := 0x24C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv177
  obtain ⟨n178, v178, d178, hv178, u178⟩ := u177.aluG hc fm_at_24c (off' := 0x250) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv178
  obtain ⟨n179, v179, d179, hv179, u179⟩ := u178.aluG hc fm_at_250 (off' := 0x252) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv179
  obtain ⟨n180, v180, d180, hv180, u180⟩ := u179.aluG hc fm_at_252 (off' := 0x256) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv180
  obtain ⟨n181, v181, d181, hv181, u181⟩ := u180.aluG hc fm_at_256 (off' := 0x25A) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv181
  obtain ⟨n182, v182, d182, hv182, u182⟩ := u181.aluG hc fm_at_25a (off' := 0x25E) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv182
  obtain ⟨n183, v183, d183, hv183, u183⟩ := u182.aluG hc fm_at_25e (off' := 0x260) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv183
  obtain ⟨n184, v184, d184, hv184, u184⟩ := u183.aluG hc fm_at_260 (off' := 0x262) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv184
  obtain ⟨n185, v185, d185, hv185, u185⟩ := u184.aluG hc fm_at_262 (off' := 0x266) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv185
  obtain ⟨n186, v186, d186, hv186, u186⟩ := u185.aluG hc fm_at_266 (off' := 0x26A) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv186
  obtain ⟨n187, v187, d187, hv187, u187⟩ := u186.aluG hc fm_at_26a (off' := 0x26C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv187
  obtain ⟨n188, v188, d188, hv188, u188⟩ := u187.aluG hc fm_at_26c (off' := 0x270) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv188
  obtain ⟨n189, v189, d189, hv189, u189⟩ := u188.aluG hc fm_at_270 (off' := 0x274) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv189
  obtain ⟨n190, v190, d190, hv190, u190⟩ := u189.aluG hc fm_at_274 (off' := 0x276) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv190
  obtain ⟨n191, v191, d191, hv191, u191⟩ := u190.aluG hc fm_at_276 (off' := 0x278) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv191
  obtain ⟨n192, v192, d192, hv192, u192⟩ := u191.aluG hc fm_at_278 (off' := 0x27C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv192
  obtain ⟨n193, v193, d193, hv193, u193⟩ := u192.aluG hc fm_at_27c (off' := 0x27E) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv193
  obtain ⟨n194, v194, d194, hv194, u194⟩ := u193.aluG hc fm_at_27e (off' := 0x280) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv194
  obtain ⟨n195, v195, d195, hv195, u195⟩ := u194.aluG hc fm_at_280 (off' := 0x282) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv195
  obtain ⟨n196, v196, d196, hv196, u196⟩ := u195.aluG hc fm_at_282 (off' := 0x286) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv196
  obtain ⟨n197, v197, d197, hv197, u197⟩ := u196.aluG hc fm_at_286 (off' := 0x28A) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv197
  obtain ⟨n198, v198, d198, hv198, u198⟩ := u197.aluG hc fm_at_28a (off' := 0x28C) (by decide)
  simp +decide only [upd, ↓reduceIte] at hv198
  have o7 : reg n198 (7 : Fin 32) = v126 := by rw [u198.regs]; simp +decide only [upd, ↓reduceIte]
  have o6 : reg n198 (6 : Fin 32) = v148 := by rw [u198.regs]; simp +decide only [upd, ↓reduceIte]
  have o5 : reg n198 (5 : Fin 32) = v172 := by rw [u198.regs]; simp +decide only [upd, ↓reduceIte]
  have o15 : reg n198 a5 = v176 := by rw [u198.regs]; simp +decide only [upd, ↓reduceIte]
  have o14 : reg n198 a4 = v179 := by rw [u198.regs]; simp +decide only [upd, ↓reduceIte]
  have o10 : reg n198 a0 = v184 := by rw [u198.regs]; simp +decide only [upd, ↓reduceIte]
  have o11 : reg n198 a1 = v190 := by rw [u198.regs]; simp +decide only [upd, ↓reduceIte]
  have o12 : reg n198 a2 = v195 := by rw [u198.regs]; simp +decide only [upd, ↓reduceIte]
  have o13 : reg n198 a3 = v198 := by rw [u198.regs]; simp +decide only [upd, ↓reduceIte]
  have o19 : reg n198 (19 : Fin 32) = v16 := by rw [u198.regs]; simp +decide only [upd, ↓reduceIte]
  have s3e : v16 = 0xFFFFFFFF := by rw [← hv16]; rfl
  rw [s3e] at hv17
  rw [s3e] at hv42
  rw [s3e] at hv64
  rw [s3e] at hv88
  rw [s3e] at hv110
  rw [s3e] at hv134
  rw [s3e] at hv156
  rw [s3e] at hv180
  have E0_r3 := fmP1 hv8 (.inl hv9)
  have E0_r4 := fmP1 hv14 (.inr hv15)
  have E0_r5 := fmP1 hv22 (.inr hv23)
  have E0_r6 := fmP3 hv24 (.inl hv25) (.inl hv26) hv29 (.inl hv31)
  have E0_r7 := fmP4 (sb := v30) (c := v37) hv27 hv17 (.inr (by rw [hv28]; exact hv30)) (.inl hv33) hv35 (.inl (by rw [← hv37, ← hv32]))
  have E0_r8 : v39.toNat + 2 ^ 32 * v45.toNat = v10.toNat + 0 + v37.toNat := by
    rw [Nat.add_zero]; exact fmP1 hv39 (.inr hv45)
  have E1_r3 := fmP1 hv34 (.inl hv36)
  have E1_r4 := fmP1s hv38 (.inr hv40)
  have E1_r5 := fmP1s hv41 (.inr hv43)
  have E1_r6 := fmP3 hv44 (.inl hv47) (.inl hv46) hv48 (.inl hv49)
  have E1_r7 := fmP4 (sb := v51) (c := v55) hv50 hv42 (.inl hv51) (.inl hv52) hv54 (.inr (.inr (.inr (by rw [← hv55, ← hv53]))))
  have E1_r8 := fmP3 hv57 (.inr hv59) (.inl hv61) hv67 (.inl hv77)
  have E2_r3 := fmP1 hv56 (.inl hv58)
  have E2_r4 := fmP1s hv60 (.inr hv62)
  have E2_r5 := fmP1s hv63 (.inr hv65)
  have E2_r6 := fmP3 hv66 (.inl hv69) (.inl hv68) hv70 (.inl hv71)
  have E2_r7 := fmP4 (sb := v73) (c := v78) hv72 hv64 (.inl hv73) (.inl hv74) hv76 (.inr (.inr (.inl (by rw [← hv78, ← hv75]))))
  have E2_r8 := fmP3 hv79 (.inr hv81) (.inl hv83) hv85 (.inr hv91)
  have E3_r3 := fmP1 hv80 (.inl hv82)
  have E3_r4 := fmP1s hv84 (.inr hv86)
  have E3_r5 := fmP1s hv87 (.inr hv89)
  have E3_r6 := fmP3 hv90 (.inl hv93) (.inl hv92) hv94 (.inl hv95)
  have E3_r7 := fmP4 (sb := v97) (c := v101) hv96 hv88 (.inl hv97) (.inl hv98) hv100 (.inr (.inl (by rw [← hv101, ← hv99])))
  have E3_r8 := fmP3 hv103 (.inr hv105) (.inl hv107) hv113 (.inr hv123)
  have E4_r3 := fmP1 hv102 (.inl hv104)
  have E4_r4 := fmP1s hv106 (.inr hv108)
  have E4_r5 := fmP1s hv109 (.inr hv111)
  have E4_r6 := fmP3 hv112 (.inl hv115) (.inl hv114) hv116 (.inl hv117)
  have E4_r7 := fmP4 (sb := v119) (c := v124) hv118 hv110 (.inl hv119) (.inl hv120) hv122 (.inr (.inl (by rw [← hv124, ← hv121])))
  have E4_r8 := fmP3 hv125 (.inr hv127) (.inl hv129) hv131 (.inr hv137)
  have E5_r3 := fmP1 hv126 (.inl hv128)
  have E5_r4 := fmP1s hv130 (.inr hv132)
  have E5_r5 := fmP1s hv133 (.inr hv135)
  have E5_r6 := fmP3 hv136 (.inl hv139) (.inl hv138) hv140 (.inl hv141)
  have E5_r7 := fmP4 (sb := v143) (c := v147) hv142 hv134 (.inl hv143) (.inl hv144) hv146 (.inl (by rw [← hv147, ← hv145]))
  have E5_r8 := fmP3 hv149 (.inr hv151) (.inl hv153) hv159 (.inr hv169)
  have E6_r3 := fmP1 hv148 (.inl hv150)
  have E6_r4 := fmP1s hv152 (.inr hv154)
  have E6_r5 := fmP1s hv155 (.inr hv157)
  have E6_r6 := fmP3 hv158 (.inl hv161) (.inl hv160) hv162 (.inl hv163)
  have E6_r7 := fmP4 (sb := v165) (c := v170) hv164 hv156 (.inl hv165) (.inl hv166) hv168 (.inr (.inr (.inr (by rw [← hv170, ← hv167]))))
  have E6_r8 := fmP3 hv171 (.inr hv173) (.inl hv175) hv177 (.inr hv183)
  have E7_r3 := fmP1 hv172 (.inl hv174)
  have E7_r4 := fmP1s hv176 (.inr hv178)
  have E7_r5 := fmP1s hv179 (.inr hv181)
  have E7_r6 := fmP3 hv182 (.inl hv185) (.inl hv184) hv186 (.inl hv187)
  have E7_r7 := fmP4 (sb := v189) (c := v193) hv188 hv180 (.inl hv189) (.inr hv190) hv192 (.inr (.inr (.inl (by rw [← hv193, ← hv191]))))
  have E7_r8 := fmP3 hv194 (.inr hv196) (.inl hv195) hv197 (.inr hv198)
  have R0 := mont_round E0_r3 E0_r4 E0_r5 E0_r6 E0_r7 E0_r8
  have R1 := mont_round E1_r3 E1_r4 E1_r5 E1_r6 E1_r7 E1_r8
  have R2 := mont_round E2_r3 E2_r4 E2_r5 E2_r6 E2_r7 E2_r8
  have R3 := mont_round E3_r3 E3_r4 E3_r5 E3_r6 E3_r7 E3_r8
  have R4 := mont_round E4_r3 E4_r4 E4_r5 E4_r6 E4_r7 E4_r8
  have R5 := mont_round E5_r3 E5_r4 E5_r5 E5_r6 E5_r7 E5_r8
  have R6 := mont_round E6_r3 E6_r4 E6_r5 E6_r6 E6_r7 E6_r8
  have R7 := mont_round E7_r3 E7_r4 E7_r5 E7_r6 E7_r7 E7_r8
  clear E0_r3 E0_r4 E0_r5 E0_r6 E0_r7 E0_r8 E1_r3 E1_r4 E1_r5 E1_r6 E1_r7 E1_r8 E2_r3 E2_r4 E2_r5 E2_r6 E2_r7 E2_r8 E3_r3 E3_r4 E3_r5 E3_r6 E3_r7 E3_r8 E4_r3 E4_r4 E4_r5 E4_r6 E4_r7 E4_r8 E5_r3 E5_r4 E5_r5 E5_r6 E5_r7 E5_r8 E6_r3 E6_r4 E6_r5 E6_r6 E6_r7 E6_r8 E7_r3 E7_r4 E7_r5 E7_r6 E7_r7 E7_r8
  refine ⟨n198, (.cons d0 (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.cons d18 (.cons d19 (.cons d20 (.cons d21 (.cons d22 (.cons d23 (.cons d24 (.cons d25 (.cons d26 (.cons d27 (.cons d28 (.cons d29 (.cons d30 (.cons d31 (.cons d32 (.cons d33 (.cons d34 (.cons d35 (.cons d36 (.cons d37 (.cons d38 (.cons d39 (.cons d40 (.cons d41 (.cons d42 (.cons d43 (.cons d44 (.cons d45 (.cons d46 (.cons d47 (.cons d48 (.cons d49 (.cons d50 (.cons d51 (.cons d52 (.cons d53 (.cons d54 (.cons d55 (.cons d56 (.cons d57 (.cons d58 (.cons d59 (.cons d60 (.cons d61 (.cons d62 (.cons d63 (.cons d64 (.cons d65 (.cons d66 (.cons d67 (.cons d68 (.cons d69 (.cons d70 (.cons d71 (.cons d72 (.cons d73 (.cons d74 (.cons d75 (.cons d76 (.cons d77 (.cons d78 (.cons d79 (.cons d80 (.cons d81 (.cons d82 (.cons d83 (.cons d84 (.cons d85 (.cons d86 (.cons d87 (.cons d88 (.cons d89 (.cons d90 (.cons d91 (.cons d92 (.cons d93 (.cons d94 (.cons d95 (.cons d96 (.cons d97 (.cons d98 (.cons d99 (.cons d100 (.cons d101 (.cons d102 (.cons d103 (.cons d104 (.cons d105 (.cons d106 (.cons d107 (.cons d108 (.cons d109 (.cons d110 (.cons d111 (.cons d112 (.cons d113 (.cons d114 (.cons d115 (.cons d116 (.cons d117 (.cons d118 (.cons d119 (.cons d120 (.cons d121 (.cons d122 (.cons d123 (.cons d124 (.cons d125 (.cons d126 (.cons d127 (.cons d128 (.cons d129 (.cons d130 (.cons d131 (.cons d132 (.cons d133 (.cons d134 (.cons d135 (.cons d136 (.cons d137 (.cons d138 (.cons d139 (.cons d140 (.cons d141 (.cons d142 (.cons d143 (.cons d144 (.cons d145 (.cons d146 (.cons d147 (.cons d148 (.cons d149 (.cons d150 (.cons d151 (.cons d152 (.cons d153 (.cons d154 (.cons d155 (.cons d156 (.cons d157 (.cons d158 (.cons d159 (.cons d160 (.cons d161 (.cons d162 (.cons d163 (.cons d164 (.cons d165 (.cons d166 (.cons d167 (.cons d168 (.cons d169 (.cons d170 (.cons d171 (.cons d172 (.cons d173 (.cons d174 (.cons d175 (.cons d176 (.cons d177 (.cons d178 (.cons d179 (.cons d180 (.cons d181 (.cons d182 (.cons d183 (.cons d184 (.cons d185 (.cons d186 (.cons d187 (.cons d188 (.cons d189 (.cons d190 (.cons d191 (.cons d192 (.cons d193 (.cons d194 (.cons d195 (.cons d196 (.cons d197 (.single d198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), u198.self, ?_, o19.trans s3e, ?_⟩
  · refine ⟨2 ^ 0 * v0.toNat + 2 ^ 32 * v2.toNat + 2 ^ 64 * v3.toNat + 2 ^ 96 * v8.toNat + 2 ^ 128 * v34.toNat + 2 ^ 160 * v56.toNat + 2 ^ 192 * v80.toNat + 2 ^ 224 * v102.toNat, mq_bound v0 v2 v3 v8 v34 v56 v80 v102, ?_⟩
    rw [o7, o6, o5, o15, o14, o10, o11, o12, o13, wordsAt16, hv0, hv2, hv3, hv1, hv4, hv5, hv6, hv7, hv10, hv11, hv12, hv13, hv18, hv19, hv20, hv21]
    exact mont_tele v0 v1 v2 v3 v4 v5 v6 v7 v8 v10 v11 v12 v13 v14 v18 v19 v20 v21 v22 v26 v33 v34 v38 v39 v41 v45 v46 v52 v56 v60 v61 v63 v68 v74 v77 v80 v83 v84 v87 v91 v92 v98 v102 v106 v107 v109 v114 v120 v123 v126 v129 v130 v133 v137 v138 v144 v148 v152 v153 v155 v160 v166 v169 v172 v175 v176 v179 v183 v184 v190 v195 v198 R0 R1 R2 R3 R4 R5 R6 R7
  · intro q hq
    rw [u198.regs]
    have ⟨q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q23, q28, q29, q30, q31⟩ : q ≠ (5 : Fin 32) ∧ q ≠ (6 : Fin 32) ∧ q ≠ (7 : Fin 32) ∧ q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ (19 : Fin 32) ∧ q ≠ (20 : Fin 32) ∧ q ≠ (21 : Fin 32) ∧ q ≠ (22 : Fin 32) ∧ q ≠ (23 : Fin 32) ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ (31 : Fin 32) :=
      ⟨bkeep_ne hq (r := (5 : Fin 32)) rfl, bkeep_ne hq (r := (6 : Fin 32)) rfl, bkeep_ne hq (r := (7 : Fin 32)) rfl, bkeep_ne hq (r := (8 : Fin 32)) rfl, bkeep_ne hq (r := (9 : Fin 32)) rfl, bkeep_ne hq (r := a0) rfl, bkeep_ne hq (r := a1) rfl, bkeep_ne hq (r := a2) rfl, bkeep_ne hq (r := a3) rfl, bkeep_ne hq (r := a4) rfl, bkeep_ne hq (r := a5) rfl, bkeep_ne hq (r := a6) rfl, bkeep_ne hq (r := a7) rfl, bkeep_ne hq (r := (19 : Fin 32)) rfl, bkeep_ne hq (r := (20 : Fin 32)) rfl, bkeep_ne hq (r := (21 : Fin 32)) rfl, bkeep_ne hq (r := (22 : Fin 32)) rfl, bkeep_ne hq (r := (23 : Fin 32)) rfl, bkeep_ne hq (r := (28 : Fin 32)) rfl, bkeep_ne hq (r := (29 : Fin 32)) rfl, bkeep_ne hq (r := (30 : Fin 32)) rfl, bkeep_ne hq (r := (31 : Fin 32)) rfl⟩
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact s.zero.symm
    · simp [upd, h0, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q19, q20, q21, q22, q23, q28, q29, q30, q31]

end C3.RV32
