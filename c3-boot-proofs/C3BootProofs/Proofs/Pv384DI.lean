import C3BootProofs.Proofs.Pv384GH
import C3BootProofs.Proofs.Pv384D
import C3BootProofs.Proofs.Pv384E0a
import C3BootProofs.Proofs.Pv384E0b
import C3BootProofs.Proofs.Pv384E0c
import C3BootProofs.Proofs.Pv384E1a
import C3BootProofs.Proofs.Pv384E1b
import C3BootProofs.Proofs.Pv384E1c
import C3BootProofs.Proofs.Pv384F0
import C3BootProofs.Proofs.Pv384F1

/-!
# `p384_verify_prehash`: from the inverse of `s` to the result

Stages D to I composed, from 0x730 to the epilogue at 0x130: `u1` and `u2`,
the two tables, the two wNAF forms, the main loop, and the comparison with
`r`.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

/-- The generator, as the image keeps it, in Montgomery form. -/
def pvG : Pt := (dataVal p384GData 0 12, dataVal p384GData 0x30 12, dataVal p384GData 0x60 12)

set_option exponentiation.threshold 600 in
theorem pvG_lt : PtLt pvG := by unfold pvG PtLt p384; decide

/-- The wNAF digits of the scalar `U` in Montgomery form, as stored. -/
def pvD (U : Nat) : List Nat := wnafBytes (wnafGo (n3fm U 1) 0x180 0x181 0 0) 0x181

/-- The number of wNAF digits of the scalar `U` in Montgomery form. -/
def pvL (U : Nat) : Nat := (wnafGo (n3fm U 1) 0x180 0x181 0 0).length

/-- The sum `u1·G + u2·Q` that the main loop leaves, for the key `Q`, `r`
and the prehash in Montgomery form, and `w = s⁻¹`. -/
def pvSum (QX QY RM ZM W : Nat) : Option Pt :=
  mlRun (tblPt pvG) (tblPt (QX, QY, dataVal p384MontOneData 0 12)) (pvD (n3fm ZM W)) (pvD (n3fm RM W))
    (max (pvL (n3fm ZM W)) (pvL (n3fm RM W)))

set_option maxHeartbeats 64000000 in
/-- **Stages D to I**, from 0x730 to 0x130, or a panic in the main loop. -/
theorem pv_stDI {B : Word} {QX QY RM SM ZM W : Nat} {n0 : Machine} (F : Fr B 0x21A0) (E0 : PvEnv7 n0.mem)
    (s0 : St n0.mem PV n0 0x730 (reg n0)) (g0_2 : reg n0 sp = B + 0x420)
    (g0_18 : reg n0 (18 : Fin 32) = B + 0x420 + BitVec.ofNat 32 0x17A4)
    (g0_25 : reg n0 (25 : Fin 32) = B + 0x420 + BitVec.ofNat 32 0xD80)
    (a0_120 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x120) 12 = QX)
    (a0_150 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x150) 12 = QY)
    (a0_180 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x180) 12 = dataVal p384MontOneData 0 12)
    (a0_1b0 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x1B0) 12 = RM)
    (a0_1e0 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x1E0) 12 = SM)
    (a0_210 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x210) 12 = ZM)
    (a0_e10 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0xE10) 12 = W) (hW : W < n384)
    (hQ : PtLt (QX, QY, dataVal p384MontOneData 0 12))
    (hINV : ∀ P, pvSum QX QY RM ZM W = some P → hvOk P.2.2 → hvInv (hvLoop 15 (hvInit P.2.2)) < p384) :
    (pvSum QX QY RM ZM W = none ∧ Panics n0) ∨
    (∃ P, pvSum QX QY RM ZM W = some P ∧
      ∃ n', Steps n0 n' ∧ St n'.mem PV n' 0x130 (reg n') ∧ PvEnv7 n'.mem ∧ (∀ x, PvR B x → n'.mem x = n0.mem x) ∧
        reg n' sp = B + 0x420 ∧ reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧ reg n' a0 = pvH RM P.1 P.2.2) := by
  obtain ⟨n1, t1, s1, E1, f1, g1_2, g1_3, g1_4, g1_18, g1_23, g1_25, a1_120, a1_150, a1_180, a1_1b0, a1_1e0, a1_210, a1_270, a1_2a0, a1_2d0, a1_300, a1_330, a1_360, a1_390, a1_3c0, a1_17a4, a1_17d4, a1_1804, a1_1834, a1_1864, a1_1894, a1_18c4, a1_18f4⟩ :=
    pv_stD (QX := QX) (QY := QY) (QZ := dataVal p384MontOneData 0 12) (RM := RM) (SM := SM) (ZM := ZM) (W := W)
      F E0.E.E.E s0 g0_2 rfl rfl g0_18 g0_25 a0_120 a0_150 a0_180 a0_1b0 a0_1e0 a0_210 a0_e10 hW
  obtain ⟨n2, t2, s2, E2, f2, g2_2, g2_3, g2_4, g2_8, g2_9, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_25, a2_120, a2_150, a2_180, a2_1b0, a2_1e0, a2_210, a2_270, a2_2a0, a2_2d0, a2_300, a2_330, a2_360, a2_390, a2_3c0, a2_d50, a2_d80, a2_db0, a2_de0, a2_e10, a2_e40, a2_e70, a2_ea0, a2_ed0, a2_f00, a2_f30, a2_f60, a2_f90, a2_fc0, a2_ff0, a2_1020, a2_1050, a2_1080, a2_10b0, a2_10e0, a2_1110, a2_1140, a2_1170, a2_11a0, a2_11d0, a2_1200, a2_1230, a2_1260, a2_1294, a2_12c4, a2_12f4, a2_1324, a2_1354, a2_1384, a2_13b4, a2_13e4, a2_1414, a2_1444, a2_1474, a2_14a4, a2_14d4, a2_1504, a2_1534, a2_1564, a2_1594, a2_15c4, a2_15f4, a2_1624, a2_1654, a2_1684, a2_16b4, a2_16e4, a2_1714, a2_1744, a2_1774, a2_17a4, a2_17d4, a2_1804, a2_1834, a2_1864, a2_1894, a2_18c4, a2_18f4⟩ :=
    pv_stE0a (QX := QX) (QY := QY) (QZ := dataVal p384MontOneData 0 12) (RM := RM) (SM := SM) (ZM := ZM) (U1 := n3fm ZM W) (U2 := n3fm RM W) (P0X := dataVal p384GData 0 12) (P0Y := dataVal p384GData 0x30 12) (P0Z := dataVal p384GData 0x60 12) (P1X := QX) (P1Y := QY) (P1Z := dataVal p384MontOneData 0 12)
      F E1 s1 g1_2 rfl rfl g1_18 g1_23 g1_25 a1_120 a1_150 a1_180 a1_1b0 a1_1e0 a1_210 a1_270 a1_2a0 a1_2d0 a1_300 a1_330 a1_360 a1_390 a1_3c0 a1_17a4 a1_17d4 a1_1804 a1_1834 a1_1864 a1_1894 a1_18c4 a1_18f4 pvG_lt
  obtain ⟨n3, t3, s3, E3, f3, g3_2, g3_3, g3_4, g3_8, g3_9, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_25, a3_120, a3_150, a3_180, a3_1b0, a3_1e0, a3_210, a3_270, a3_2a0, a3_2d0, a3_300, a3_330, a3_360, a3_390, a3_3c0, a3_d50, a3_d80, a3_db0, a3_de0, a3_e10, a3_e40, a3_e70, a3_ea0, a3_ed0, a3_f00, a3_f30, a3_f60, a3_f90, a3_fc0, a3_ff0, a3_1020, a3_1050, a3_1080, a3_10b0, a3_10e0, a3_1110, a3_1140, a3_1170, a3_11a0, a3_11d0, a3_1200, a3_1230, a3_1260, a3_1294, a3_12c4, a3_12f4, a3_1324, a3_1354, a3_1384, a3_13b4, a3_13e4, a3_1414, a3_1444, a3_1474, a3_14a4, a3_14d4, a3_1504, a3_1534, a3_1564, a3_1594, a3_15c4, a3_15f4, a3_1624, a3_1654, a3_1684, a3_16b4, a3_16e4, a3_1714, a3_1744, a3_1774, a3_17a4, a3_17d4, a3_1804, a3_1834, a3_1864, a3_1894, a3_18c4, a3_18f4⟩ :=
    pv_stE0b (QX := QX) (QY := QY) (QZ := dataVal p384MontOneData 0 12) (RM := RM) (SM := SM) (ZM := ZM) (U1 := n3fm ZM W) (U2 := n3fm RM W) (P0X := dataVal p384GData 0 12) (P0Y := dataVal p384GData 0x30 12) (P0Z := dataVal p384GData 0x60 12) (P1X := QX) (P1Y := QY) (P1Z := dataVal p384MontOneData 0 12)
      F E2 s2 g2_2 rfl rfl g2_8 g2_9 g2_18 g2_19 g2_20 g2_21 g2_22 g2_23 g2_25 a2_120 a2_150 a2_180 a2_1b0 a2_1e0 a2_210 a2_270 a2_2a0 a2_2d0 a2_300 a2_330 a2_360 a2_390 a2_3c0 a2_d50 a2_d80 a2_db0 a2_de0 a2_e10 a2_e40 a2_e70 a2_ea0 a2_ed0 a2_f00 a2_f30 a2_f60 a2_f90 a2_fc0 a2_ff0 a2_1020 a2_1050 a2_1080 a2_10b0 a2_10e0 a2_1110 a2_1140 a2_1170 a2_11a0 a2_11d0 a2_1200 a2_1230 a2_1260 a2_1294 a2_12c4 a2_12f4 a2_1324 a2_1354 a2_1384 a2_13b4 a2_13e4 a2_1414 a2_1444 a2_1474 a2_14a4 a2_14d4 a2_1504 a2_1534 a2_1564 a2_1594 a2_15c4 a2_15f4 a2_1624 a2_1654 a2_1684 a2_16b4 a2_16e4 a2_1714 a2_1744 a2_1774 a2_17a4 a2_17d4 a2_1804 a2_1834 a2_1864 a2_1894 a2_18c4 a2_18f4 pvG_lt
  obtain ⟨n4, t4, s4, E4, f4, g4_2, g4_3, g4_4, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_25, a4_120, a4_150, a4_180, a4_1b0, a4_1e0, a4_210, a4_270, a4_2a0, a4_2d0, a4_300, a4_330, a4_360, a4_390, a4_3c0, a4_17a4, a4_17d4, a4_1804, a4_1834, a4_1864, a4_1894, a4_18c4, a4_18f4, tb4_450⟩ :=
    pv_stE0c (QX := QX) (QY := QY) (QZ := dataVal p384MontOneData 0 12) (RM := RM) (SM := SM) (ZM := ZM) (U1 := n3fm ZM W) (U2 := n3fm RM W) (P0X := dataVal p384GData 0 12) (P0Y := dataVal p384GData 0x30 12) (P0Z := dataVal p384GData 0x60 12) (P1X := QX) (P1Y := QY) (P1Z := dataVal p384MontOneData 0 12)
      F E3 s3 g3_2 rfl rfl g3_8 g3_9 g3_18 g3_19 g3_20 g3_21 g3_22 g3_23 g3_25 a3_120 a3_150 a3_180 a3_1b0 a3_1e0 a3_210 a3_270 a3_2a0 a3_2d0 a3_300 a3_330 a3_360 a3_390 a3_3c0 a3_d50 a3_d80 a3_db0 a3_de0 a3_e10 a3_e40 a3_e70 a3_ea0 a3_ed0 a3_f00 a3_f30 a3_f60 a3_f90 a3_fc0 a3_ff0 a3_1020 a3_1050 a3_1080 a3_10b0 a3_10e0 a3_1110 a3_1140 a3_1170 a3_11a0 a3_11d0 a3_1200 a3_1230 a3_1260 a3_1294 a3_12c4 a3_12f4 a3_1324 a3_1354 a3_1384 a3_13b4 a3_13e4 a3_1414 a3_1444 a3_1474 a3_14a4 a3_14d4 a3_1504 a3_1534 a3_1564 a3_1594 a3_15c4 a3_15f4 a3_1624 a3_1654 a3_1684 a3_16b4 a3_16e4 a3_1714 a3_1744 a3_1774 a3_17a4 a3_17d4 a3_1804 a3_1834 a3_1864 a3_1894 a3_18c4 a3_18f4 pvG_lt
  obtain ⟨n5, t5, s5, E5, f5, g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_25, a5_120, a5_150, a5_180, a5_1b0, a5_1e0, a5_210, a5_270, a5_2a0, a5_2d0, a5_300, a5_330, a5_360, a5_390, a5_3c0, a5_d50, a5_d80, a5_db0, a5_de0, a5_e10, a5_e40, a5_e70, a5_ea0, a5_ed0, a5_f00, a5_f30, a5_f60, a5_f90, a5_fc0, a5_ff0, a5_1020, a5_1050, a5_1080, a5_10b0, a5_10e0, a5_1110, a5_1140, a5_1170, a5_11a0, a5_11d0, a5_1200, a5_1230, a5_1260, a5_1294, a5_12c4, a5_12f4, a5_1324, a5_1354, a5_1384, a5_13b4, a5_13e4, a5_1414, a5_1444, a5_1474, a5_14a4, a5_14d4, a5_1504, a5_1534, a5_1564, a5_1594, a5_15c4, a5_15f4, a5_1624, a5_1654, a5_1684, a5_16b4, a5_16e4, a5_1714, a5_1744, a5_1774, a5_17a4, a5_17d4, a5_1804, a5_1834, a5_1864, a5_1894, a5_18c4, a5_18f4, tb5_450⟩ :=
    pv_stE1a (QX := QX) (QY := QY) (QZ := dataVal p384MontOneData 0 12) (RM := RM) (SM := SM) (ZM := ZM) (U1 := n3fm ZM W) (U2 := n3fm RM W) (P0X := dataVal p384GData 0 12) (P0Y := dataVal p384GData 0x30 12) (P0Z := dataVal p384GData 0x60 12) (P1X := QX) (P1Y := QY) (P1Z := dataVal p384MontOneData 0 12)
      F E4 s4 g4_2 rfl rfl g4_18 g4_19 g4_20 g4_21 g4_22 g4_23 g4_25 a4_120 a4_150 a4_180 a4_1b0 a4_1e0 a4_210 a4_270 a4_2a0 a4_2d0 a4_300 a4_330 a4_360 a4_390 a4_3c0 a4_17a4 a4_17d4 a4_1804 a4_1834 a4_1864 a4_1894 a4_18c4 a4_18f4 tb4_450 hQ
  obtain ⟨n6, t6, s6, E6, f6, g6_2, g6_3, g6_4, g6_8, g6_9, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_25, a6_120, a6_150, a6_180, a6_1b0, a6_1e0, a6_210, a6_270, a6_2a0, a6_2d0, a6_300, a6_330, a6_360, a6_390, a6_3c0, a6_d50, a6_d80, a6_db0, a6_de0, a6_e10, a6_e40, a6_e70, a6_ea0, a6_ed0, a6_f00, a6_f30, a6_f60, a6_f90, a6_fc0, a6_ff0, a6_1020, a6_1050, a6_1080, a6_10b0, a6_10e0, a6_1110, a6_1140, a6_1170, a6_11a0, a6_11d0, a6_1200, a6_1230, a6_1260, a6_1294, a6_12c4, a6_12f4, a6_1324, a6_1354, a6_1384, a6_13b4, a6_13e4, a6_1414, a6_1444, a6_1474, a6_14a4, a6_14d4, a6_1504, a6_1534, a6_1564, a6_1594, a6_15c4, a6_15f4, a6_1624, a6_1654, a6_1684, a6_16b4, a6_16e4, a6_1714, a6_1744, a6_1774, a6_17a4, a6_17d4, a6_1804, a6_1834, a6_1864, a6_1894, a6_18c4, a6_18f4, tb6_450⟩ :=
    pv_stE1b (QX := QX) (QY := QY) (QZ := dataVal p384MontOneData 0 12) (RM := RM) (SM := SM) (ZM := ZM) (U1 := n3fm ZM W) (U2 := n3fm RM W) (P0X := dataVal p384GData 0 12) (P0Y := dataVal p384GData 0x30 12) (P0Z := dataVal p384GData 0x60 12) (P1X := QX) (P1Y := QY) (P1Z := dataVal p384MontOneData 0 12)
      F E5 s5 g5_2 rfl rfl g5_8 g5_9 g5_18 g5_19 g5_20 g5_21 g5_22 g5_23 g5_25 a5_120 a5_150 a5_180 a5_1b0 a5_1e0 a5_210 a5_270 a5_2a0 a5_2d0 a5_300 a5_330 a5_360 a5_390 a5_3c0 a5_d50 a5_d80 a5_db0 a5_de0 a5_e10 a5_e40 a5_e70 a5_ea0 a5_ed0 a5_f00 a5_f30 a5_f60 a5_f90 a5_fc0 a5_ff0 a5_1020 a5_1050 a5_1080 a5_10b0 a5_10e0 a5_1110 a5_1140 a5_1170 a5_11a0 a5_11d0 a5_1200 a5_1230 a5_1260 a5_1294 a5_12c4 a5_12f4 a5_1324 a5_1354 a5_1384 a5_13b4 a5_13e4 a5_1414 a5_1444 a5_1474 a5_14a4 a5_14d4 a5_1504 a5_1534 a5_1564 a5_1594 a5_15c4 a5_15f4 a5_1624 a5_1654 a5_1684 a5_16b4 a5_16e4 a5_1714 a5_1744 a5_1774 a5_17a4 a5_17d4 a5_1804 a5_1834 a5_1864 a5_1894 a5_18c4 a5_18f4 tb5_450 hQ
  obtain ⟨n7, t7, s7, E7, f7, g7_2, g7_3, g7_4, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_25, a7_120, a7_150, a7_180, a7_1b0, a7_1e0, a7_210, a7_270, a7_2a0, a7_2d0, a7_300, a7_330, a7_360, a7_390, a7_3c0, a7_17a4, a7_17d4, a7_1804, a7_1834, a7_1864, a7_1894, a7_18c4, a7_18f4, tb7_450, tb7_8d0⟩ :=
    pv_stE1c (QX := QX) (QY := QY) (QZ := dataVal p384MontOneData 0 12) (RM := RM) (SM := SM) (ZM := ZM) (U1 := n3fm ZM W) (U2 := n3fm RM W) (P0X := dataVal p384GData 0 12) (P0Y := dataVal p384GData 0x30 12) (P0Z := dataVal p384GData 0x60 12) (P1X := QX) (P1Y := QY) (P1Z := dataVal p384MontOneData 0 12)
      F E6 s6 g6_2 rfl rfl g6_8 g6_9 g6_18 g6_19 g6_20 g6_21 g6_22 g6_23 g6_25 a6_120 a6_150 a6_180 a6_1b0 a6_1e0 a6_210 a6_270 a6_2a0 a6_2d0 a6_300 a6_330 a6_360 a6_390 a6_3c0 a6_d50 a6_d80 a6_db0 a6_de0 a6_e10 a6_e40 a6_e70 a6_ea0 a6_ed0 a6_f00 a6_f30 a6_f60 a6_f90 a6_fc0 a6_ff0 a6_1020 a6_1050 a6_1080 a6_10b0 a6_10e0 a6_1110 a6_1140 a6_1170 a6_11a0 a6_11d0 a6_1200 a6_1230 a6_1260 a6_1294 a6_12c4 a6_12f4 a6_1324 a6_1354 a6_1384 a6_13b4 a6_13e4 a6_1414 a6_1444 a6_1474 a6_14a4 a6_14d4 a6_1504 a6_1534 a6_1564 a6_1594 a6_15c4 a6_15f4 a6_1624 a6_1654 a6_1684 a6_16b4 a6_16e4 a6_1714 a6_1744 a6_1774 a6_17a4 a6_17d4 a6_1804 a6_1834 a6_1864 a6_1894 a6_18c4 a6_18f4 tb6_450 hQ
  have fRe : ∀ x, PvR B x → n7.mem x = n0.mem x := fun x hx => by rw [f7 x hx, f6 x hx, f5 x hx, f4 x hx, f3 x hx, f2 x hx, f1 x hx]
  obtain ⟨n8, t8, s8, E8, f8, g8_2, g8_3, g8_4, g8_9, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, x8_1, a8_120, a8_150, a8_180, a8_1b0, a8_1e0, a8_210, a8_270, a8_2a0, a8_2d0, a8_300, a8_330, a8_360, a8_390, a8_3c0, a8_17a4, a8_17d4, a8_1804, a8_1834, a8_1864, a8_1894, a8_18c4, a8_18f4, w8_e10, w8_1294, w8_1924, ln8_d50, mb8_e14, mb8_1298, mb8_1928, tb8_450, tb8_8d0⟩ :=
    pv_stF0 (QX := QX) (QY := QY) (QZ := dataVal p384MontOneData 0 12) (RM := RM) (SM := SM) (ZM := ZM) (U1 := n3fm ZM W) (U2 := n3fm RM W) (P0X := dataVal p384GData 0 12) (P0Y := dataVal p384GData 0x30 12) (P0Z := dataVal p384GData 0x60 12) (P1X := QX) (P1Y := QY) (P1Z := dataVal p384MontOneData 0 12)
      F (E0.E.E.fr F fRe) s7 g7_2 rfl rfl g7_25 a7_120 a7_150 a7_180 a7_1b0 a7_1e0 a7_210 a7_270 a7_2a0 a7_2d0 a7_300 a7_330 a7_360 a7_390 a7_3c0 a7_17a4 a7_17d4 a7_1804 a7_1834 a7_1864 a7_1894 a7_18c4 a7_18f4 tb7_450 tb7_8d0 (Nat.mod_lt _ n384_pos)
  obtain ⟨n9, t9, s9, E9, f9, g9_2, g9_3, g9_4, g9_9, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, x9_1, a9_120, a9_150, a9_180, a9_1b0, a9_1e0, a9_210, w9_e10, w9_1294, w9_1924, w9_1aac, ln9_d50, mb9_e14, mb9_1298, mb9_1928, mb9_1ab0, tb9_450, tb9_8d0⟩ :=
    pv_stF1 (QX := QX) (QY := QY) (QZ := dataVal p384MontOneData 0 12) (RM := RM) (SM := SM) (ZM := ZM) (U1 := n3fm ZM W) (U2 := n3fm RM W) (P0X := dataVal p384GData 0 12) (P0Y := dataVal p384GData 0x30 12) (P0Z := dataVal p384GData 0x60 12) (P1X := QX) (P1Y := QY) (P1Z := dataVal p384MontOneData 0 12)
      F E8 s8 g8_2 rfl rfl g8_9 g8_18 g8_19 g8_20 g8_21 g8_22 g8_23 g8_24 g8_25 a8_120 a8_150 a8_180 a8_1b0 a8_1e0 a8_210 a8_270 a8_2a0 a8_2d0 a8_300 a8_330 a8_360 a8_390 a8_3c0 a8_17a4 a8_17d4 a8_1804 a8_1834 a8_1864 a8_1894 a8_18c4 a8_18f4 w8_1924 mb8_1928 tb8_450 tb8_8d0 (Nat.mod_lt _ n384_pos)
  have fR9 : ∀ x, PvR B x → n9.mem x = n0.mem x := fun x hx => by rw [f9 x hx, f8 x hx, fRe x hx]
  have hG : ((dataVal p384GData 0 12, dataVal p384GData 0x30 12, dataVal p384GData 0x60 12) : Pt) = pvG := rfl
  rw [hG] at tb9_450
  have M9 : GM B n9.mem (tblPt pvG) (tblPt (QX, QY, dataVal p384MontOneData 0 12)) (pvD (n3fm ZM W))
      (pvD (n3fm RM W)) RM :=
    ⟨tb9_450, tb9_8d0, fun j _ => ⟨tblPt_lt pvG_lt j, tblPt_lt hQ j⟩, mb9_1928, mb9_1ab0, a9_1b0⟩
  rcases pv_stGH F (E0.fr F fR9) s9 g9_2 w9_1924 w9_1aac x8_1 x9_1 M9 hINV with
    ⟨hn, hp⟩ | ⟨P, hP, n10, t10, s10, E10, f10, sp10, r310, r410, a10⟩
  · exact .inl ⟨hn, Panics.of_steps (t1.trans (t2.trans (t3.trans (t4.trans (t5.trans (t6.trans (t7.trans (t8.trans t9)))))))) hp⟩
  · exact .inr ⟨P, hP, n10, t1.trans (t2.trans (t3.trans (t4.trans (t5.trans (t6.trans (t7.trans (t8.trans (t9.trans t10)))))))), s10, E10,
      fun x hx => by rw [f10 x hx, fR9 x hx], sp10, by rw [r310, g9_3, g8_3, g7_3, g6_3, g5_3, g4_3, g3_3, g2_3, g1_3],
      by rw [r410, g9_4, g8_4, g7_4, g6_4, g5_4, g4_4, g3_4, g2_4, g1_4], a10⟩

end C3.RV32.Pv
