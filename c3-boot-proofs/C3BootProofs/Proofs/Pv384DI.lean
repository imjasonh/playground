import C3BootProofs.Proofs.Pv384GH
import C3BootProofs.Proofs.Pv384D
import C3BootProofs.Proofs.Pv384E0
import C3BootProofs.Proofs.Pv384E1
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

theorem ptV_of {M : Word → BitVec 8} {B : Word} {c : Nat} {P : Pt}
    (h1 : accV M (B + 0x420 + BitVec.ofNat 32 c) 12 = P.1)
    (h2 : accV M (B + 0x420 + BitVec.ofNat 32 (c + 0x30)) 12 = P.2.1)
    (h3 : accV M (B + 0x420 + BitVec.ofNat 32 (c + 0x60)) 12 = P.2.2) : ptV M B c = P := by
  unfold ptV; rw [h1, h2, h3]

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
  obtain ⟨n2, t2, s2, E2, f2, g2_2, g2_3, g2_4, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_25, a2_120, a2_150, a2_180, a2_1b0, a2_1e0, a2_210, a2_270, a2_2a0, a2_2d0, a2_300, a2_330, a2_360, a2_390, a2_3c0, a2_450, a2_480, a2_4b0, a2_4e0, a2_510, a2_540, a2_570, a2_5a0, a2_5d0, a2_600, a2_630, a2_660, a2_690, a2_6c0, a2_6f0, a2_720, a2_750, a2_780, a2_7b0, a2_7e0, a2_810, a2_840, a2_870, a2_8a0, a2_17a4, a2_17d4, a2_1804, a2_1834, a2_1864, a2_1894, a2_18c4, a2_18f4⟩ :=
    pv_stE0 (QX := QX) (QY := QY) (QZ := dataVal p384MontOneData 0 12) (RM := RM) (SM := SM) (ZM := ZM) (U1 := n3fm ZM W) (U2 := n3fm RM W) (P0X := dataVal p384GData 0 12) (P0Y := dataVal p384GData 0x30 12) (P0Z := dataVal p384GData 0x60 12) (P1X := QX) (P1Y := QY) (P1Z := dataVal p384MontOneData 0 12)
      F E1 s1 g1_2 rfl rfl g1_18 g1_23 g1_25 a1_120 a1_150 a1_180 a1_1b0 a1_1e0 a1_210 a1_270 a1_2a0 a1_2d0 a1_300 a1_330 a1_360 a1_390 a1_3c0 a1_17a4 a1_17d4 a1_1804 a1_1834 a1_1864 a1_1894 a1_18c4 a1_18f4 pvG_lt
  obtain ⟨n3, t3, s3, E3, f3, g3_2, g3_3, g3_4, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_25, a3_120, a3_150, a3_180, a3_1b0, a3_1e0, a3_210, a3_270, a3_2a0, a3_2d0, a3_300, a3_330, a3_360, a3_390, a3_3c0, a3_450, a3_480, a3_4b0, a3_4e0, a3_510, a3_540, a3_570, a3_5a0, a3_5d0, a3_600, a3_630, a3_660, a3_690, a3_6c0, a3_6f0, a3_720, a3_750, a3_780, a3_7b0, a3_7e0, a3_810, a3_840, a3_870, a3_8a0, a3_8d0, a3_900, a3_930, a3_960, a3_990, a3_9c0, a3_9f0, a3_a20, a3_a50, a3_a80, a3_ab0, a3_ae0, a3_b10, a3_b40, a3_b70, a3_ba0, a3_bd0, a3_c00, a3_c30, a3_c60, a3_c90, a3_cc0, a3_cf0, a3_d20, a3_17a4, a3_17d4, a3_1804, a3_1834, a3_1864, a3_1894, a3_18c4, a3_18f4⟩ :=
    pv_stE1 (QX := QX) (QY := QY) (QZ := dataVal p384MontOneData 0 12) (RM := RM) (SM := SM) (ZM := ZM) (U1 := n3fm ZM W) (U2 := n3fm RM W) (P0X := dataVal p384GData 0 12) (P0Y := dataVal p384GData 0x30 12) (P0Z := dataVal p384GData 0x60 12) (P1X := QX) (P1Y := QY) (P1Z := dataVal p384MontOneData 0 12)
      F E2 s2 g2_2 rfl rfl g2_18 g2_19 g2_20 g2_21 g2_22 g2_23 g2_25 a2_120 a2_150 a2_180 a2_1b0 a2_1e0 a2_210 a2_270 a2_2a0 a2_2d0 a2_300 a2_330 a2_360 a2_390 a2_3c0 a2_450 a2_480 a2_4b0 a2_4e0 a2_510 a2_540 a2_570 a2_5a0 a2_5d0 a2_600 a2_630 a2_660 a2_690 a2_6c0 a2_6f0 a2_720 a2_750 a2_780 a2_7b0 a2_7e0 a2_810 a2_840 a2_870 a2_8a0 a2_17a4 a2_17d4 a2_1804 a2_1834 a2_1864 a2_1894 a2_18c4 a2_18f4 hQ
  have fR3 : ∀ x, PvR B x → n3.mem x = n0.mem x := fun x hx => by rw [f3 x hx, f2 x hx, f1 x hx]
  obtain ⟨n4, t4, s4, E4, f4, g4_2, g4_3, g4_4, g4_9, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_25, x4_1, a4_120, a4_150, a4_180, a4_1b0, a4_1e0, a4_210, a4_270, a4_2a0, a4_2d0, a4_300, a4_330, a4_360, a4_390, a4_3c0, a4_450, a4_480, a4_4b0, a4_4e0, a4_510, a4_540, a4_570, a4_5a0, a4_5d0, a4_600, a4_630, a4_660, a4_690, a4_6c0, a4_6f0, a4_720, a4_750, a4_780, a4_7b0, a4_7e0, a4_810, a4_840, a4_870, a4_8a0, a4_8d0, a4_900, a4_930, a4_960, a4_990, a4_9c0, a4_9f0, a4_a20, a4_a50, a4_a80, a4_ab0, a4_ae0, a4_b10, a4_b40, a4_b70, a4_ba0, a4_bd0, a4_c00, a4_c30, a4_c60, a4_c90, a4_cc0, a4_cf0, a4_d20, a4_17a4, a4_17d4, a4_1804, a4_1834, a4_1864, a4_1894, a4_18c4, a4_18f4, w4_e10, w4_1294, w4_1924, ln4_d50, mb4_e14, mb4_1298, mb4_1928⟩ :=
    pv_stF0 (QX := QX) (QY := QY) (QZ := dataVal p384MontOneData 0 12) (RM := RM) (SM := SM) (ZM := ZM) (U1 := n3fm ZM W) (U2 := n3fm RM W) (P0X := dataVal p384GData 0 12) (P0Y := dataVal p384GData 0x30 12) (P0Z := dataVal p384GData 0x60 12) (P1X := QX) (P1Y := QY) (P1Z := dataVal p384MontOneData 0 12)
      F (E0.E.E.fr F fR3) s3 g3_2 rfl rfl g3_25 a3_120 a3_150 a3_180 a3_1b0 a3_1e0 a3_210 a3_270 a3_2a0 a3_2d0 a3_300 a3_330 a3_360 a3_390 a3_3c0 a3_450 a3_480 a3_4b0 a3_4e0 a3_510 a3_540 a3_570 a3_5a0 a3_5d0 a3_600 a3_630 a3_660 a3_690 a3_6c0 a3_6f0 a3_720 a3_750 a3_780 a3_7b0 a3_7e0 a3_810 a3_840 a3_870 a3_8a0 a3_8d0 a3_900 a3_930 a3_960 a3_990 a3_9c0 a3_9f0 a3_a20 a3_a50 a3_a80 a3_ab0 a3_ae0 a3_b10 a3_b40 a3_b70 a3_ba0 a3_bd0 a3_c00 a3_c30 a3_c60 a3_c90 a3_cc0 a3_cf0 a3_d20 a3_17a4 a3_17d4 a3_1804 a3_1834 a3_1864 a3_1894 a3_18c4 a3_18f4 (Nat.mod_lt _ n384_pos)
  obtain ⟨n5, t5, s5, E5, f5, g5_2, g5_3, g5_4, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, x5_1, a5_120, a5_150, a5_180, a5_1b0, a5_1e0, a5_210, a5_450, a5_480, a5_4b0, a5_4e0, a5_510, a5_540, a5_570, a5_5a0, a5_5d0, a5_600, a5_630, a5_660, a5_690, a5_6c0, a5_6f0, a5_720, a5_750, a5_780, a5_7b0, a5_7e0, a5_810, a5_840, a5_870, a5_8a0, a5_8d0, a5_900, a5_930, a5_960, a5_990, a5_9c0, a5_9f0, a5_a20, a5_a50, a5_a80, a5_ab0, a5_ae0, a5_b10, a5_b40, a5_b70, a5_ba0, a5_bd0, a5_c00, a5_c30, a5_c60, a5_c90, a5_cc0, a5_cf0, a5_d20, w5_e10, w5_1294, w5_1924, w5_1aac, ln5_d50, mb5_e14, mb5_1298, mb5_1928, mb5_1ab0⟩ :=
    pv_stF1 (QX := QX) (QY := QY) (QZ := dataVal p384MontOneData 0 12) (RM := RM) (SM := SM) (ZM := ZM) (U1 := n3fm ZM W) (U2 := n3fm RM W) (P0X := dataVal p384GData 0 12) (P0Y := dataVal p384GData 0x30 12) (P0Z := dataVal p384GData 0x60 12) (P1X := QX) (P1Y := QY) (P1Z := dataVal p384MontOneData 0 12)
      F E4 s4 g4_2 rfl rfl g4_9 g4_18 g4_19 g4_20 g4_21 g4_22 g4_23 g4_24 g4_25 a4_120 a4_150 a4_180 a4_1b0 a4_1e0 a4_210 a4_270 a4_2a0 a4_2d0 a4_300 a4_330 a4_360 a4_390 a4_3c0 a4_450 a4_480 a4_4b0 a4_4e0 a4_510 a4_540 a4_570 a4_5a0 a4_5d0 a4_600 a4_630 a4_660 a4_690 a4_6c0 a4_6f0 a4_720 a4_750 a4_780 a4_7b0 a4_7e0 a4_810 a4_840 a4_870 a4_8a0 a4_8d0 a4_900 a4_930 a4_960 a4_990 a4_9c0 a4_9f0 a4_a20 a4_a50 a4_a80 a4_ab0 a4_ae0 a4_b10 a4_b40 a4_b70 a4_ba0 a4_bd0 a4_c00 a4_c30 a4_c60 a4_c90 a4_cc0 a4_cf0 a4_d20 a4_17a4 a4_17d4 a4_1804 a4_1834 a4_1864 a4_1894 a4_18c4 a4_18f4 w4_1924 mb4_1928 (Nat.mod_lt _ n384_pos)
  have fR5 : ∀ x, PvR B x → n5.mem x = n0.mem x := fun x hx => by rw [f5 x hx, f4 x hx, fR3 x hx]
  have hG : ((dataVal p384GData 0 12, dataVal p384GData 0x30 12, dataVal p384GData 0x60 12) : Pt) = pvG := rfl
  rw [hG] at a5_450 a5_480 a5_4b0 a5_4e0 a5_510 a5_540 a5_570 a5_5a0 a5_5d0 a5_600 a5_630 a5_660 a5_690 a5_6c0 a5_6f0 a5_720 a5_750 a5_780 a5_7b0 a5_7e0 a5_810 a5_840 a5_870 a5_8a0
  have M5 : GM B n5.mem (tblPt pvG) (tblPt (QX, QY, dataVal p384MontOneData 0 12)) (pvD (n3fm ZM W))
      (pvD (n3fm RM W)) RM :=
    ⟨fun j hj => match j, hj with
      | 0, _ => ptV_of a5_450 a5_480 a5_4b0
      | 1, _ => ptV_of a5_4e0 a5_510 a5_540
      | 2, _ => ptV_of a5_570 a5_5a0 a5_5d0
      | 3, _ => ptV_of a5_600 a5_630 a5_660
      | 4, _ => ptV_of a5_690 a5_6c0 a5_6f0
      | 5, _ => ptV_of a5_720 a5_750 a5_780
      | 6, _ => ptV_of a5_7b0 a5_7e0 a5_810
      | 7, _ => ptV_of a5_840 a5_870 a5_8a0
      | _ + 8, h => absurd h (by omega),
     fun j hj => match j, hj with
      | 0, _ => ptV_of a5_8d0 a5_900 a5_930
      | 1, _ => ptV_of a5_960 a5_990 a5_9c0
      | 2, _ => ptV_of a5_9f0 a5_a20 a5_a50
      | 3, _ => ptV_of a5_a80 a5_ab0 a5_ae0
      | 4, _ => ptV_of a5_b10 a5_b40 a5_b70
      | 5, _ => ptV_of a5_ba0 a5_bd0 a5_c00
      | 6, _ => ptV_of a5_c30 a5_c60 a5_c90
      | 7, _ => ptV_of a5_cc0 a5_cf0 a5_d20
      | _ + 8, h => absurd h (by omega),
     fun j _ => ⟨tblPt_lt pvG_lt j, tblPt_lt hQ j⟩, mb5_1928, mb5_1ab0, a5_1b0⟩
  rcases pv_stGH F (E0.fr F fR5) s5 g5_2 w5_1924 w5_1aac x4_1 x5_1 M5 hINV with ⟨hn, hp⟩ | ⟨P, hP, n6, t6, s6, E6, f6, sp6, r36, r46, a6⟩
  · exact .inl ⟨hn, Panics.of_steps (t1.trans (t2.trans (t3.trans (t4.trans t5)))) hp⟩
  · exact .inr ⟨P, hP, n6, t1.trans (t2.trans (t3.trans (t4.trans (t5.trans t6)))), s6, E6,
      fun x hx => by rw [f6 x hx, fR5 x hx], sp6, by rw [r36, g5_3, g4_3, g3_3, g2_3, g1_3],
      by rw [r46, g5_4, g4_4, g3_4, g2_4, g1_4], a6⟩

end C3.RV32.Pv
