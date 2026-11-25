import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvCr1
import C3BootProofs.Proofs.SvRl
import C3BootProofs.Proofs.SvRm
import C3BootProofs.Proofs.SvWin0
import C3BootProofs.Proofs.SvWin1
import C3BootProofs.Proofs.SvWin2
import C3BootProofs.Proofs.SvWin3
import C3BootProofs.Proofs.SvWin4
import C3BootProofs.Proofs.SvWin5
import C3BootProofs.Proofs.SvWin6
import C3BootProofs.Proofs.SvWin7

/-!
# `sigstore::verify`: The entry's index and the validity windows

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The entry's index and the validity windows**: from 0x17F8 to the successful exit at 0x1A9E, `sv_cr1`, `sv_rl`, `sv_rm`, and the eight window checks. -/
theorem sv_seg_win {B out bp x20 x21 x22 x23 x24 x25 x26 x27 kp w1c w40 q w64 w74 lih lil : Word} {rt : Bytes} {v : Nat → Word} {n0 : Machine} {w68 : Word} {w6c : Word} {w70 : Word} {w3c : Word} {w54 : Word} {w58 : Word} {w5c : Word} {w60 : Word} {w78 : Word} {w7c : Word}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x17F8 (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = x27)
    (w0_1c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c)
    (w0_20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74)
    (q0_3e0 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0))
    (RS : SvRoSep B)
    (lid_in : SvIn B (q + BitVec.ofNat 32 0x5) 19)
    (h40 : w40 ≠ 0)
    (hlih : memLoad32 M0 (bp + 0x2C) = lih)
    (hlil : memLoad32 M0 (bp + 0x28) = lil)
    (lih_in : SvIn B (bp + 0x2C) 4)
    (lil_in : SvIn B (bp + 0x28) 4)
    (a_lih : (bp + 0x2C).toNat % 4 = 0)
    (a_lil : (bp + 0x28).toNat % 4 = 0)
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68)
    (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70)
    (S2 : SvSha2Code M0)
    (RK0 : SvRkCode M0)
    (dgi_in : SvIn B x20 32)
    (sig_in : SvIn B w70 w68.toNat)
    (crt_in : SvIn B w6c x22.toNat)
    (pp_in4 : SvIn B (bp + 0x10) 4)
    (pl_in4 : SvIn B (bp + 0x14) 4)
    (a_pp : (bp + 0x10).toNat % 4 = 0)
    (a_pl : (bp + 0x14).toNat % 4 = 0)
    (pp_in : SvIn B (memLoad32 M0 (bp + 0x10)) (memLoad32 M0 (bp + 0x14)).toNat)
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c)
    (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54)
    (w0_58 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58)
    (w0_5c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c)
    (w0_60 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c)
    (ii2h : SvIn B (x23 + 0xFFFFFFE8) 4)
    (ai2h : (x23 + 0xFFFFFFE8).toNat % 4 = 0)
    (ii2l : SvIn B (x23 + 0xFFFFFFE4) 4)
    (ai2l : (x23 + 0xFFFFFFE4).toNat % 4 = 0)
    (ii3h : SvIn B (x23 + 0xFFFFFFF0) 4)
    (ai3h : (x23 + 0xFFFFFFF0).toNat % 4 = 0)
    (ii3l : SvIn B (x23 + 0xFFFFFFEC) 4)
    (ai3l : (x23 + 0xFFFFFFEC).toNat % 4 = 0)
    (it4h : SvIn B (w78 + 0xC) 4)
    (at4h : (w78 + 0xC).toNat % 4 = 0)
    (it4l : SvIn B (w78 + 0x8) 4)
    (at4l : (w78 + 0x8).toNat % 4 = 0)
    (it5h : SvIn B (w78 + 0x14) 4)
    (at5h : (w78 + 0x14).toNat % 4 = 0)
    (it5l : SvIn B (w78 + 0x10) 4)
    (at5l : (w78 + 0x10).toNat % 4 = 0) :
    SvErrRet B out v n0 ∨
    ((((lih = w74) ∧ (aluEval .sltu (lil) (w64) ≠ 0)) ∨ ((¬ (lih = w74)) ∧ (aluEval .sltu (lih) (w74) ≠ 0))) ∧
      ∃ root6_3, rootFromInclusion (pair64 (lil) (lih)) (pair64 (w64) (w74)) ((sha256 ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes M0 (w70) ((w68).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid2Address)) (0x54) ++ base64Encode (memBytes M0 (w6c) ((x22).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPostAddress)) (0x7)))) (memBytes M0 ((memLoad32 M0 (bp + 0x10))) (((memLoad32 M0 (bp + 0x14))).toNat)) = some root6_3 ∧
      (b32 root6_3 = b32 rt) ∧
      (((w5c = w7c) ∧ (aluEval .sltu (w3c) (w60) = 0)) ∨ ((¬ (w5c = w7c)) ∧ (aluEval .sltu (w7c) (w5c) = 0))) ∧
      (((w7c = w54) ∧ (aluEval .sltu (w58) (w3c) = 0)) ∨ ((¬ (w7c = w54)) ∧ (aluEval .sltu (w54) (w7c) = 0))) ∧
      ((((memLoad32 M0 (x23 + 0xFFFFFFE8)) = w7c) ∧ (aluEval .sltu (w3c) ((memLoad32 M0 (x23 + 0xFFFFFFE4))) = 0)) ∨ ((¬ ((memLoad32 M0 (x23 + 0xFFFFFFE8)) = w7c)) ∧ (aluEval .sltu (w7c) ((memLoad32 M0 (x23 + 0xFFFFFFE8))) = 0))) ∧
      (((w7c = (memLoad32 M0 (x23 + 0xFFFFFFF0))) ∧ (aluEval .sltu ((memLoad32 M0 (x23 + 0xFFFFFFEC))) (w3c) = 0)) ∨ ((¬ (w7c = (memLoad32 M0 (x23 + 0xFFFFFFF0)))) ∧ (aluEval .sltu ((memLoad32 M0 (x23 + 0xFFFFFFF0))) (w7c) = 0))) ∧
      ((((memLoad32 M0 (w78 + 0xC)) = w7c) ∧ (aluEval .sltu (w3c) ((memLoad32 M0 (w78 + 0x8))) = 0)) ∨ ((¬ ((memLoad32 M0 (w78 + 0xC)) = w7c)) ∧ (aluEval .sltu (w7c) ((memLoad32 M0 (w78 + 0xC))) = 0))) ∧
      (((w7c = (memLoad32 M0 (w78 + 0x14))) ∧ (aluEval .sltu ((memLoad32 M0 (w78 + 0x10))) (w3c) = 0)) ∨ ((¬ (w7c = (memLoad32 M0 (w78 + 0x14)))) ∧ (aluEval .sltu ((memLoad32 M0 (w78 + 0x14))) (w7c) = 0))) ∧
      ((((memLoad32 M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) = w7c) ∧ (aluEval .sltu (w3c) ((memLoad32 M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 3))) = 0)) ∨ ((¬ ((memLoad32 M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) = w7c)) ∧ (aluEval .sltu (w7c) ((memLoad32 M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7))) = 0))) ∧
      (((w7c = (memLoad32 M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15))) ∧ (aluEval .sltu ((memLoad32 M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 11))) (w3c) = 0)) ∨ ((¬ (w7c = (memLoad32 M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15)))) ∧ (aluEval .sltu ((memLoad32 M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15))) (w7c) = 0))) ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x1A9E (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = (BitVec.ofNat 32 0x1E) ∧
        reg n' (21 : Fin 32) = lil ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = lih ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (memLoad32 M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 3)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (memLoad32 M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x390) = (memLoad32 M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 11)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x394) = (memLoad32 M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A0) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A4) = w74 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = (x25).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1FC) = BitVec.ofNat 8 (root6_3.getD 0 0) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6_3.getD 0 0) ∧
        SvKeepL B n0.mem n'.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1), (0x3A0, 0x4), (0x3A4, 0x4), (0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x400, 0x20), (0x420, 0x21), (0x1FD, 0x1F), (0x1FC, 0x1)]) := by
  rcases sv_cr1 FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_1c w0_20 w0_34 w0_40 w0_4c w0_64 w0_74 q0_3e0 RS lid_in h40 hlih hlil lih_in lil_in a_lih a_lil with e | hx1
  · exact .inl e
  obtain ⟨x1_0, hx1⟩ := hx1
  obtain ⟨n1, hx1⟩ := hx1
  obtain ⟨c1, hx1⟩ := hx1
  obtain ⟨s1, hx1⟩ := hx1
  obtain ⟨E1, hx1⟩ := hx1
  obtain ⟨V1, hx1⟩ := hx1
  obtain ⟨fR1, hx1⟩ := hx1
  obtain ⟨r1_2, hx1⟩ := hx1
  obtain ⟨r1_3, hx1⟩ := hx1
  obtain ⟨r1_4, hx1⟩ := hx1
  obtain ⟨r1_18, hx1⟩ := hx1
  obtain ⟨r1_19, hx1⟩ := hx1
  obtain ⟨r1_20, hx1⟩ := hx1
  obtain ⟨r1_21, hx1⟩ := hx1
  obtain ⟨r1_22, hx1⟩ := hx1
  obtain ⟨r1_23, hx1⟩ := hx1
  obtain ⟨r1_24, hx1⟩ := hx1
  obtain ⟨r1_25, hx1⟩ := hx1
  obtain ⟨r1_26, hx1⟩ := hx1
  obtain ⟨r1_27, hx1⟩ := hx1
  obtain ⟨w1_1c, hx1⟩ := hx1
  obtain ⟨w1_20, hx1⟩ := hx1
  obtain ⟨w1_34, hx1⟩ := hx1
  obtain ⟨w1_40, hx1⟩ := hx1
  obtain ⟨w1_4c, hx1⟩ := hx1
  obtain ⟨w1_64, hx1⟩ := hx1
  obtain ⟨w1_74, hx1⟩ := hx1
  obtain ⟨w1_380, hx1⟩ := hx1
  obtain ⟨w1_398, hx1⟩ := hx1
  obtain ⟨w1_39c, hx1⟩ := hx1
  obtain ⟨w1_3a0, hx1⟩ := hx1
  obtain ⟨w1_3a4, hx1⟩ := hx1
  obtain ⟨b1_384, hx1⟩ := hx1
  obtain ⟨b1_3a8, hx1⟩ := hx1
  obtain ⟨q1_25c, hx1⟩ := hx1
  obtain ⟨q1_27c, hx1⟩ := hx1
  obtain ⟨q1_385, hx1⟩ := hx1
  obtain ⟨q1_3a9, hx1⟩ := hx1
  obtain ⟨q1_3e0, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_rl FW E1 V1 hret hO s1 M0 fR1 r1_2 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_25 r1_26 r1_27 w1_64 ((K1_L.w32 (by decide) (by decide)).trans w0_68) ((K1_L.w32 (by decide) (by decide)).trans w0_6c) ((K1_L.w32 (by decide) (by decide)).trans w0_70) w1_74 S2 RS RK0 dgi_in sig_in crt_in with ⟨-, e⟩ | hx2
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  obtain ⟨n2, hx2⟩ := hx2
  obtain ⟨c2, hx2⟩ := hx2
  obtain ⟨s2, hx2⟩ := hx2
  obtain ⟨E2, hx2⟩ := hx2
  obtain ⟨V2, hx2⟩ := hx2
  obtain ⟨fR2, hx2⟩ := hx2
  obtain ⟨r2_2, hx2⟩ := hx2
  obtain ⟨r2_3, hx2⟩ := hx2
  obtain ⟨r2_4, hx2⟩ := hx2
  obtain ⟨r2_18, hx2⟩ := hx2
  obtain ⟨r2_19, hx2⟩ := hx2
  obtain ⟨r2_20, hx2⟩ := hx2
  obtain ⟨r2_21, hx2⟩ := hx2
  obtain ⟨r2_22, hx2⟩ := hx2
  obtain ⟨r2_23, hx2⟩ := hx2
  obtain ⟨r2_24, hx2⟩ := hx2
  obtain ⟨r2_25, hx2⟩ := hx2
  obtain ⟨r2_26, hx2⟩ := hx2
  obtain ⟨r2_27, hx2⟩ := hx2
  obtain ⟨w2_64, hx2⟩ := hx2
  obtain ⟨w2_68, hx2⟩ := hx2
  obtain ⟨w2_6c, hx2⟩ := hx2
  obtain ⟨w2_70, hx2⟩ := hx2
  obtain ⟨w2_74, hx2⟩ := hx2
  obtain ⟨mb2_400, hx2⟩ := hx2
  have K2_L := hx2
  rcases sv_rm FW E2 V2 hret hO s2 M0 fR2 r2_2 r2_18 r2_19 r2_20 r2_21 r2_22 r2_23 r2_24 r2_25 r2_26 r2_27 w2_64 w2_74 S2 RS RK0 ((K2_L.b8 (by decide) (by decide)).trans b1_3a8) (fun j hj => (K2_L.range (by decide) (by decide) j hj).trans (q1_3a9 j hj)) mb2_400 rfl rfl pp_in4 pl_in4 a_pp a_pl pp_in with ⟨-, e⟩ | hx3
  · exact .inl (SvErrRet.pre (c1.trans (c2)) (by rw [r2_3, r1_3]) (by rw [r2_4, r1_4])
      (fun x hx => (fR2 x hx).trans (fM x hx).symm) e)
  obtain ⟨root6_3, hx3⟩ := hx3
  obtain ⟨x3_0, hx3⟩ := hx3
  obtain ⟨x3_1, hx3⟩ := hx3
  obtain ⟨n3, hx3⟩ := hx3
  obtain ⟨c3, hx3⟩ := hx3
  obtain ⟨s3, hx3⟩ := hx3
  obtain ⟨E3, hx3⟩ := hx3
  obtain ⟨V3, hx3⟩ := hx3
  obtain ⟨fR3, hx3⟩ := hx3
  obtain ⟨r3_2, hx3⟩ := hx3
  obtain ⟨r3_3, hx3⟩ := hx3
  obtain ⟨r3_4, hx3⟩ := hx3
  obtain ⟨r3_8, hx3⟩ := hx3
  obtain ⟨r3_9, hx3⟩ := hx3
  obtain ⟨r3_18, hx3⟩ := hx3
  obtain ⟨r3_19, hx3⟩ := hx3
  obtain ⟨r3_20, hx3⟩ := hx3
  obtain ⟨r3_21, hx3⟩ := hx3
  obtain ⟨r3_22, hx3⟩ := hx3
  obtain ⟨r3_23, hx3⟩ := hx3
  obtain ⟨r3_24, hx3⟩ := hx3
  obtain ⟨r3_25, hx3⟩ := hx3
  obtain ⟨r3_26, hx3⟩ := hx3
  obtain ⟨r3_27, hx3⟩ := hx3
  obtain ⟨w3_64, hx3⟩ := hx3
  obtain ⟨w3_74, hx3⟩ := hx3
  obtain ⟨b3_1fc, hx3⟩ := hx3
  obtain ⟨b3_3a8, hx3⟩ := hx3
  obtain ⟨b3_420, hx3⟩ := hx3
  obtain ⟨b3_421, hx3⟩ := hx3
  obtain ⟨q3_1fd, hx3⟩ := hx3
  obtain ⟨q3_3a9, hx3⟩ := hx3
  obtain ⟨q3_421, hx3⟩ := hx3
  have K3_L := hx3
  rcases sv_win0 (i2h := 0) (i2l := 0) (i3h := 0) (i3l := 0) (t4h := 0) (t4l := 0) (t5h := 0) (t5l := 0) FW E3 V3 hret hO s3 M0 fR3 r3_2 r3_18 r3_19 r3_20 r3_21 r3_22 r3_23 r3_24 r3_25 r3_26 r3_27 ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_3c))) ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_54))) ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_58))) ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_5c))) ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_60))) ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_78))) ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_7c))) ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans (memLoad32_of_range (c := 0x385) (d := 3) q1_385 (by decide)))) ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans (memLoad32_of_range (c := 0x385) (d := 7) q1_385 (by decide)))) ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans (memLoad32_of_range (c := 0x385) (d := 11) q1_385 (by decide)))) ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans (memLoad32_of_range (c := 0x385) (d := 15) q1_385 (by decide)))) with e | hx4
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3))) (by rw [r3_3, r2_3, r1_3]) (by rw [r3_4, r2_4, r1_4])
      (fun x hx => (fR3 x hx).trans (fM x hx).symm) e)
  obtain ⟨x4_0, hx4⟩ := hx4
  obtain ⟨n4, hx4⟩ := hx4
  obtain ⟨c4, hx4⟩ := hx4
  obtain ⟨s4, hx4⟩ := hx4
  obtain ⟨E4, hx4⟩ := hx4
  obtain ⟨V4, hx4⟩ := hx4
  obtain ⟨fR4, hx4⟩ := hx4
  obtain ⟨r4_2, hx4⟩ := hx4
  obtain ⟨r4_3, hx4⟩ := hx4
  obtain ⟨r4_4, hx4⟩ := hx4
  obtain ⟨r4_18, hx4⟩ := hx4
  obtain ⟨r4_19, hx4⟩ := hx4
  obtain ⟨r4_20, hx4⟩ := hx4
  obtain ⟨r4_21, hx4⟩ := hx4
  obtain ⟨r4_22, hx4⟩ := hx4
  obtain ⟨r4_23, hx4⟩ := hx4
  obtain ⟨r4_24, hx4⟩ := hx4
  obtain ⟨r4_25, hx4⟩ := hx4
  obtain ⟨r4_26, hx4⟩ := hx4
  obtain ⟨r4_27, hx4⟩ := hx4
  obtain ⟨w4_3c, hx4⟩ := hx4
  obtain ⟨w4_54, hx4⟩ := hx4
  obtain ⟨w4_58, hx4⟩ := hx4
  obtain ⟨w4_5c, hx4⟩ := hx4
  obtain ⟨w4_60, hx4⟩ := hx4
  obtain ⟨w4_78, hx4⟩ := hx4
  obtain ⟨w4_7c, hx4⟩ := hx4
  obtain ⟨w4_388, hx4⟩ := hx4
  obtain ⟨w4_38c, hx4⟩ := hx4
  obtain ⟨w4_390, hx4⟩ := hx4
  obtain ⟨w4_394, hx4⟩ := hx4
  have K4_L := hx4
  rcases sv_win1 (i2h := 0) (i2l := 0) (i3h := 0) (i3l := 0) (t4h := 0) (t4l := 0) (t5h := 0) (t5l := 0) FW E4 V4 hret hO s4 M0 fR4 r4_2 r4_18 r4_19 r4_20 r4_21 r4_22 r4_23 r4_24 r4_25 r4_26 r4_27 w4_3c w4_54 w4_58 w4_5c w4_60 w4_78 w4_7c w4_388 w4_38c w4_390 w4_394 with e | hx5
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4)))) (by rw [r4_3, r3_3, r2_3, r1_3]) (by rw [r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR4 x hx).trans (fM x hx).symm) e)
  obtain ⟨x5_0, hx5⟩ := hx5
  obtain ⟨n5, hx5⟩ := hx5
  obtain ⟨c5, hx5⟩ := hx5
  obtain ⟨s5, hx5⟩ := hx5
  obtain ⟨E5, hx5⟩ := hx5
  obtain ⟨V5, hx5⟩ := hx5
  obtain ⟨fR5, hx5⟩ := hx5
  obtain ⟨r5_2, hx5⟩ := hx5
  obtain ⟨r5_3, hx5⟩ := hx5
  obtain ⟨r5_4, hx5⟩ := hx5
  obtain ⟨r5_18, hx5⟩ := hx5
  obtain ⟨r5_19, hx5⟩ := hx5
  obtain ⟨r5_20, hx5⟩ := hx5
  obtain ⟨r5_21, hx5⟩ := hx5
  obtain ⟨r5_22, hx5⟩ := hx5
  obtain ⟨r5_23, hx5⟩ := hx5
  obtain ⟨r5_24, hx5⟩ := hx5
  obtain ⟨r5_25, hx5⟩ := hx5
  obtain ⟨r5_26, hx5⟩ := hx5
  obtain ⟨r5_27, hx5⟩ := hx5
  obtain ⟨w5_3c, hx5⟩ := hx5
  obtain ⟨w5_54, hx5⟩ := hx5
  obtain ⟨w5_58, hx5⟩ := hx5
  obtain ⟨w5_5c, hx5⟩ := hx5
  obtain ⟨w5_60, hx5⟩ := hx5
  obtain ⟨w5_78, hx5⟩ := hx5
  obtain ⟨w5_7c, hx5⟩ := hx5
  obtain ⟨w5_388, hx5⟩ := hx5
  obtain ⟨w5_38c, hx5⟩ := hx5
  obtain ⟨w5_390, hx5⟩ := hx5
  obtain ⟨w5_394, hx5⟩ := hx5
  have K5_L := hx5
  rcases sv_win2 (i3h := 0) (i3l := 0) (t4h := 0) (t4l := 0) (t5h := 0) (t5l := 0) FW E5 V5 hret hO s5 M0 fR5 r5_2 r5_18 r5_19 r5_20 r5_21 r5_22 r5_23 r5_24 r5_25 r5_26 r5_27 w5_3c w5_54 w5_58 w5_5c w5_60 w5_78 w5_7c w5_388 w5_38c w5_390 w5_394 rfl ii2h ai2h rfl ii2l ai2l with e | hx6
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5))))) (by rw [r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR5 x hx).trans (fM x hx).symm) e)
  obtain ⟨x6_0, hx6⟩ := hx6
  obtain ⟨n6, hx6⟩ := hx6
  obtain ⟨c6, hx6⟩ := hx6
  obtain ⟨s6, hx6⟩ := hx6
  obtain ⟨E6, hx6⟩ := hx6
  obtain ⟨V6, hx6⟩ := hx6
  obtain ⟨fR6, hx6⟩ := hx6
  obtain ⟨r6_2, hx6⟩ := hx6
  obtain ⟨r6_3, hx6⟩ := hx6
  obtain ⟨r6_4, hx6⟩ := hx6
  obtain ⟨r6_18, hx6⟩ := hx6
  obtain ⟨r6_19, hx6⟩ := hx6
  obtain ⟨r6_20, hx6⟩ := hx6
  obtain ⟨r6_21, hx6⟩ := hx6
  obtain ⟨r6_22, hx6⟩ := hx6
  obtain ⟨r6_23, hx6⟩ := hx6
  obtain ⟨r6_24, hx6⟩ := hx6
  obtain ⟨r6_25, hx6⟩ := hx6
  obtain ⟨r6_26, hx6⟩ := hx6
  obtain ⟨r6_27, hx6⟩ := hx6
  obtain ⟨w6_3c, hx6⟩ := hx6
  obtain ⟨w6_54, hx6⟩ := hx6
  obtain ⟨w6_58, hx6⟩ := hx6
  obtain ⟨w6_5c, hx6⟩ := hx6
  obtain ⟨w6_60, hx6⟩ := hx6
  obtain ⟨w6_78, hx6⟩ := hx6
  obtain ⟨w6_7c, hx6⟩ := hx6
  obtain ⟨w6_388, hx6⟩ := hx6
  obtain ⟨w6_38c, hx6⟩ := hx6
  obtain ⟨w6_390, hx6⟩ := hx6
  obtain ⟨w6_394, hx6⟩ := hx6
  have K6_L := hx6
  rcases sv_win3 (i2h := 0) (i2l := 0) (t4h := 0) (t4l := 0) (t5h := 0) (t5l := 0) FW E6 V6 hret hO s6 M0 fR6 r6_2 r6_18 r6_19 r6_20 r6_21 r6_22 r6_23 r6_24 r6_25 r6_26 r6_27 w6_3c w6_54 w6_58 w6_5c w6_60 w6_78 w6_7c w6_388 w6_38c w6_390 w6_394 rfl ii3h ai3h rfl ii3l ai3l with e | hx7
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6)))))) (by rw [r6_3, r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r6_4, r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR6 x hx).trans (fM x hx).symm) e)
  obtain ⟨x7_0, hx7⟩ := hx7
  obtain ⟨n7, hx7⟩ := hx7
  obtain ⟨c7, hx7⟩ := hx7
  obtain ⟨s7, hx7⟩ := hx7
  obtain ⟨E7, hx7⟩ := hx7
  obtain ⟨V7, hx7⟩ := hx7
  obtain ⟨fR7, hx7⟩ := hx7
  obtain ⟨r7_2, hx7⟩ := hx7
  obtain ⟨r7_3, hx7⟩ := hx7
  obtain ⟨r7_4, hx7⟩ := hx7
  obtain ⟨r7_18, hx7⟩ := hx7
  obtain ⟨r7_19, hx7⟩ := hx7
  obtain ⟨r7_20, hx7⟩ := hx7
  obtain ⟨r7_21, hx7⟩ := hx7
  obtain ⟨r7_22, hx7⟩ := hx7
  obtain ⟨r7_23, hx7⟩ := hx7
  obtain ⟨r7_24, hx7⟩ := hx7
  obtain ⟨r7_25, hx7⟩ := hx7
  obtain ⟨r7_26, hx7⟩ := hx7
  obtain ⟨r7_27, hx7⟩ := hx7
  obtain ⟨w7_3c, hx7⟩ := hx7
  obtain ⟨w7_54, hx7⟩ := hx7
  obtain ⟨w7_58, hx7⟩ := hx7
  obtain ⟨w7_5c, hx7⟩ := hx7
  obtain ⟨w7_60, hx7⟩ := hx7
  obtain ⟨w7_78, hx7⟩ := hx7
  obtain ⟨w7_7c, hx7⟩ := hx7
  obtain ⟨w7_388, hx7⟩ := hx7
  obtain ⟨w7_38c, hx7⟩ := hx7
  obtain ⟨w7_390, hx7⟩ := hx7
  obtain ⟨w7_394, hx7⟩ := hx7
  have K7_L := hx7
  rcases sv_win4 (i2h := 0) (i2l := 0) (i3h := 0) (i3l := 0) (t5h := 0) (t5l := 0) FW E7 V7 hret hO s7 M0 fR7 r7_2 r7_18 r7_19 r7_20 r7_21 r7_22 r7_23 r7_24 r7_25 r7_26 r7_27 w7_3c w7_54 w7_58 w7_5c w7_60 w7_78 w7_7c w7_388 w7_38c w7_390 w7_394 rfl it4h at4h rfl it4l at4l with e | hx8
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7))))))) (by rw [r7_3, r6_3, r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r7_4, r6_4, r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR7 x hx).trans (fM x hx).symm) e)
  obtain ⟨x8_0, hx8⟩ := hx8
  obtain ⟨n8, hx8⟩ := hx8
  obtain ⟨c8, hx8⟩ := hx8
  obtain ⟨s8, hx8⟩ := hx8
  obtain ⟨E8, hx8⟩ := hx8
  obtain ⟨V8, hx8⟩ := hx8
  obtain ⟨fR8, hx8⟩ := hx8
  obtain ⟨r8_2, hx8⟩ := hx8
  obtain ⟨r8_3, hx8⟩ := hx8
  obtain ⟨r8_4, hx8⟩ := hx8
  obtain ⟨r8_18, hx8⟩ := hx8
  obtain ⟨r8_19, hx8⟩ := hx8
  obtain ⟨r8_20, hx8⟩ := hx8
  obtain ⟨r8_21, hx8⟩ := hx8
  obtain ⟨r8_22, hx8⟩ := hx8
  obtain ⟨r8_23, hx8⟩ := hx8
  obtain ⟨r8_24, hx8⟩ := hx8
  obtain ⟨r8_25, hx8⟩ := hx8
  obtain ⟨r8_26, hx8⟩ := hx8
  obtain ⟨r8_27, hx8⟩ := hx8
  obtain ⟨w8_3c, hx8⟩ := hx8
  obtain ⟨w8_54, hx8⟩ := hx8
  obtain ⟨w8_58, hx8⟩ := hx8
  obtain ⟨w8_5c, hx8⟩ := hx8
  obtain ⟨w8_60, hx8⟩ := hx8
  obtain ⟨w8_78, hx8⟩ := hx8
  obtain ⟨w8_7c, hx8⟩ := hx8
  obtain ⟨w8_388, hx8⟩ := hx8
  obtain ⟨w8_38c, hx8⟩ := hx8
  obtain ⟨w8_390, hx8⟩ := hx8
  obtain ⟨w8_394, hx8⟩ := hx8
  have K8_L := hx8
  rcases sv_win5 (i2h := 0) (i2l := 0) (i3h := 0) (i3l := 0) (t4h := 0) (t4l := 0) FW E8 V8 hret hO s8 M0 fR8 r8_2 r8_18 r8_19 r8_20 r8_21 r8_22 r8_23 r8_24 r8_25 r8_26 r8_27 w8_3c w8_54 w8_58 w8_5c w8_60 w8_78 w8_7c w8_388 w8_38c w8_390 w8_394 rfl it5h at5h rfl it5l at5l with e | hx9
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8)))))))) (by rw [r8_3, r7_3, r6_3, r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r8_4, r7_4, r6_4, r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR8 x hx).trans (fM x hx).symm) e)
  obtain ⟨x9_0, hx9⟩ := hx9
  obtain ⟨n9, hx9⟩ := hx9
  obtain ⟨c9, hx9⟩ := hx9
  obtain ⟨s9, hx9⟩ := hx9
  obtain ⟨E9, hx9⟩ := hx9
  obtain ⟨V9, hx9⟩ := hx9
  obtain ⟨fR9, hx9⟩ := hx9
  obtain ⟨r9_2, hx9⟩ := hx9
  obtain ⟨r9_3, hx9⟩ := hx9
  obtain ⟨r9_4, hx9⟩ := hx9
  obtain ⟨r9_18, hx9⟩ := hx9
  obtain ⟨r9_19, hx9⟩ := hx9
  obtain ⟨r9_20, hx9⟩ := hx9
  obtain ⟨r9_21, hx9⟩ := hx9
  obtain ⟨r9_22, hx9⟩ := hx9
  obtain ⟨r9_23, hx9⟩ := hx9
  obtain ⟨r9_24, hx9⟩ := hx9
  obtain ⟨r9_25, hx9⟩ := hx9
  obtain ⟨r9_26, hx9⟩ := hx9
  obtain ⟨r9_27, hx9⟩ := hx9
  obtain ⟨w9_3c, hx9⟩ := hx9
  obtain ⟨w9_54, hx9⟩ := hx9
  obtain ⟨w9_58, hx9⟩ := hx9
  obtain ⟨w9_5c, hx9⟩ := hx9
  obtain ⟨w9_60, hx9⟩ := hx9
  obtain ⟨w9_78, hx9⟩ := hx9
  obtain ⟨w9_7c, hx9⟩ := hx9
  obtain ⟨w9_388, hx9⟩ := hx9
  obtain ⟨w9_38c, hx9⟩ := hx9
  obtain ⟨w9_390, hx9⟩ := hx9
  obtain ⟨w9_394, hx9⟩ := hx9
  have K9_L := hx9
  rcases sv_win6 (i2h := 0) (i2l := 0) (i3h := 0) (i3l := 0) (t4h := 0) (t4l := 0) (t5h := 0) (t5l := 0) FW E9 V9 hret hO s9 M0 fR9 r9_2 r9_18 r9_19 r9_20 r9_21 r9_22 r9_23 r9_24 r9_25 r9_26 r9_27 w9_3c w9_54 w9_58 w9_5c w9_60 w9_78 w9_7c w9_388 w9_38c w9_390 w9_394 with e | hx10
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9))))))))) (by rw [r9_3, r8_3, r7_3, r6_3, r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r9_4, r8_4, r7_4, r6_4, r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR9 x hx).trans (fM x hx).symm) e)
  obtain ⟨x10_0, hx10⟩ := hx10
  obtain ⟨n10, hx10⟩ := hx10
  obtain ⟨c10, hx10⟩ := hx10
  obtain ⟨s10, hx10⟩ := hx10
  obtain ⟨E10, hx10⟩ := hx10
  obtain ⟨V10, hx10⟩ := hx10
  obtain ⟨fR10, hx10⟩ := hx10
  obtain ⟨r10_2, hx10⟩ := hx10
  obtain ⟨r10_3, hx10⟩ := hx10
  obtain ⟨r10_4, hx10⟩ := hx10
  obtain ⟨r10_18, hx10⟩ := hx10
  obtain ⟨r10_19, hx10⟩ := hx10
  obtain ⟨r10_20, hx10⟩ := hx10
  obtain ⟨r10_21, hx10⟩ := hx10
  obtain ⟨r10_22, hx10⟩ := hx10
  obtain ⟨r10_23, hx10⟩ := hx10
  obtain ⟨r10_24, hx10⟩ := hx10
  obtain ⟨r10_25, hx10⟩ := hx10
  obtain ⟨r10_26, hx10⟩ := hx10
  obtain ⟨r10_27, hx10⟩ := hx10
  obtain ⟨w10_3c, hx10⟩ := hx10
  obtain ⟨w10_54, hx10⟩ := hx10
  obtain ⟨w10_58, hx10⟩ := hx10
  obtain ⟨w10_5c, hx10⟩ := hx10
  obtain ⟨w10_60, hx10⟩ := hx10
  obtain ⟨w10_78, hx10⟩ := hx10
  obtain ⟨w10_7c, hx10⟩ := hx10
  obtain ⟨w10_388, hx10⟩ := hx10
  obtain ⟨w10_38c, hx10⟩ := hx10
  obtain ⟨w10_390, hx10⟩ := hx10
  obtain ⟨w10_394, hx10⟩ := hx10
  have K10_L := hx10
  rcases sv_win7 (i2h := 0) (i2l := 0) (i3h := 0) (i3l := 0) (t4h := 0) (t4l := 0) (t5h := 0) (t5l := 0) FW E10 V10 hret hO s10 M0 fR10 r10_2 r10_18 r10_19 r10_20 r10_21 r10_22 r10_23 r10_24 r10_25 r10_26 r10_27 w10_3c w10_54 w10_58 w10_5c w10_60 w10_78 w10_7c w10_388 w10_38c w10_390 w10_394 with e | hx11
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10)))))))))) (by rw [r10_3, r9_3, r8_3, r7_3, r6_3, r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r10_4, r9_4, r8_4, r7_4, r6_4, r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR10 x hx).trans (fM x hx).symm) e)
  obtain ⟨x11_0, hx11⟩ := hx11
  obtain ⟨n11, hx11⟩ := hx11
  obtain ⟨c11, hx11⟩ := hx11
  obtain ⟨s11, hx11⟩ := hx11
  obtain ⟨E11, hx11⟩ := hx11
  obtain ⟨V11, hx11⟩ := hx11
  obtain ⟨fR11, hx11⟩ := hx11
  obtain ⟨r11_2, hx11⟩ := hx11
  obtain ⟨r11_3, hx11⟩ := hx11
  obtain ⟨r11_4, hx11⟩ := hx11
  obtain ⟨r11_18, hx11⟩ := hx11
  obtain ⟨r11_19, hx11⟩ := hx11
  obtain ⟨r11_20, hx11⟩ := hx11
  obtain ⟨r11_21, hx11⟩ := hx11
  obtain ⟨r11_22, hx11⟩ := hx11
  obtain ⟨r11_23, hx11⟩ := hx11
  obtain ⟨r11_24, hx11⟩ := hx11
  obtain ⟨r11_25, hx11⟩ := hx11
  obtain ⟨r11_26, hx11⟩ := hx11
  obtain ⟨r11_27, hx11⟩ := hx11
  obtain ⟨w11_3c, hx11⟩ := hx11
  obtain ⟨w11_54, hx11⟩ := hx11
  obtain ⟨w11_58, hx11⟩ := hx11
  obtain ⟨w11_5c, hx11⟩ := hx11
  obtain ⟨w11_60, hx11⟩ := hx11
  obtain ⟨w11_78, hx11⟩ := hx11
  obtain ⟨w11_7c, hx11⟩ := hx11
  obtain ⟨w11_388, hx11⟩ := hx11
  obtain ⟨w11_38c, hx11⟩ := hx11
  obtain ⟨w11_390, hx11⟩ := hx11
  obtain ⟨w11_394, hx11⟩ := hx11
  have K11_L := hx11
  exact .inr ⟨x1_0, root6_3, x3_0, x3_1, x4_0, x5_0, x6_0, x7_0, x8_0, x9_0, x10_0, x11_0, n11, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans (c11)))))))))), fR11, s11, E11, V11,
    by rw [r11_3, r10_3, r9_3, r8_3, r7_3, r6_3, r5_3, r4_3, r3_3, r2_3, r1_3], by rw [r11_4, r10_4, r9_4, r8_4, r7_4, r6_4, r5_4, r4_4, r3_4, r2_4, r1_4], r11_2, r11_18, r11_19, r11_20, r11_21, r11_22, r11_23, r11_24, r11_25, r11_26, r11_27, w11_3c, w11_54, w11_58, w11_5c, w11_60, w11_78, w11_7c, w11_388, w11_38c, w11_390, w11_394, ((K11_L.w32 (by decide) (by decide)).trans ((K10_L.w32 (by decide) (by decide)).trans ((K9_L.w32 (by decide) (by decide)).trans ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_1c)))))))))), ((K11_L.w32 (by decide) (by decide)).trans ((K10_L.w32 (by decide) (by decide)).trans ((K9_L.w32 (by decide) (by decide)).trans ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_20)))))))))), ((K11_L.w32 (by decide) (by decide)).trans ((K10_L.w32 (by decide) (by decide)).trans ((K9_L.w32 (by decide) (by decide)).trans ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_34)))))))))), ((K11_L.w32 (by decide) (by decide)).trans ((K10_L.w32 (by decide) (by decide)).trans ((K9_L.w32 (by decide) (by decide)).trans ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_40)))))))))), ((K11_L.w32 (by decide) (by decide)).trans ((K10_L.w32 (by decide) (by decide)).trans ((K9_L.w32 (by decide) (by decide)).trans ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_4c)))))))))), ((K11_L.w32 (by decide) (by decide)).trans ((K10_L.w32 (by decide) (by decide)).trans ((K9_L.w32 (by decide) (by decide)).trans ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans w3_64)))))))), ((K11_L.w32 (by decide) (by decide)).trans ((K10_L.w32 (by decide) (by decide)).trans ((K9_L.w32 (by decide) (by decide)).trans ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans w3_74)))))))), (fun j hj => (K11_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K10_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K9_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K8_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K7_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K6_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K5_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K4_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K3_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K2_L.range (by decide) (by decide) j hj).trans (q1_3e0 j hj)) j hj)) j hj)) j hj)) j hj)) j hj)) j hj)) j hj)) j hj)) j hj)), ((K11_L.w32 (by decide) (by decide)).trans ((K10_L.w32 (by decide) (by decide)).trans ((K9_L.w32 (by decide) (by decide)).trans ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_380)))))))))), ((K11_L.w32 (by decide) (by decide)).trans ((K10_L.w32 (by decide) (by decide)).trans ((K9_L.w32 (by decide) (by decide)).trans ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_398)))))))))), ((K11_L.w32 (by decide) (by decide)).trans ((K10_L.w32 (by decide) (by decide)).trans ((K9_L.w32 (by decide) (by decide)).trans ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_39c)))))))))), ((K11_L.w32 (by decide) (by decide)).trans ((K10_L.w32 (by decide) (by decide)).trans ((K9_L.w32 (by decide) (by decide)).trans ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_3a0)))))))))), ((K11_L.w32 (by decide) (by decide)).trans ((K10_L.w32 (by decide) (by decide)).trans ((K9_L.w32 (by decide) (by decide)).trans ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_3a4)))))))))), ((K11_L.b8 (by decide) (by decide)).trans ((K10_L.b8 (by decide) (by decide)).trans ((K9_L.b8 (by decide) (by decide)).trans ((K8_L.b8 (by decide) (by decide)).trans ((K7_L.b8 (by decide) (by decide)).trans ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans b1_384)))))))))), ((K11_L.b8 (by decide) (by decide)).trans ((K10_L.b8 (by decide) (by decide)).trans ((K9_L.b8 (by decide) (by decide)).trans ((K8_L.b8 (by decide) (by decide)).trans ((K7_L.b8 (by decide) (by decide)).trans ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans b3_3a8)))))))), ((K11_L.w32 (by decide) (by decide)).trans ((K10_L.w32 (by decide) (by decide)).trans ((K9_L.w32 (by decide) (by decide)).trans ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans w2_68))))))))), ((K11_L.w32 (by decide) (by decide)).trans ((K10_L.w32 (by decide) (by decide)).trans ((K9_L.w32 (by decide) (by decide)).trans ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans w2_6c))))))))), ((K11_L.w32 (by decide) (by decide)).trans ((K10_L.w32 (by decide) (by decide)).trans ((K9_L.w32 (by decide) (by decide)).trans ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans w2_70))))))))), ((K11_L.b8 (by decide) (by decide)).trans ((K10_L.b8 (by decide) (by decide)).trans ((K9_L.b8 (by decide) (by decide)).trans ((K8_L.b8 (by decide) (by decide)).trans ((K7_L.b8 (by decide) (by decide)).trans ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans b3_1fc)))))))), ((K11_L.b8 (by decide) (by decide)).trans ((K10_L.b8 (by decide) (by decide)).trans ((K9_L.b8 (by decide) (by decide)).trans ((K8_L.b8 (by decide) (by decide)).trans ((K7_L.b8 (by decide) (by decide)).trans ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans b3_420)))))))), ((K11_L.b8 (by decide) (by decide)).trans ((K10_L.b8 (by decide) (by decide)).trans ((K9_L.b8 (by decide) (by decide)).trans ((K8_L.b8 (by decide) (by decide)).trans ((K7_L.b8 (by decide) (by decide)).trans ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans b3_421)))))))), (((((((((((K1_L).trans K2_L).trans K3_L).trans K4_L).trans K5_L).trans K6_L).trans K7_L).trans K8_L).trans K9_L).trans K10_L).trans K11_L).mono (by decide)⟩

end C3.RV32.Sv
