import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvSegCkpt
import C3BootProofs.Proofs.SvCkdLoop
import C3BootProofs.Proofs.SvCSearch
import C3BootProofs.Proofs.SvCs1
import C3BootProofs.Proofs.SvCosigLoop
import C3BootProofs.Proofs.SvSegWin

/-!
# `sigstore::verify`: The transparency log entry

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The transparency log entry**: from the checkpoint at 0x142E to the successful exit at 0x1A9E: the checkpoint, the log that signed it, its signatures, the entry's index, and the validity windows. -/
theorem sv_seg_log {B out bp x20 x21 x22 x23 x24 x25 x26 x27 pv ckp ckl : Word} {v : Nat → Word} {n0 : Machine} {w68 : Word} {w6c : Word} {w70 : Word} {w3c : Word} {w54 : Word} {w58 : Word} {w5c : Word} {w60 : Word} {w78 : Word} {w7c : Word}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x142E (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = pv)
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
    (CK0 : SvCkCode M0)
    (hckp : memLoad32 M0 (bp + 0x18) = ckp)
    (hckl : memLoad32 M0 (bp + 0x1C) = ckl)
    (ckp_in4 : SvIn B (bp + 0x18) 4)
    (ckl_in4 : SvIn B (bp + 0x1C) 4)
    (a_ckp : (bp + 0x18).toNat % 4 = 0)
    (a_ckl : (bp + 0x1C).toNat % 4 = 0)
    (ck_in : SvIn B ckp ckl.toNat)
    (H' : ∀ i, i < 16 → ∀ c'_3 q'_3, (c'_3, q'_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), ((x21) + BitVec.ofNat 32 0x108)) → (SvIn B (q'_3 + 0x20) 4) ∧ (SvIn B (q'_3 + 0x24) 4) ∧ ((q'_3 + 0x20).toNat % 4 = 0) ∧ ((q'_3 + 0x24).toNat % 4 = 0) ∧ ((memLoad32 M0 (q'_3 + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (q'_3 + 0x20)) (memLoad32 M0 (q'_3 + 0x24)).toNat))
    (S2 : SvSha2Code M0)
    (RS : SvRoSep B)
    (kp_in4 : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (x21 + BitVec.ofNat 32 0x108)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x18) 4)
    (kw_in4 : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (x21 + BitVec.ofNat 32 0x108)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x1C) 4)
    (a_kp : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (x21 + BitVec.ofNat 32 0x108)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x18).toNat % 4 = 0)
    (a_kw : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (x21 + BitVec.ofNat 32 0x108)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x1C).toNat % 4 = 0)
    (kp_in : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (x21 + BitVec.ofNat 32 0x108)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 32)
    (EE0 : EvEnv M0)
    (hiv : (s5Hv M0 (BitVec.ofNat 32 (img% sha512IVAddress))).toList = Sha512.h0)
    (pk_in : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (x21 + BitVec.ofNat 32 0x108)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 32)
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68)
    (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70)
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c)
    (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54)
    (w0_58 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58)
    (w0_5c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c)
    (w0_60 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c)
    (lid_in : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (x21 + BitVec.ofNat 32 0x108)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + BitVec.ofNat 32 0x5) 19)
    (lih_in : SvIn B (bp + 0x2C) 4)
    (lil_in : SvIn B (bp + 0x28) 4)
    (a_lih : (bp + 0x2C).toNat % 4 = 0)
    (a_lil : (bp + 0x28).toNat % 4 = 0)
    (RK0 : SvRkCode M0)
    (dgi_in : SvIn B x20 32)
    (sig_in : SvIn B w70 w68.toNat)
    (crt_in : SvIn B w6c x22.toNat)
    (pp_in4 : SvIn B (bp + 0x10) 4)
    (pl_in4 : SvIn B (bp + 0x14) 4)
    (a_pp : (bp + 0x10).toNat % 4 = 0)
    (a_pl : (bp + 0x14).toNat % 4 = 0)
    (pp_in : SvIn B (memLoad32 M0 (bp + 0x10)) (memLoad32 M0 (bp + 0x14)).toNat)
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
    ((pv ≠ 0) ∧
      ∃ ix8_1_1, nlScan M0 (ckp) 0 ((ckl).toNat) = some ix8_1_1 ∧
      ∃ ix18_1_1, nlScan M0 ((ckp) + BitVec.ofNat 32 (ix8_1_1 + 1)) 0 (((ckl).toNat) - (ix8_1_1 + 1)) = some ix18_1_1 ∧
      ∃ ix26_1_1, nlScan M0 (((ckp) + BitVec.ofNat 32 (ix8_1_1 + 1)) + BitVec.ofNat 32 (ix18_1_1 + 1)) 0 ((((ckl).toNat) - (ix8_1_1 + 1)) - (ix18_1_1 + 1)) = some ix26_1_1 ∧
      ∃ ix34_1_1, nlScan M0 ((((ckp) + BitVec.ofNat 32 (ix8_1_1 + 1)) + BitVec.ofNat 32 (ix18_1_1 + 1)) + BitVec.ofNat 32 (ix26_1_1 + 1)) 0 (((((ckl).toNat) - (ix8_1_1 + 1)) - (ix18_1_1 + 1)) - (ix26_1_1 + 1)) = some ix34_1_1 ∧
      (BitVec.ofNat 32 ix34_1_1 = 0) ∧
      (BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1_1 + 1)) - (ix18_1_1 + 1)) - (ix26_1_1 + 1)) - BitVec.ofNat 32 (ix34_1_1 + 1) ≠ 0) ∧
      (((1 < (BitVec.ofNat 32 ix18_1_1).toNat) ∧ ((BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1_1 + 1)) - (ix18_1_1 + 1)) - (ix26_1_1 + 1)) - BitVec.ofNat 32 (ix34_1_1 + 1)).toNat < ckl.toNat) ∧ (¬ (ckl).toNat < ((aluEval .xor ((BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1_1 + 1)) - (ix18_1_1 + 1)) - (ix26_1_1 + 1)) - BitVec.ofNat 32 (ix34_1_1 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl)).toNat) ∧ (¬ (((BitVec.ofNat 32 ix18_1_1)) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat) ∧ (M0 ((ckp) + BitVec.ofNat 32 (ix8_1_1 + 1)) ≠ 0x30)) ∨ ((¬ (1 < (BitVec.ofNat 32 ix18_1_1).toNat)) ∧ ((BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1_1 + 1)) - (ix18_1_1 + 1)) - (ix26_1_1 + 1)) - BitVec.ofNat 32 (ix34_1_1 + 1)).toNat < ckl.toNat) ∧ (¬ (ckl).toNat < ((aluEval .xor ((BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1_1 + 1)) - (ix18_1_1 + 1)) - (ix26_1_1 + 1)) - BitVec.ofNat 32 (ix34_1_1 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl)).toNat) ∧ (¬ (((BitVec.ofNat 32 ix18_1_1)) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat))) ∧
      ∃ c'_2 p'_2 w64'_2 w74'_2, (c'_2, p'_2, w64'_2, w74'_2) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))))) (BitVec.ofNat 32 ix18_1_1).toNat ((BitVec.ofNat 32 ix18_1_1), ((ckp) + BitVec.ofNat 32 (ix8_1_1 + 1)), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0)) ∧ (∀ i, i < (BitVec.ofNat 32 ix18_1_1).toNat → ∀ c'_2 p'_2 w64'_2 w74'_2, (c'_2, p'_2, w64'_2, w74'_2) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))))) i ((BitVec.ofNat 32 ix18_1_1), ((ckp) + BitVec.ofNat 32 (ix8_1_1 + 1)), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0)) → ((((((M0 (p'_2)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF).toNat < (BitVec.ofNat 32 0xA).toNat)) ∧ (((aluEval .sltu ((aluEval .mul (w74'_2) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64'_2) (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64'_2) (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74'_2) (BitVec.ofNat 32 0xA))) = 0)) ∧ (((aluEval .sltu (((((M0 (p'_2)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64'_2) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64'_2) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74'_2) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64'_2) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p'_2)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64'_2) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64'_2) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74'_2) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64'_2) (BitVec.ofNat 32 0xA)))) = 0))) ∧
      (w74'_2.toNat < 2 ^ 31) ∧ ∃ bs7_2, base64Decode (memBytes M0 ((((ckp) + BitVec.ofNat 32 (ix8_1_1 + 1)) + BitVec.ofNat 32 (ix18_1_1 + 1))) (((BitVec.ofNat 32 ix26_1_1)).toNat)) = some bs7_2 ∧ (bs7_2.length = 32) ∧
      ∃ k_3, k_3 < 16 ∧
      (∀ i, i < k_3 → ∀ c'_3 q'_3, (c'_3, q'_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), ((x21) + BitVec.ofNat 32 0x108)) → ¬ (memBytes M0 (memLoad32 M0 (q'_3 + 0x20)) (memLoad32 M0 (q'_3 + 0x24)).toNat = memBytes M0 ckp (BitVec.ofNat 32 ix8_1_1).toNat)) ∧
      ∃ c'_3 q'_3, (c'_3, q'_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k_3 ((BitVec.ofNat 32 0x200), ((x21) + BitVec.ofNat 32 0x108)) ∧ (memBytes M0 (memLoad32 M0 (q'_3 + 0x20)) (memLoad32 M0 (q'_3 + 0x24)).toNat = memBytes M0 ckp (BitVec.ofNat 32 ix8_1_1).toNat) ∧
      ((memLoad32 M0 (q'_3 + 0x20)) ≠ 0) ∧
      ∃ sg_5, ∃ k_5 f'_5 w38'_5 w50'_5 sg'_5, svChain (sv_cosigStep B out bp x20 x22 x23 (memLoad32 M0 (q'_3 + 0x24)) (le4 (sha256 (memBytes M0 (ckp) (((BitVec.ofNat 32 ix8_1_1)).toNat) ++ memBytes M0 (BitVec.ofNat 32 (img% svNewlineAddress)) (1) ++ memBytes M0 (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes M0 ((memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x18))) (32))) 0) ckp (BitVec.ofNat 32 ix8_1_1) (memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x18)) ckp ((aluEval .xor ((BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1_1 + 1)) - (ix18_1_1 + 1)) - (ix26_1_1 + 1)) - BitVec.ofNat 32 (ix34_1_1 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl)) v M0) k_5 ((BitVec.ofNat 32 0x0), (((((ckp) + BitVec.ofNat 32 (ix8_1_1 + 1)) + BitVec.ofNat 32 (ix18_1_1 + 1)) + BitVec.ofNat 32 (ix26_1_1 + 1)) + BitVec.ofNat 32 (ix34_1_1 + 1)), (BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1_1 + 1)) - (ix18_1_1 + 1)) - (ix26_1_1 + 1)) - BitVec.ofNat 32 (ix34_1_1 + 1)), sg_5) (f'_5, w38'_5, w50'_5, sg'_5) ∧
      w50'_5 = 0 ∧
      ((f'_5) &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ (evSpec (sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 0x420) sg'_5) (memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) ckp (((aluEval .xor ((BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1_1 + 1)) - (ix18_1_1 + 1)) - (ix26_1_1 + 1)) - BitVec.ofNat 32 (ix34_1_1 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl))).toNat = true) ∧
      ((((memLoad32 M0 (bp + 0x2C)) = w74'_2) ∧ (aluEval .sltu ((memLoad32 M0 (bp + 0x28))) (w64'_2) ≠ 0)) ∨ ((¬ ((memLoad32 M0 (bp + 0x2C)) = w74'_2)) ∧ (aluEval .sltu ((memLoad32 M0 (bp + 0x2C))) (w74'_2) ≠ 0))) ∧
      ∃ root6_3_6, rootFromInclusion (pair64 ((memLoad32 M0 (bp + 0x28))) ((memLoad32 M0 (bp + 0x2C)))) (pair64 (w64'_2) (w74'_2)) ((sha256 ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes M0 (w70) ((w68).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid2Address)) (0x54) ++ base64Encode (memBytes M0 (w6c) ((x22).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPostAddress)) (0x7)))) (memBytes M0 ((memLoad32 M0 (bp + 0x10))) (((memLoad32 M0 (bp + 0x14))).toNat)) = some root6_3_6 ∧
      (b32 root6_3_6 = b32 bs7_2) ∧
      (((w5c = w7c) ∧ (aluEval .sltu (w3c) (w60) = 0)) ∨ ((¬ (w5c = w7c)) ∧ (aluEval .sltu (w7c) (w5c) = 0))) ∧
      (((w7c = w54) ∧ (aluEval .sltu (w58) (w3c) = 0)) ∨ ((¬ (w7c = w54)) ∧ (aluEval .sltu (w54) (w7c) = 0))) ∧
      ((((memLoad32 M0 (x23 + 0xFFFFFFE8)) = w7c) ∧ (aluEval .sltu (w3c) ((memLoad32 M0 (x23 + 0xFFFFFFE4))) = 0)) ∨ ((¬ ((memLoad32 M0 (x23 + 0xFFFFFFE8)) = w7c)) ∧ (aluEval .sltu (w7c) ((memLoad32 M0 (x23 + 0xFFFFFFE8))) = 0))) ∧
      (((w7c = (memLoad32 M0 (x23 + 0xFFFFFFF0))) ∧ (aluEval .sltu ((memLoad32 M0 (x23 + 0xFFFFFFEC))) (w3c) = 0)) ∨ ((¬ (w7c = (memLoad32 M0 (x23 + 0xFFFFFFF0)))) ∧ (aluEval .sltu ((memLoad32 M0 (x23 + 0xFFFFFFF0))) (w7c) = 0))) ∧
      ((((memLoad32 M0 (w78 + 0xC)) = w7c) ∧ (aluEval .sltu (w3c) ((memLoad32 M0 (w78 + 0x8))) = 0)) ∨ ((¬ ((memLoad32 M0 (w78 + 0xC)) = w7c)) ∧ (aluEval .sltu (w7c) ((memLoad32 M0 (w78 + 0xC))) = 0))) ∧
      (((w7c = (memLoad32 M0 (w78 + 0x14))) ∧ (aluEval .sltu ((memLoad32 M0 (w78 + 0x10))) (w3c) = 0)) ∨ ((¬ (w7c = (memLoad32 M0 (w78 + 0x14)))) ∧ (aluEval .sltu ((memLoad32 M0 (w78 + 0x14))) (w7c) = 0))) ∧
      ((((memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) = w7c) ∧ (aluEval .sltu (w3c) ((memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 3))) = 0)) ∨ ((¬ ((memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) = w7c)) ∧ (aluEval .sltu (w7c) ((memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7))) = 0))) ∧
      (((w7c = (memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15))) ∧ (aluEval .sltu ((memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 11))) (w3c) = 0)) ∨ ((¬ (w7c = (memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15)))) ∧ (aluEval .sltu ((memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15))) (w7c) = 0))) ∧
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
        reg n' (20 : Fin 32) = BitVec.ofNat 32 0x1E ∧
        reg n' (21 : Fin 32) = (memLoad32 M0 (bp + 0x28)) ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = (memLoad32 M0 (bp + 0x2C)) ∧
        reg n' (25 : Fin 32) = (memLoad32 M0 (q'_3 + 0x24)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 3)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x390) = (memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 11)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x394) = (memLoad32 M0 (((((q'_3) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x1C)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (bs7_2.getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = (memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x18)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = (memLoad32 M0 (q'_3 + 0x20)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = ((q'_3) + BitVec.ofNat 32 0x20) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74'_2 ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (bs7_2.getD (1 + j) 0)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = (memLoad32 M0 (q'_3 + 0x20)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = (memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x18)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = (memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x1C)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A0) = w64'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A4) = w74'_2 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = ((memLoad32 M0 (q'_3 + 0x24))).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (bs7_2.getD 0 0)).zeroExtend 32).extractLsb' 0 8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1FC) = BitVec.ofNat 8 (root6_3_6.getD 0 0) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6_3_6.getD 0 0) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ((aluEval .xor ((BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1_1 + 1)) - (ix18_1_1 + 1)) - (ix26_1_1 + 1)) - BitVec.ofNat 32 (ix34_1_1 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38'_5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50'_5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (BitVec.ofNat 32 ix8_1_1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = (le4 (sha256 (memBytes M0 (ckp) (((BitVec.ofNat 32 ix8_1_1)).toNat) ++ memBytes M0 (BitVec.ofNat 32 (img% svNewlineAddress)) (1) ++ memBytes M0 (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes M0 ((memLoad32 M0 (((q'_3) + BitVec.ofNat 32 0x20) + 0x18))) (32))) 0) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f'_5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f'_5) &&& BitVec.ofNat 32 0x1 ∧
        SvKeepL B n0.mem n'.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10), (0x50, 0x4), (0x24, 0x4), (0x38, 0x4), (0x64, 0x4), (0x74, 0x4), (0x420, 0x60), (0x400, 0x8), (0x20, 0x4), (0x3E0, 0x1F), (0x4C, 0x4), (0x40, 0x4), (0x1C, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4), (0x400, 0x20), (0x30, 0x4), (0x18, 0x4), (0x2C, 0x4), (0xC, 0x4), (0x8, 0x4), (0x10, 0x4), (0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3), (0x14, 0x4), (0x1FC, 0x3F), (0x421, 0x3F), (0x420, 0x1), (0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1), (0x3A0, 0x4), (0x3A4, 0x4), (0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x21), (0x1FD, 0x1F), (0x1FC, 0x1)]) := by
  rcases sv_seg_ck FW E0 V0 hret hO s0 M0 fM g0_2 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 CK0 hckp hckl ckp_in4 ckl_in4 a_ckp a_ckl ck_in with e | hx1
  · exact .inl e
  obtain ⟨x1_0, hx1⟩ := hx1
  obtain ⟨ix8_1_1, hx1⟩ := hx1
  obtain ⟨x1_1, hx1⟩ := hx1
  obtain ⟨ix18_1_1, hx1⟩ := hx1
  obtain ⟨x1_2, hx1⟩ := hx1
  obtain ⟨ix26_1_1, hx1⟩ := hx1
  obtain ⟨x1_3, hx1⟩ := hx1
  obtain ⟨ix34_1_1, hx1⟩ := hx1
  obtain ⟨x1_4, hx1⟩ := hx1
  obtain ⟨x1_5, hx1⟩ := hx1
  obtain ⟨x1_6, hx1⟩ := hx1
  obtain ⟨x1_7, hx1⟩ := hx1
  obtain ⟨n1, hx1⟩ := hx1
  obtain ⟨c1, hx1⟩ := hx1
  obtain ⟨fR1, hx1⟩ := hx1
  obtain ⟨s1, hx1⟩ := hx1
  obtain ⟨E1, hx1⟩ := hx1
  obtain ⟨V1, hx1⟩ := hx1
  obtain ⟨r1_3, hx1⟩ := hx1
  obtain ⟨r1_4, hx1⟩ := hx1
  obtain ⟨r1_2, hx1⟩ := hx1
  obtain ⟨r1_8, hx1⟩ := hx1
  obtain ⟨r1_9, hx1⟩ := hx1
  obtain ⟨r1_a0, hx1⟩ := hx1
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
  obtain ⟨w1_24, hx1⟩ := hx1
  obtain ⟨w1_38, hx1⟩ := hx1
  obtain ⟨w1_50, hx1⟩ := hx1
  obtain ⟨w1_64, hx1⟩ := hx1
  obtain ⟨w1_74, hx1⟩ := hx1
  obtain ⟨w1_428, hx1⟩ := hx1
  obtain ⟨w1_28, hx1⟩ := hx1
  obtain ⟨w1_44, hx1⟩ := hx1
  obtain ⟨w1_48, hx1⟩ := hx1
  obtain ⟨w1_42c, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_ckdloop_run FW hret hO M0 E1 V1 s1 fR1 r1_2 r1_8 r1_a0 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_25 r1_26 r1_27 w1_64 w1_74 ((((ck_in).nlRest x1_1).nlLine x1_2).ofNatLen) (((((ck_in).nlRest x1_1).nlRest x1_2).nlLine x1_3).ofNatLen) CK0 with e | hx2
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  obtain ⟨c'_2, hx2⟩ := hx2
  obtain ⟨p'_2, hx2⟩ := hx2
  obtain ⟨w64'_2, hx2⟩ := hx2
  obtain ⟨w74'_2, hx2⟩ := hx2
  obtain ⟨x2_0, hx2⟩ := hx2
  obtain ⟨x2_1, hx2⟩ := hx2
  obtain ⟨x2_2, hx2⟩ := hx2
  obtain ⟨bs7_2, hx2⟩ := hx2
  obtain ⟨x2_3, hx2⟩ := hx2
  obtain ⟨x2_4, hx2⟩ := hx2
  obtain ⟨n2, hx2⟩ := hx2
  obtain ⟨c2, hx2⟩ := hx2
  obtain ⟨s2, hx2⟩ := hx2
  obtain ⟨E2, hx2⟩ := hx2
  obtain ⟨V2, hx2⟩ := hx2
  obtain ⟨fR2, hx2⟩ := hx2
  obtain ⟨r2_2, hx2⟩ := hx2
  obtain ⟨r2_3, hx2⟩ := hx2
  obtain ⟨r2_4, hx2⟩ := hx2
  obtain ⟨r2_8, hx2⟩ := hx2
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
  obtain ⟨w2_20, hx2⟩ := hx2
  obtain ⟨w2_4c, hx2⟩ := hx2
  obtain ⟨w2_64, hx2⟩ := hx2
  obtain ⟨w2_74, hx2⟩ := hx2
  obtain ⟨w2_404, hx2⟩ := hx2
  obtain ⟨b2_400, hx2⟩ := hx2
  obtain ⟨b2_420, hx2⟩ := hx2
  obtain ⟨q2_3e0, hx2⟩ := hx2
  obtain ⟨q2_420, hx2⟩ := hx2
  have K2_L := hx2
  rcases sv_csearch_st FW hret hO M0 (fun _ _ h => svCnt_zero Prod.fst (BitVec.ofNat 32 0x200) 0xFFFFFFE0 (by intro _; rfl) rfl (by decide) (congrArg Prod.fst h)) E2 V2 s2 fR2 r2_2 r2_8 r2_18 r2_19 r2_20 r2_21 r2_22 r2_23 r2_24 r2_26 r2_27 ((K2_L.w32 (by decide) (by decide)).trans w1_44) ((K2_L.w32 (by decide) (by decide)).trans w1_48) w2_4c (fun i hi c'_3 q'_3 h => ⟨(svCnt_ne Prod.fst (BitVec.ofNat 32 0x200) 0xFFFFFFE0 (by intro _; rfl) rfl (by decide) hi (congrArg Prod.fst h)), (H' i hi c'_3 q'_3 h).1, (H' i hi c'_3 q'_3 h).2.1, (H' i hi c'_3 q'_3 h).2.2.1, (H' i hi c'_3 q'_3 h).2.2.2.1, (H' i hi c'_3 q'_3 h).2.2.2.2, (((ck_in).nlLine x1_1).ofNatLen)⟩) with e | hx3
  · exact .inl (SvErrRet.pre (c1.trans (c2)) (by rw [r2_3, r1_3]) (by rw [r2_4, r1_4])
      (fun x hx => (fR2 x hx).trans (fM x hx).symm) e)
  obtain ⟨k_3, hx3⟩ := hx3
  obtain ⟨x3_0, hx3⟩ := hx3
  obtain ⟨x3_1, hx3⟩ := hx3
  obtain ⟨c'_3, hx3⟩ := hx3
  obtain ⟨q'_3, hx3⟩ := hx3
  obtain ⟨x3_2, hx3⟩ := hx3
  obtain ⟨x3_3, hx3⟩ := hx3
  obtain ⟨x3_4, hx3⟩ := hx3
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
  obtain ⟨w3_40, hx3⟩ := hx3
  obtain ⟨w3_44, hx3⟩ := hx3
  obtain ⟨w3_48, hx3⟩ := hx3
  obtain ⟨w3_4c, hx3⟩ := hx3
  have K3_L := hx3
  rcases sv_cs1 FW E3 V3 hret hO s3 M0 fR3 r3_2 r3_8 r3_18 r3_19 r3_20 r3_21 r3_22 r3_23 r3_24 r3_25 r3_26 r3_27 w3_44 w3_48 w3_4c S2 RS rfl rfl (kp_in4 k_3 x3_0 c'_3 q'_3 x3_2 x3_4) (kw_in4 k_3 x3_0 c'_3 q'_3 x3_2 x3_4) (a_kp k_3 x3_0 c'_3 q'_3 x3_2 x3_4) (a_kw k_3 x3_0 c'_3 q'_3 x3_2 x3_4) (kp_in k_3 x3_0 c'_3 q'_3 x3_2 x3_4) (((ck_in).nlLine x1_1).ofNatLen) with ⟨-, e⟩ | hx4
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3))) (by rw [r3_3, r2_3, r1_3]) (by rw [r3_4, r2_4, r1_4])
      (fun x hx => (fR3 x hx).trans (fM x hx).symm) e)
  obtain ⟨n4, hx4⟩ := hx4
  obtain ⟨c4, hx4⟩ := hx4
  obtain ⟨s4, hx4⟩ := hx4
  obtain ⟨E4, hx4⟩ := hx4
  obtain ⟨V4, hx4⟩ := hx4
  obtain ⟨fR4, hx4⟩ := hx4
  obtain ⟨r4_2, hx4⟩ := hx4
  obtain ⟨r4_3, hx4⟩ := hx4
  obtain ⟨r4_4, hx4⟩ := hx4
  obtain ⟨r4_8, hx4⟩ := hx4
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
  obtain ⟨w4_18, hx4⟩ := hx4
  obtain ⟨w4_1c, hx4⟩ := hx4
  obtain ⟨w4_30, hx4⟩ := hx4
  obtain ⟨w4_34, hx4⟩ := hx4
  obtain ⟨w4_44, hx4⟩ := hx4
  obtain ⟨w4_48, hx4⟩ := hx4
  obtain ⟨w4_4c, hx4⟩ := hx4
  obtain ⟨w4_400, hx4⟩ := hx4
  obtain ⟨w4_420, hx4⟩ := hx4
  obtain ⟨w4_424, hx4⟩ := hx4
  obtain ⟨w4_428, hx4⟩ := hx4
  obtain ⟨w4_42c, hx4⟩ := hx4
  obtain ⟨w4_430, hx4⟩ := hx4
  obtain ⟨w4_434, hx4⟩ := hx4
  obtain ⟨w4_438, hx4⟩ := hx4
  obtain ⟨w4_43c, hx4⟩ := hx4
  have K4_L := hx4
  rcases sv_cosigloop_st0 FW hret hO M0 (Nat.le_refl _) E4 V4 s4 fR4 r4_2 r4_18 r4_19 r4_20 r4_22 r4_23 r4_25 w4_18 ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_24))) ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_28))) w4_30 w4_34 ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_38))) w4_44 w4_48 ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_50))) (by rw [svSubNat_toNat (by have := ((((ck_in).nlRest x1_1).nlRest x1_2).nlRest x1_3).lo; omega) (by have := (nlScan_lt _ _ _ x1_4).2; omega)]; exact ((((ck_in).nlRest x1_1).nlRest x1_2).nlRest x1_3).nlRest x1_4) CK0 (((ck_in).nlLine x1_1).ofNatLen) EE0 RS hiv (pk_in k_3 x3_0 c'_3 q'_3 x3_2 x3_4) ((ck_in).shrink (svNotAdd_le (by have := (ck_in).lo; have := (nlScan_lt _ _ _ x1_1).2; have := (nlScan_lt _ _ _ x1_2).2; have := (nlScan_lt _ _ _ x1_3).2; have := (nlScan_lt _ _ _ x1_4).2; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow] at *; omega))) ((((ck_in).shrink (svNotAdd_le (by have := (ck_in).lo; have := (nlScan_lt _ _ _ x1_1).2; have := (nlScan_lt _ _ _ x1_2).2; have := (nlScan_lt _ _ _ x1_3).2; have := (nlScan_lt _ _ _ x1_4).2; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow] at *; omega)))).len_lt) with e | hx5
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4)))) (by rw [r4_3, r3_3, r2_3, r1_3]) (by rw [r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR4 x hx).trans (fM x hx).symm) e)
  obtain ⟨sg_5, hx5⟩ := hx5
  obtain ⟨k_5, hx5⟩ := hx5
  obtain ⟨f'_5, hx5⟩ := hx5
  obtain ⟨w38'_5, hx5⟩ := hx5
  obtain ⟨w50'_5, hx5⟩ := hx5
  obtain ⟨sg'_5, hx5⟩ := hx5
  obtain ⟨x5_0, hx5⟩ := hx5
  obtain ⟨x5_1, hx5⟩ := hx5
  obtain ⟨x5_2, hx5⟩ := hx5
  obtain ⟨x5_3, hx5⟩ := hx5
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
  obtain ⟨r5_22, hx5⟩ := hx5
  obtain ⟨r5_23, hx5⟩ := hx5
  obtain ⟨r5_25, hx5⟩ := hx5
  obtain ⟨w5_18, hx5⟩ := hx5
  obtain ⟨w5_24, hx5⟩ := hx5
  obtain ⟨w5_28, hx5⟩ := hx5
  obtain ⟨w5_2c, hx5⟩ := hx5
  obtain ⟨w5_30, hx5⟩ := hx5
  obtain ⟨w5_34, hx5⟩ := hx5
  obtain ⟨w5_38, hx5⟩ := hx5
  obtain ⟨w5_44, hx5⟩ := hx5
  obtain ⟨w5_48, hx5⟩ := hx5
  obtain ⟨w5_50, hx5⟩ := hx5
  obtain ⟨q5_1fc, hx5⟩ := hx5
  obtain ⟨q5_421, hx5⟩ := hx5
  have K5_L := hx5
  rcases sv_seg_win FW E5 V5 hret hO s5 M0 fR5 r5_2 r5_18 r5_19 r5_20 rfl r5_22 r5_23 rfl r5_25 rfl rfl ((K5_L.w32 (by decide) (by decide)).trans w4_1c) ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans w2_20))) w5_34 ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans w3_40)) ((K5_L.w32 (by decide) (by decide)).trans w4_4c) ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans w2_64))) ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans w2_74))) (fun j hj => (K5_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K4_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K3_L.range (by decide) (by decide) j hj).trans (q2_3e0 j hj)) j hj)) j hj)) RS (lid_in k_3 x3_0 c'_3 q'_3 x3_2 x3_4) x3_4 rfl rfl lih_in lil_in a_lih a_lil ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_68))))) ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_6c))))) ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_70))))) S2 RK0 dgi_in sig_in crt_in pp_in4 pl_in4 a_pp a_pl pp_in ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_3c))))) ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_54))))) ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_58))))) ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_5c))))) ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_60))))) ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_78))))) ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_7c))))) ii2h ai2h ii2l ai2l ii3h ai3h ii3l ai3l it4h at4h it4l at4l it5h at5h it5l at5l with e | hx6
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5))))) (by rw [r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR5 x hx).trans (fM x hx).symm) e)
  obtain ⟨x6_0, hx6⟩ := hx6
  obtain ⟨root6_3_6, hx6⟩ := hx6
  obtain ⟨x6_1, hx6⟩ := hx6
  obtain ⟨x6_2, hx6⟩ := hx6
  obtain ⟨x6_3, hx6⟩ := hx6
  obtain ⟨x6_4, hx6⟩ := hx6
  obtain ⟨x6_5, hx6⟩ := hx6
  obtain ⟨x6_6, hx6⟩ := hx6
  obtain ⟨x6_7, hx6⟩ := hx6
  obtain ⟨x6_8, hx6⟩ := hx6
  obtain ⟨x6_9, hx6⟩ := hx6
  obtain ⟨x6_10, hx6⟩ := hx6
  obtain ⟨n6, hx6⟩ := hx6
  obtain ⟨c6, hx6⟩ := hx6
  obtain ⟨fR6, hx6⟩ := hx6
  obtain ⟨s6, hx6⟩ := hx6
  obtain ⟨E6, hx6⟩ := hx6
  obtain ⟨V6, hx6⟩ := hx6
  obtain ⟨r6_3, hx6⟩ := hx6
  obtain ⟨r6_4, hx6⟩ := hx6
  obtain ⟨r6_2, hx6⟩ := hx6
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
  obtain ⟨w6_1c, hx6⟩ := hx6
  obtain ⟨w6_20, hx6⟩ := hx6
  obtain ⟨w6_34, hx6⟩ := hx6
  obtain ⟨w6_40, hx6⟩ := hx6
  obtain ⟨w6_4c, hx6⟩ := hx6
  obtain ⟨w6_64, hx6⟩ := hx6
  obtain ⟨w6_74, hx6⟩ := hx6
  obtain ⟨q6_3e0, hx6⟩ := hx6
  obtain ⟨w6_380, hx6⟩ := hx6
  obtain ⟨w6_398, hx6⟩ := hx6
  obtain ⟨w6_39c, hx6⟩ := hx6
  obtain ⟨w6_3a0, hx6⟩ := hx6
  obtain ⟨w6_3a4, hx6⟩ := hx6
  obtain ⟨b6_384, hx6⟩ := hx6
  obtain ⟨b6_3a8, hx6⟩ := hx6
  obtain ⟨w6_68, hx6⟩ := hx6
  obtain ⟨w6_6c, hx6⟩ := hx6
  obtain ⟨w6_70, hx6⟩ := hx6
  obtain ⟨b6_1fc, hx6⟩ := hx6
  obtain ⟨b6_420, hx6⟩ := hx6
  obtain ⟨b6_421, hx6⟩ := hx6
  have K6_L := hx6
  exact .inr ⟨x1_0, ix8_1_1, x1_1, ix18_1_1, x1_2, ix26_1_1, x1_3, ix34_1_1, x1_4, x1_5, x1_6, x1_7, c'_2, p'_2, w64'_2, w74'_2, x2_0, x2_1, x2_2, bs7_2, x2_3, x2_4, k_3, x3_0, x3_1, c'_3, q'_3, x3_2, x3_3, x3_4, sg_5, k_5, f'_5, w38'_5, w50'_5, sg'_5, x5_0, x5_1, x5_2, x5_3, x6_0, root6_3_6, x6_1, x6_2, x6_3, x6_4, x6_5, x6_6, x6_7, x6_8, x6_9, x6_10, n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6))))), fR6, s6, E6, V6,
    by rw [r6_3, r5_3, r4_3, r3_3, r2_3, r1_3], by rw [r6_4, r5_4, r4_4, r3_4, r2_4, r1_4], r6_2, r6_18, r6_19, r6_20, r6_21, r6_22, r6_23, r6_24, r6_25, w6_3c, w6_54, w6_58, w6_5c, w6_60, w6_78, w6_7c, w6_388, w6_38c, w6_390, w6_394, w6_1c, w6_20, w6_34, w6_40, w6_4c, w6_64, w6_74, q6_3e0, w6_380, w6_398, w6_39c, w6_3a0, w6_3a4, b6_384, b6_3a8, w6_68, w6_6c, w6_70, b6_1fc, b6_420, b6_421, ((K6_L.w32 (by decide) (by decide)).trans w5_24), ((K6_L.w32 (by decide) (by decide)).trans w5_38), ((K6_L.w32 (by decide) (by decide)).trans w5_50), ((K6_L.w32 (by decide) (by decide)).trans w5_28), ((K6_L.w32 (by decide) (by decide)).trans w5_44), ((K6_L.w32 (by decide) (by decide)).trans w5_48), ((K6_L.w32 (by decide) (by decide)).trans w5_18), ((K6_L.w32 (by decide) (by decide)).trans w5_30), ((K6_L.w32 (by decide) (by decide)).trans w5_2c), ((((((K1_L).trans K2_L).trans K3_L).trans K4_L).trans K5_L).trans K6_L).mono (by decide)⟩

end C3.RV32.Sv
