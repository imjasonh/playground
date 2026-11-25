import C3BootProofs.Proofs.SvSha2

/-!
# `sigstore::verify`: the timestamp's digests

From 0x139C to 0x1416: SHA-256 of the TSTInfo is the signed `messageDigest`, SHA-256 of the image signature is the TSTInfo's message imprint, the signed attributes aren't empty, and the frame at offset 0x420 holds SHA-256 of the signed attributes with their first byte replaced by 0x31.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTsig13a0 : List BInstr :=
  [.aluImm .add a0 sp 0x420]
theorem svTsig13a0_end : blockEnd sigstoreVerifyCode 0x13A0 svTsig13a0 = some 0x13A4 := by
  simp only [svTsig13a0]
  rw [blockEnd, sv_at_13a0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsig13ae : List BInstr :=
  [.aluImm .add a0 sp 0x420]
theorem svTsig13ae_end : blockEnd sigstoreVerifyCode 0x13AE svTsig13ae = some 0x13B2 := by
  simp only [svTsig13ae]
  rw [blockEnd, sv_at_13ae]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsig13bc : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x1F]
theorem svTsig13bc_end : blockEnd sigstoreVerifyCode 0x13BC svTsig13bc = some 0x13BE := by
  simp only [svTsig13bc]
  rw [blockEnd, sv_at_13bc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsig13c2 : List BInstr :=
  [.aluImm .add a0 sp 0x420]
theorem svTsig13c2_end : blockEnd sigstoreVerifyCode 0x13C2 svTsig13c2 = some 0x13C6 := by
  simp only [svTsig13c2]
  rw [blockEnd, sv_at_13c2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsig13d2 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .alu .add a1 x0 (27 : Fin 32)]
theorem svTsig13d2_end : blockEnd sigstoreVerifyCode 0x13D2 svTsig13d2 = some 0x13D8 := by
  simp only [svTsig13d2]
  rw [blockEnd, sv_at_13d2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_13d6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsig1552 : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x0]
theorem svTsig1552_end : blockEnd sigstoreVerifyCode 0x1552 svTsig1552 = some 0x1554 := by
  simp only [svTsig1552]
  rw [blockEnd, sv_at_1552]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsig13ec : List BInstr :=
  [.aluImm .add a0 a0 0x1]
theorem svTsig13ec_end : blockEnd sigstoreVerifyCode 0x13EC svTsig13ec = some 0x13EE := by
  simp only [svTsig13ec]
  rw [blockEnd, sv_at_13ec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsig13f0 : List BInstr :=
  [.aluImm .add a1 a1 0xFFFFFFFF]
theorem svTsig13f0_end : blockEnd sigstoreVerifyCode 0x13F0 svTsig13f0 = some 0x13F2 := by
  simp only [svTsig13f0]
  rw [blockEnd, sv_at_13f0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsig13f2 : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF855]
theorem svTsig13f2_end : blockEnd sigstoreVerifyCode 0x13F2 svTsig13f2 = some 0x13FA := by
  simp only [svTsig13f2]
  rw [blockEnd, sv_at_13f2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_13f6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsig13fa : List BInstr :=
  [.aluImm .add a3 x0 0x1, .aluImm .add a4 sp 0x380]
theorem svTsig13fa_end : blockEnd sigstoreVerifyCode 0x13FA svTsig13fa = some 0x13FE := by
  simp only [svTsig13fa]
  rw [blockEnd, sv_at_13fa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_13fc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTsig1406 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x380, .aluImm .add a2 x0 0x2]
theorem svTsig1406_end : blockEnd sigstoreVerifyCode 0x1406 svTsig1406 = some 0x140E := by
  simp only [svTsig1406]
  rw [blockEnd, sv_at_1406]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_140a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_140c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_tsig {B out bp x20 x21 x22 x23 x24 x25 x27 : Word} {tp tl dg w70 w68 w50 w44 q : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x139C (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190)
    (g0_27 : reg n0 (27 : Fin 32) = x27)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg)
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q)
    (w0_174 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl)
    (S2 : SvSha2Code M0)
    (RS : SvRoSep B)
    (tst_in : SvIn B tp tl.toNat)
    (dg_in : SvIn B dg 32)
    (sig_in : SvIn B w70 w68.toNat)
    (dp_in : SvIn B x27 32)
    (sa_in : SvIn B w44 w50.toNat) :
    (¬ ((sha256 (memBytes M0 (tp) (tl).toNat) = memBytes M0 dg 32) ∧ (sha256 (memBytes M0 (w70) (w68).toNat) = memBytes M0 x27 32) ∧ (w50 ≠ 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((sha256 (memBytes M0 (tp) (tl).toNat) = memBytes M0 dg 32) ∧
    (sha256 (memBytes M0 (w70) (w68).toNat) = memBytes M0 x27 32) ∧
    (w50 ≠ 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1416 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 ∧
        reg n' (27 : Fin 32) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = BitVec.ofNat 32 (img% svConstCmsAddress + 0x14) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (w44) + BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (w50) + BitVec.ofNat 32 0xFFFFFFFF ∧
        memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 = sha256 (memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x14)) (1) ++ memBytes M0 ((w44) + BitVec.ofNat 32 0x1) (((w50) + BitVec.ofNat 32 0xFFFFFFFF).toNat)) ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x20), (0x420, 0x20), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x20)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x139C: lw
  obtain ⟨n1, d1, u1⟩ := s0.lw E0.self sv_at_139c (off' := 0x13A0) (by decide)
    (by rw [g0_2, show B + 0x21A0 + 0x174 = B + 0x21A0 + BitVec.ofNat 32 0x174 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s1 : St n1.mem SV n1 0x13A0 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_4]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, upd_ne (by decide) (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = x20 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = x22 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = x23 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = x24 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = x27 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_27]
  have g1_12 : reg n1 a2 = tl := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_2, show B + 0x21A0 + 0x174 = B + 0x21A0 + BitVec.ofNat 32 0x174 by sv_addr, w0_174]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_44 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m1]; exact w0_44
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m1]; exact w0_50
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m1]; exact w0_64
  have w1_68 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m1]; exact w0_68
  have w1_70 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m1]; exact w0_70
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m1]; exact w0_74
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m1]; exact w0_78
  have w1_174 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m1]; exact w0_174
  -- 0x13A0
  obtain ⟨n2, c2, u2⟩ := s1.block svTsig13a0 E1.self svTsig13a0_end
    ⟨trivial, trivial⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have s2 : St n2.mem SV n2 0x13A4 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have rb2 : ∀ q, reg n2 q = (runBlock svTsig13a0 (n1.mem, reg n1)).2 q := fun q => by rw [u2.regs]
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by
    rw [rb2, runBlock_reg _ _ _ sp s1.zero (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb2, runBlock_reg _ _ _ (3 : Fin 32) s1.zero (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb2, runBlock_reg _ _ _ (4 : Fin 32) s1.zero (by decide), g1_4]
  have g2_12 : reg n2 a2 = tl := by
    rw [rb2, runBlock_reg _ _ _ a2 s1.zero (by decide), g1_12]
  have g2_18 : reg n2 (18 : Fin 32) = out := by
    rw [rb2, runBlock_reg _ _ _ (18 : Fin 32) s1.zero (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by
    rw [rb2, runBlock_reg _ _ _ (19 : Fin 32) s1.zero (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by
    rw [rb2, runBlock_reg _ _ _ (20 : Fin 32) s1.zero (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by
    rw [rb2, runBlock_reg _ _ _ (21 : Fin 32) s1.zero (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by
    rw [rb2, runBlock_reg _ _ _ (22 : Fin 32) s1.zero (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by
    rw [rb2, runBlock_reg _ _ _ (23 : Fin 32) s1.zero (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = x24 := by
    rw [rb2, runBlock_reg _ _ _ (24 : Fin 32) s1.zero (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by
    rw [rb2, runBlock_reg _ _ _ (25 : Fin 32) s1.zero (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
    rw [rb2, runBlock_reg _ _ _ (26 : Fin 32) s1.zero (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = x27 := by
    rw [rb2, runBlock_reg _ _ _ (27 : Fin 32) s1.zero (by decide), g1_27]
  have g2_10 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, svTsig13a0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_12, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_24, g1_25, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m2]; exact w1_44
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m2]; exact w1_50
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m2]; exact w1_64
  have w2_68 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m2]; exact w1_68
  have w2_70 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m2]; exact w1_70
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m2]; exact w1_74
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m2]; exact w1_78
  have w2_174 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m2]; exact w1_174
  clear w1_174 w1_78 w1_74 w1_70 w1_68 w1_64 w1_50 w1_44 g1_12 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x13A4: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_13a4 (off' := 0x13A6) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0x13A6 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_10]
  have g3_12 : reg n3 a2 = tl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_12]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = x24 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = x27 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_11 : reg n3 a1 = tp := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr, w2_74]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_44 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m3]; exact w2_44
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m3]; exact w2_50
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m3]; exact w2_64
  have w3_68 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m3]; exact w2_68
  have w3_70 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m3]; exact w2_70
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m3]; exact w2_74
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m3]; exact w2_78
  have w3_174 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m3]; exact w2_174
  clear w2_174 w2_78 w2_74 w2_70 w2_68 w2_64 w2_50 w2_44 g2_10 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_12 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 rb2 s2 m2 u2 c2
  -- 0x13A6: sv_sha256F
  obtain ⟨n4, c4, s4, sp4, rk4, K4, D4, fr4⟩ := sv_sha256F (oc := 0x420) (nl := (tl).toNat)
    FW E3 (S2.sv FW RS fR3) RS s3 sv_at_13a6 sv_at_13aa (by decide) (by decide) g3_2
    g3_10 g3_11 (by rw [g3_12, ofNat_toNat_self]) (by decide) (.inl tst_in) (by have := tst_in.lo; omega)
  have t4 : Steps n0 n4 := t3.trans c4
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.keepL K4 (by decide)
  rw [sv_mbRo FW fR3 (.inl tst_in)] at D4
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk4 (3 : Fin 32) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk4 (4 : Fin 32) (by decide), g3_4]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [rk4 (18 : Fin 32) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [rk4 (19 : Fin 32) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [rk4 (20 : Fin 32) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [rk4 (21 : Fin 32) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [rk4 (22 : Fin 32) (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [rk4 (23 : Fin 32) (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = x24 := by rw [rk4 (24 : Fin 32) (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [rk4 (25 : Fin 32) (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rk4 (26 : Fin 32) (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = x27 := by rw [rk4 (27 : Fin 32) (by decide), g3_27]
  have g4_2 : reg n4 sp = B + 0x21A0 := sp4
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x20)] := keep_kk3.trans K4
  clear keep_kk3
  have w4_44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K4.w32 (by decide) (by decide)).trans w3_44
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K4.w32 (by decide) (by decide)).trans w3_50
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K4.w32 (by decide) (by decide)).trans w3_64
  have w4_68 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K4.w32 (by decide) (by decide)).trans w3_68
  have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K4.w32 (by decide) (by decide)).trans w3_70
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K4.w32 (by decide) (by decide)).trans w3_74
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := (K4.w32 (by decide) (by decide)).trans w3_78
  have w4_174 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := (K4.w32 (by decide) (by decide)).trans w3_174
  clear w3_174 w3_78 w3_74 w3_70 w3_68 w3_64 w3_50 w3_44 g3_11 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_12 g3_10 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x13AE
  obtain ⟨n5, c5, u5⟩ := s4.block svTsig13ae E4.self svTsig13ae_end
    ⟨trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0x13B2 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svTsig13ae (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by
    rw [rb5, runBlock_reg _ _ _ sp s4.zero (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (3 : Fin 32) s4.zero (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (4 : Fin 32) s4.zero (by decide), g4_4]
  have g5_18 : reg n5 (18 : Fin 32) = out := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by
    rw [rb5, runBlock_reg _ _ _ (20 : Fin 32) s4.zero (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by
    rw [rb5, runBlock_reg _ _ _ (22 : Fin 32) s4.zero (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by
    rw [rb5, runBlock_reg _ _ _ (23 : Fin 32) s4.zero (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by
    rw [rb5, runBlock_reg _ _ _ (25 : Fin 32) s4.zero (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = x27 := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svTsig13ae, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x20)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m5]; exact w4_44
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m5]; exact w4_64
  have w5_68 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m5]; exact w4_68
  have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m5]; exact w4_70
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m5]; exact w4_74
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m5]; exact w4_78
  have w5_174 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m5]; exact w4_174
  clear w4_174 w4_78 w4_74 w4_70 w4_68 w4_64 w4_50 w4_44 g4_2 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_4 g4_3 V4 E4 fR4 t4 fr4 K4 rk4 sp4 s4 c4
  have D5 : memBytes n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 = sha256 (memBytes M0 (tp) ((tl).toNat)) := by rw [m5]; exact D4
  -- 0x13B2: lw
  obtain ⟨n6, d6, u6⟩ := s5.lw E5.self sv_at_13b2 (off' := 0x13B4) (by decide)
    (by rw [g5_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s6 : St n6.mem SV n6 0x13B4 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_10]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = x24 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = x27 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_27]
  have g6_11 : reg n6 a1 = dg := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g5_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr, w5_64]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x20)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m6]; exact w5_44
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m6]; exact w5_50
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m6]; exact w5_64
  have w6_68 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m6]; exact w5_68
  have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m6]; exact w5_70
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m6]; exact w5_74
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m6]; exact w5_78
  have w6_174 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m6]; exact w5_174
  clear w5_174 w5_78 w5_74 w5_70 w5_68 w5_64 w5_50 w5_44 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  have D6 : memBytes n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 = sha256 (memBytes M0 (tp) ((tl).toNat)) := by rw [m6]; exact D5
  -- 0x13B4: sv_a32neF
  obtain ⟨n7, c7, s7, sp7, rk7, a0_7, K7, fr7⟩ := sv_a32neF (oc := 0x420)
    F E6 s6 sv_at_13b4 sv_at_13b8 (by decide) (by decide) g6_2
    g6_10 g6_11 (by decide) (.inl dg_in)
  have t7 : Steps n0 n7 := t6.trans c7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.keepL K7 (by decide)
  rw [D6, sv_mbRo FW fR6 (.inl dg_in)] at a0_7
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk7 (3 : Fin 32) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk7 (4 : Fin 32) (by decide), g6_4]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [rk7 (18 : Fin 32) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [rk7 (19 : Fin 32) (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [rk7 (20 : Fin 32) (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [rk7 (21 : Fin 32) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [rk7 (22 : Fin 32) (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [rk7 (23 : Fin 32) (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = x24 := by rw [rk7 (24 : Fin 32) (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [rk7 (25 : Fin 32) (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rk7 (26 : Fin 32) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = x27 := by rw [rk7 (27 : Fin 32) (by decide), g6_27]
  have g7_2 : reg n7 sp = B + 0x21A0 := sp7
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x20)] := keep_kk6.trans K7
  clear keep_kk6
  have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K7.w32 (by decide) (by decide)).trans w6_44
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K7.w32 (by decide) (by decide)).trans w6_50
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K7.w32 (by decide) (by decide)).trans w6_64
  have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K7.w32 (by decide) (by decide)).trans w6_68
  have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K7.w32 (by decide) (by decide)).trans w6_70
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K7.w32 (by decide) (by decide)).trans w6_74
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := (K7.w32 (by decide) (by decide)).trans w6_78
  have w7_174 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := (K7.w32 (by decide) (by decide)).trans w6_174
  clear w6_174 w6_78 w6_74 w6_70 w6_68 w6_64 w6_50 w6_44 g6_11 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  by_cases htd : sha256 (memBytes M0 (tp) (tl).toNat) = memBytes M0 dg 32
  rotate_left
  · have g7_10 : reg n7 a0 = BitVec.ofNat 32 1 := by rw [a0_7, ite_eq_right htd]; rfl
    -- 0x13BC
    obtain ⟨n8, c8, u8⟩ := s7.block svTsig13bc E7.self svTsig13bc_end
      ⟨trivial, trivial⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have s8 : St n8.mem SV n8 0x13BE (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have rb8 : ∀ q, reg n8 q = (runBlock svTsig13bc (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
    have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
    have t8 : Steps n0 n8 := t7.trans c8
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.same m8
    have g8_2 : reg n8 sp = B + 0x21A0 := by
      rw [rb8, runBlock_reg _ _ _ sp s7.zero (by decide), g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb8, runBlock_reg _ _ _ (3 : Fin 32) s7.zero (by decide), g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb8, runBlock_reg _ _ _ (4 : Fin 32) s7.zero (by decide), g7_4]
    have g8_10 : reg n8 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb8, runBlock_reg _ _ _ a0 s7.zero (by decide), g7_10]
    have g8_18 : reg n8 (18 : Fin 32) = out := by
      rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by
      rw [rb8, runBlock_reg _ _ _ (19 : Fin 32) s7.zero (by decide), g7_19]
    have g8_20 : reg n8 (20 : Fin 32) = x20 := by
      rw [rb8, runBlock_reg _ _ _ (20 : Fin 32) s7.zero (by decide), g7_20]
    have g8_21 : reg n8 (21 : Fin 32) = x21 := by
      rw [rb8, runBlock_reg _ _ _ (21 : Fin 32) s7.zero (by decide), g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = x22 := by
      rw [rb8, runBlock_reg _ _ _ (22 : Fin 32) s7.zero (by decide), g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = x23 := by
      rw [rb8, runBlock_reg _ _ _ (23 : Fin 32) s7.zero (by decide), g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = x24 := by
      rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = x25 := by
      rw [rb8, runBlock_reg _ _ _ (25 : Fin 32) s7.zero (by decide), g7_25]
    have g8_26 : reg n8 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
      rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = x27 := by
      rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
    have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by
      rw [rb8]; simp +decide only [runBlock, BInstr.run, svTsig13bc, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g7_2, g7_3, g7_4, g7_10, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x20)] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m8]; exact w7_44
    have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
    have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m8]; exact w7_64
    have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m8]; exact w7_68
    have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m8]; exact w7_70
    have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m8]; exact w7_74
    have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m8]; exact w7_78
    have w8_174 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m8]; exact w7_174
    clear w7_174 w7_78 w7_74 w7_70 w7_68 w7_64 w7_50 w7_44 g7_2 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_4 g7_3 V7 E7 fR7 t7 fr7 K7 a0_7 rk7 sp7 s7 c7
    -- 0x13BE: branch, taken
    obtain ⟨n9, d9, u9⟩ := s8.taken E8.self 0x7A4 sv_at_13be
      (by decide) (by rw [g8_10, s8.zero]; decide)
    have s9 : St n9.mem SV n9 0x7A4 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
    have t9 : Steps n0 n9 := t8.trans (.single d9)
    have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.same m9
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, g8_4]
    have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [u9.regs, g8_8]
    have g9_10 : reg n9 a0 = BitVec.ofNat 32 0x1 := by rw [u9.regs, g8_10]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = x24 := by rw [u9.regs, g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [u9.regs, g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u9.regs, g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = x27 := by rw [u9.regs, g8_27]
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x20)] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m9]; exact w8_44
    have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
    have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m9]; exact w8_64
    have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m9]; exact w8_68
    have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m9]; exact w8_70
    have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m9]; exact w8_74
    have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m9]; exact w8_78
    have w9_174 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m9]; exact w8_174
    clear w8_174 w8_78 w8_74 w8_70 w8_68 w8_64 w8_50 w8_44 g8_8 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8 g7_10
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact htd h0'), sv_fail F E9 s9 t9 (fun x hx => (fR9 x hx).trans (fM x hx).symm) V9 hret g9_2 g9_18 hO g9_3 g9_4⟩
  have g7_10 : reg n7 a0 = BitVec.ofNat 32 0 := by rw [a0_7, ite_eq_left htd]; rfl
  -- 0x13BC
  obtain ⟨n8, c8, u8⟩ := s7.block svTsig13bc E7.self svTsig13bc_end
    ⟨trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem SV n8 0x13BE (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock svTsig13bc (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans c8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by
    rw [rb8, runBlock_reg _ _ _ sp s7.zero (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb8, runBlock_reg _ _ _ (3 : Fin 32) s7.zero (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb8, runBlock_reg _ _ _ (4 : Fin 32) s7.zero (by decide), g7_4]
  have g8_10 : reg n8 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb8, runBlock_reg _ _ _ a0 s7.zero (by decide), g7_10]
  have g8_18 : reg n8 (18 : Fin 32) = out := by
    rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by
    rw [rb8, runBlock_reg _ _ _ (19 : Fin 32) s7.zero (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by
    rw [rb8, runBlock_reg _ _ _ (20 : Fin 32) s7.zero (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by
    rw [rb8, runBlock_reg _ _ _ (21 : Fin 32) s7.zero (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by
    rw [rb8, runBlock_reg _ _ _ (22 : Fin 32) s7.zero (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by
    rw [rb8, runBlock_reg _ _ _ (23 : Fin 32) s7.zero (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = x24 := by
    rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by
    rw [rb8, runBlock_reg _ _ _ (25 : Fin 32) s7.zero (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
    rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = x27 := by
    rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
  have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svTsig13bc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_10, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x20)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m8]; exact w7_44
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m8]; exact w7_64
  have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m8]; exact w7_68
  have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m8]; exact w7_70
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m8]; exact w7_74
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m8]; exact w7_78
  have w8_174 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m8]; exact w7_174
  clear w7_174 w7_78 w7_74 w7_70 w7_68 w7_64 w7_50 w7_44 g7_2 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_4 g7_3 V7 E7 fR7 t7 fr7 K7 a0_7 rk7 sp7 s7 c7
  -- 0x13BE: branch, not taken
  obtain ⟨n9, d9, u9⟩ := s8.notTaken E8.self 0x13C2 sv_at_13be
    (by decide) (by rw [g8_10, s8.zero]; decide)
  have s9 : St n9.mem SV n9 0x13C2 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans (.single d9)
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [u9.regs, g8_8]
  have g9_10 : reg n9 a0 = BitVec.ofNat 32 0x0 := by rw [u9.regs, g8_10]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = x24 := by rw [u9.regs, g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [u9.regs, g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u9.regs, g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = x27 := by rw [u9.regs, g8_27]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x20)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m9]; exact w8_44
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m9]; exact w8_64
  have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m9]; exact w8_68
  have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m9]; exact w8_70
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m9]; exact w8_74
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m9]; exact w8_78
  have w9_174 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m9]; exact w8_174
  clear w8_174 w8_78 w8_74 w8_70 w8_68 w8_64 w8_50 w8_44 g8_8 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8 g7_10
  -- 0x13C2
  obtain ⟨n10, c10, u10⟩ := s9.block svTsig13c2 E9.self svTsig13c2_end
    ⟨trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0x13C6 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svTsig13c2 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans c10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by
    rw [rb10, runBlock_reg _ _ _ sp s9.zero (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb10, runBlock_reg _ _ _ (3 : Fin 32) s9.zero (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb10, runBlock_reg _ _ _ (4 : Fin 32) s9.zero (by decide), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by
    rw [rb10, runBlock_reg _ _ _ (8 : Fin 32) s9.zero (by decide), g9_8]
  have g10_18 : reg n10 (18 : Fin 32) = out := by
    rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by
    rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by
    rw [rb10, runBlock_reg _ _ _ (20 : Fin 32) s9.zero (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by
    rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by
    rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by
    rw [rb10, runBlock_reg _ _ _ (23 : Fin 32) s9.zero (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = x24 := by
    rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by
    rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = x27 := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svTsig13c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x20)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m10]; exact w9_44
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m10]; exact w9_50
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m10]; exact w9_64
  have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m10]; exact w9_68
  have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m10]; exact w9_70
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m10]; exact w9_74
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m10]; exact w9_78
  have w10_174 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m10]; exact w9_174
  clear w9_174 w9_78 w9_74 w9_70 w9_68 w9_64 w9_50 w9_44 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  -- 0x13C6: lw
  obtain ⟨n11, d11, u11⟩ := s10.lw E10.self sv_at_13c6 (off' := 0x13C8) (by decide)
    (by rw [g10_2, show B + 0x21A0 + 0x70 = B + 0x21A0 + BitVec.ofNat 32 0x70 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s11 : St n11.mem SV n11 0x13C8 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [u11.regs, upd_ne (by decide) (by decide), g10_8]
  have g11_10 : reg n11 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
  have g11_11 : reg n11 a1 = w70 := by
    rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g10_2, show B + 0x21A0 + 0x70 = B + 0x21A0 + BitVec.ofNat 32 0x70 by sv_addr, w10_70]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x20)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m11]; exact w10_44
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m11]; exact w10_64
  have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m11]; exact w10_68
  have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m11]; exact w10_70
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m11]; exact w10_74
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m11]; exact w10_78
  have w11_174 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m11]; exact w10_174
  clear w10_174 w10_78 w10_74 w10_70 w10_68 w10_64 w10_50 w10_44 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0x13C8: lw
  obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_13c8 (off' := 0x13CA) (by decide)
    (by rw [g11_2, show B + 0x21A0 + 0x68 = B + 0x21A0 + BitVec.ofNat 32 0x68 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s12 : St n12.mem SV n12 0x13CA (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [u12.regs, upd_ne (by decide) (by decide), g11_8]
  have g12_10 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_10]
  have g12_11 : reg n12 a1 = w70 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_11]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = x24 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = x27 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
  have g12_12 : reg n12 a2 = w68 := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_2, show B + 0x21A0 + 0x68 = B + 0x21A0 + BitVec.ofNat 32 0x68 by sv_addr, w11_68]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x20)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m12]; exact w11_44
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m12]; exact w11_64
  have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m12]; exact w11_68
  have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m12]; exact w11_70
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m12]; exact w11_74
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m12]; exact w11_78
  have w12_174 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m12]; exact w11_174
  clear w11_174 w11_78 w11_74 w11_70 w11_68 w11_64 w11_50 w11_44 g11_11 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0x13CA: sv_sha256F
  obtain ⟨n13, c13, s13, sp13, rk13, K13, D13, fr13⟩ := sv_sha256F (oc := 0x420) (nl := (w68).toNat)
    FW E12 (S2.sv FW RS fR12) RS s12 sv_at_13ca sv_at_13ce (by decide) (by decide) g12_2
    g12_10 g12_11 (by rw [g12_12, ofNat_toNat_self]) (by decide) (.inl sig_in) (by have := sig_in.lo; omega)
  have t13 : Steps n0 n13 := t12.trans c13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keepL K13 (by decide)
  rw [sv_mbRo FW fR12 (.inl sig_in)] at D13
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk13 (3 : Fin 32) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk13 (4 : Fin 32) (by decide), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [rk13 (8 : Fin 32) (by decide), g12_8]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rk13 (18 : Fin 32) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rk13 (19 : Fin 32) (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [rk13 (20 : Fin 32) (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [rk13 (21 : Fin 32) (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [rk13 (22 : Fin 32) (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [rk13 (23 : Fin 32) (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [rk13 (24 : Fin 32) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [rk13 (25 : Fin 32) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rk13 (26 : Fin 32) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [rk13 (27 : Fin 32) (by decide), g12_27]
  have g13_2 : reg n13 sp = B + 0x21A0 := sp13
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x20), (0x420, 0x20)] := keep_kk12.trans K13
  clear keep_kk12
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K13.w32 (by decide) (by decide)).trans w12_44
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K13.w32 (by decide) (by decide)).trans w12_50
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K13.w32 (by decide) (by decide)).trans w12_64
  have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K13.w32 (by decide) (by decide)).trans w12_68
  have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K13.w32 (by decide) (by decide)).trans w12_70
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K13.w32 (by decide) (by decide)).trans w12_74
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := (K13.w32 (by decide) (by decide)).trans w12_78
  have w13_174 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := (K13.w32 (by decide) (by decide)).trans w12_174
  clear w12_174 w12_78 w12_74 w12_70 w12_68 w12_64 w12_50 w12_44 g12_12 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_11 g12_10 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0x13D2
  obtain ⟨n14, c14, u14⟩ := s13.block svTsig13d2 E13.self svTsig13d2_end
    ⟨trivial, trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem SV n14 0x13D8 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock svTsig13d2 (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans c14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by
    rw [rb14, runBlock_reg _ _ _ sp s13.zero (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb14, runBlock_reg _ _ _ (3 : Fin 32) s13.zero (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb14, runBlock_reg _ _ _ (4 : Fin 32) s13.zero (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by
    rw [rb14, runBlock_reg _ _ _ (8 : Fin 32) s13.zero (by decide), g13_8]
  have g14_18 : reg n14 (18 : Fin 32) = out := by
    rw [rb14, runBlock_reg _ _ _ (18 : Fin 32) s13.zero (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by
    rw [rb14, runBlock_reg _ _ _ (19 : Fin 32) s13.zero (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by
    rw [rb14, runBlock_reg _ _ _ (20 : Fin 32) s13.zero (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by
    rw [rb14, runBlock_reg _ _ _ (21 : Fin 32) s13.zero (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by
    rw [rb14, runBlock_reg _ _ _ (22 : Fin 32) s13.zero (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by
    rw [rb14, runBlock_reg _ _ _ (23 : Fin 32) s13.zero (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = x24 := by
    rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by
    rw [rb14, runBlock_reg _ _ _ (25 : Fin 32) s13.zero (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
    rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = x27 := by
    rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
  have g14_10 : reg n14 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svTsig13d2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g14_11 : reg n14 a1 = x27 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svTsig13d2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x20), (0x420, 0x20)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m14]; exact w13_44
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m14]; exact w13_50
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m14]; exact w13_64
  have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m14]; exact w13_68
  have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m14]; exact w13_70
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m14]; exact w13_74
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m14]; exact w13_78
  have w14_174 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m14]; exact w13_174
  clear w13_174 w13_78 w13_74 w13_70 w13_68 w13_64 w13_50 w13_44 g13_2 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_8 g13_4 g13_3 V13 E13 fR13 t13 fr13 K13 rk13 sp13 s13 c13
  have D14 : memBytes n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 = sha256 (memBytes M0 (w70) ((w68).toNat)) := by rw [m14]; exact D13
  -- 0x13D8: sv_a32neF
  obtain ⟨n15, c15, s15, sp15, rk15, a0_15, K15, fr15⟩ := sv_a32neF (oc := 0x420)
    F E14 s14 sv_at_13d8 sv_at_13dc (by decide) (by decide) g14_2
    g14_10 g14_11 (by decide) (.inl dp_in)
  have t15 : Steps n0 n15 := t14.trans c15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keepL K15 (by decide)
  rw [D14, sv_mbRo FW fR14 (.inl dp_in)] at a0_15
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk15 (3 : Fin 32) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk15 (4 : Fin 32) (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [rk15 (8 : Fin 32) (by decide), g14_8]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rk15 (18 : Fin 32) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rk15 (19 : Fin 32) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [rk15 (20 : Fin 32) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [rk15 (21 : Fin 32) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [rk15 (22 : Fin 32) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [rk15 (23 : Fin 32) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [rk15 (24 : Fin 32) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [rk15 (25 : Fin 32) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rk15 (26 : Fin 32) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [rk15 (27 : Fin 32) (by decide), g14_27]
  have g15_2 : reg n15 sp = B + 0x21A0 := sp15
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x20), (0x420, 0x20)] := keep_kk14.trans K15
  clear keep_kk14
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K15.w32 (by decide) (by decide)).trans w14_44
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K15.w32 (by decide) (by decide)).trans w14_50
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K15.w32 (by decide) (by decide)).trans w14_64
  have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K15.w32 (by decide) (by decide)).trans w14_68
  have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K15.w32 (by decide) (by decide)).trans w14_70
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K15.w32 (by decide) (by decide)).trans w14_74
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := (K15.w32 (by decide) (by decide)).trans w14_78
  have w15_174 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := (K15.w32 (by decide) (by decide)).trans w14_174
  clear w14_174 w14_78 w14_74 w14_70 w14_68 w14_64 w14_50 w14_44 g14_11 g14_10 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  by_cases him : sha256 (memBytes M0 (w70) (w68).toNat) = memBytes M0 x27 32
  rotate_left
  · have g15_10 : reg n15 a0 = BitVec.ofNat 32 1 := by rw [a0_15, ite_eq_right him]; rfl
    -- 0x13E0: branch, taken
    obtain ⟨n16, d16, u16⟩ := s15.taken E15.self 0x7A4 sv_at_13e0
      (by decide) (by rw [g15_10, s15.zero]; decide)
    have s16 : St n16.mem SV n16 0x7A4 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans (.single d16)
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, g15_4]
    have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [u16.regs, g15_8]
    have g16_10 : reg n16 a0 = BitVec.ofNat 32 0x1 := by rw [u16.regs, g15_10]
    have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [u16.regs, g15_20]
    have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = x24 := by rw [u16.regs, g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u16.regs, g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = x27 := by rw [u16.regs, g15_27]
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x20), (0x420, 0x20)] := by rw [m16]; exact keep_kk15
    clear keep_kk15
    have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m16]; exact w15_44
    have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m16]; exact w15_50
    have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m16]; exact w15_64
    have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m16]; exact w15_68
    have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m16]; exact w15_70
    have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m16]; exact w15_74
    have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m16]; exact w15_78
    have w16_174 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m16]; exact w15_174
    clear w15_174 w15_78 w15_74 w15_70 w15_68 w15_64 w15_50 w15_44 g15_2 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_8 g15_4 g15_3 V15 E15 fR15 t15 fr15 K15 a0_15 rk15 sp15 s15 c15
    exact .inl ⟨(fun ⟨h0', h1', _⟩ => by exact him h1'), sv_fail F E16 s16 t16 (fun x hx => (fR16 x hx).trans (fM x hx).symm) V16 hret g16_2 g16_18 hO g16_3 g16_4⟩
  have g15_10 : reg n15 a0 = BitVec.ofNat 32 0 := by rw [a0_15, ite_eq_left him]; rfl
  -- 0x13E0: branch, not taken
  obtain ⟨n16, d16, u16⟩ := s15.notTaken E15.self 0x13E4 sv_at_13e0
    (by decide) (by rw [g15_10, s15.zero]; decide)
  have s16 : St n16.mem SV n16 0x13E4 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [u16.regs, g15_8]
  have g16_10 : reg n16 a0 = BitVec.ofNat 32 0x0 := by rw [u16.regs, g15_10]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [u16.regs, g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = x24 := by rw [u16.regs, g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u16.regs, g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = x27 := by rw [u16.regs, g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x20), (0x420, 0x20)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m16]; exact w15_44
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m16]; exact w15_50
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m16]; exact w15_64
  have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m16]; exact w15_68
  have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m16]; exact w15_70
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m16]; exact w15_74
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m16]; exact w15_78
  have w16_174 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m16]; exact w15_174
  clear w15_174 w15_78 w15_74 w15_70 w15_68 w15_64 w15_50 w15_44 g15_2 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_8 g15_4 g15_3 V15 E15 fR15 t15 fr15 K15 a0_15 rk15 sp15 s15 c15
  -- 0x13E4: lw
  obtain ⟨n17, d17, u17⟩ := s16.lw E16.self sv_at_13e4 (off' := 0x13E6) (by decide)
    (by rw [g16_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s17 : St n17.mem SV n17 0x13E6 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans (.single d17)
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [u17.regs, upd_ne (by decide) (by decide), g16_8]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, upd_ne (by decide) (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = x24 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = x27 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_27]
  have g17_10 : reg n17 a0 = w50 := by
    rw [u17.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g16_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w16_50]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x20), (0x420, 0x20)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m17]; exact w16_44
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m17]; exact w16_50
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m17]; exact w16_64
  have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m17]; exact w16_68
  have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m17]; exact w16_70
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m17]; exact w16_74
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m17]; exact w16_78
  have w17_174 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m17]; exact w16_174
  clear w16_174 w16_78 w16_74 w16_70 w16_68 w16_64 w16_50 w16_44 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_10 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16 g15_10
  by_cases hsa : w50 ≠ 0
  rotate_left
  · -- 0x13E6: branch, taken
    obtain ⟨n18, d18, u18⟩ := s17.taken E17.self 0x1552 sv_at_13e6
      (by decide) (by rw [g17_10, s17.zero]; exact br_beq_t (Decidable.of_not_not hsa))
    have s18 : St n18.mem SV n18 0x1552 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
    have m18 : n18.mem = n17.mem := u18.mem
    have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
    have t18 : Steps n0 n18 := t17.trans (.single d18)
    have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
    have E18 : SvCode n18.mem := E17.fr F fr18
    have V18 : SvSaves B n18.mem v := V17.same m18
    have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
    have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
    have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
    have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [u18.regs, g17_8]
    have g18_10 : reg n18 a0 = w50 := by rw [u18.regs, g17_10]
    have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
    have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
    have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [u18.regs, g17_20]
    have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, g17_21]
    have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [u18.regs, g17_22]
    have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [u18.regs, g17_23]
    have g18_24 : reg n18 (24 : Fin 32) = x24 := by rw [u18.regs, g17_24]
    have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, g17_25]
    have g18_26 : reg n18 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u18.regs, g17_26]
    have g18_27 : reg n18 (27 : Fin 32) = x27 := by rw [u18.regs, g17_27]
    have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x420, 0x20), (0x420, 0x20)] := by rw [m18]; exact keep_kk17
    clear keep_kk17
    have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m18]; exact w17_44
    have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m18]; exact w17_50
    have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m18]; exact w17_64
    have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m18]; exact w17_68
    have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m18]; exact w17_70
    have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m18]; exact w17_74
    have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m18]; exact w17_78
    have w18_174 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m18]; exact w17_174
    clear w17_174 w17_78 w17_74 w17_70 w17_68 w17_64 w17_50 w17_44 g17_10 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
    -- 0x1552
    obtain ⟨n19, c19, u19⟩ := s18.block svTsig1552 E18.self svTsig1552_end
      ⟨trivial, trivial⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have s19 : St n19.mem SV n19 0x1554 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have rb19 : ∀ q, reg n19 q = (runBlock svTsig1552 (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans c19
    have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by
      rw [rb19, runBlock_reg _ _ _ sp s18.zero (by decide), g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb19, runBlock_reg _ _ _ (3 : Fin 32) s18.zero (by decide), g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb19, runBlock_reg _ _ _ (4 : Fin 32) s18.zero (by decide), g18_4]
    have g19_10 : reg n19 a0 = w50 := by
      rw [rb19, runBlock_reg _ _ _ a0 s18.zero (by decide), g18_10]
    have g19_18 : reg n19 (18 : Fin 32) = out := by
      rw [rb19, runBlock_reg _ _ _ (18 : Fin 32) s18.zero (by decide), g18_18]
    have g19_19 : reg n19 (19 : Fin 32) = bp := by
      rw [rb19, runBlock_reg _ _ _ (19 : Fin 32) s18.zero (by decide), g18_19]
    have g19_20 : reg n19 (20 : Fin 32) = x20 := by
      rw [rb19, runBlock_reg _ _ _ (20 : Fin 32) s18.zero (by decide), g18_20]
    have g19_21 : reg n19 (21 : Fin 32) = x21 := by
      rw [rb19, runBlock_reg _ _ _ (21 : Fin 32) s18.zero (by decide), g18_21]
    have g19_22 : reg n19 (22 : Fin 32) = x22 := by
      rw [rb19, runBlock_reg _ _ _ (22 : Fin 32) s18.zero (by decide), g18_22]
    have g19_23 : reg n19 (23 : Fin 32) = x23 := by
      rw [rb19, runBlock_reg _ _ _ (23 : Fin 32) s18.zero (by decide), g18_23]
    have g19_24 : reg n19 (24 : Fin 32) = x24 := by
      rw [rb19, runBlock_reg _ _ _ (24 : Fin 32) s18.zero (by decide), g18_24]
    have g19_25 : reg n19 (25 : Fin 32) = x25 := by
      rw [rb19, runBlock_reg _ _ _ (25 : Fin 32) s18.zero (by decide), g18_25]
    have g19_26 : reg n19 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
      rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
    have g19_27 : reg n19 (27 : Fin 32) = x27 := by
      rw [rb19, runBlock_reg _ _ _ (27 : Fin 32) s18.zero (by decide), g18_27]
    have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb19]; simp +decide only [runBlock, BInstr.run, svTsig1552, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_10, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x420, 0x20), (0x420, 0x20)] := by rw [m19]; exact keep_kk18
    clear keep_kk18
    have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m19]; exact w18_44
    have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m19]; exact w18_50
    have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m19]; exact w18_64
    have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m19]; exact w18_68
    have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m19]; exact w18_70
    have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m19]; exact w18_74
    have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m19]; exact w18_78
    have w19_174 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m19]; exact w18_174
    clear w18_174 w18_78 w18_74 w18_70 w18_68 w18_64 w18_50 w18_44 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_10 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
    -- 0x1554: j
    obtain ⟨n20, d20, u20⟩ := s19.jump E19.self sv_at_1554 (off' := 0x7A4) (by decide)
      (by rw [s19.pc]; decide)
    have s20 : St n20.mem SV n20 0x7A4 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
    have t20 : Steps n0 n20 := t19.trans (.single d20)
    have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
    have E20 : SvCode n20.mem := E19.fr F fr20
    have V20 : SvSaves B n20.mem v := V19.same m20
    have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, g19_2]
    have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, g19_3]
    have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, g19_4]
    have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u20.regs, g19_8]
    have g20_10 : reg n20 a0 = w50 := by rw [u20.regs, g19_10]
    have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, g19_19]
    have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [u20.regs, g19_20]
    have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [u20.regs, g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [u20.regs, g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [u20.regs, g19_23]
    have g20_24 : reg n20 (24 : Fin 32) = x24 := by rw [u20.regs, g19_24]
    have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [u20.regs, g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u20.regs, g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = x27 := by rw [u20.regs, g19_27]
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x420, 0x20), (0x420, 0x20)] := by rw [m20]; exact keep_kk19
    clear keep_kk19
    have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m20]; exact w19_44
    have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m20]; exact w19_50
    have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m20]; exact w19_64
    have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m20]; exact w19_68
    have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m20]; exact w19_70
    have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m20]; exact w19_74
    have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m20]; exact w19_78
    have w20_174 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m20]; exact w19_174
    clear w19_174 w19_78 w19_74 w19_70 w19_68 w19_64 w19_50 w19_44 g19_8 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_10 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
    exact .inl ⟨(fun ⟨h0', h1', h2', _⟩ => by exact hsa h2'), sv_fail F E20 s20 t20 (fun x hx => (fR20 x hx).trans (fM x hx).symm) V20 hret g20_2 g20_18 hO g20_3 g20_4⟩
  -- 0x13E6: branch, not taken
  obtain ⟨n18, d18, u18⟩ := s17.notTaken E17.self 0x13EA sv_at_13e6
    (by decide) (by rw [g17_10, s17.zero]; exact br_beq_f hsa)
  have s18 : St n18.mem SV n18 0x13EA (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [u18.regs, g17_8]
  have g18_10 : reg n18 a0 = w50 := by rw [u18.regs, g17_10]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [u18.regs, g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [u18.regs, g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [u18.regs, g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = x24 := by rw [u18.regs, g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u18.regs, g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = x27 := by rw [u18.regs, g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x420, 0x20), (0x420, 0x20)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m18]; exact w17_44
  have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m18]; exact w17_50
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m18]; exact w17_64
  have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m18]; exact w17_68
  have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m18]; exact w17_70
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m18]; exact w17_74
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m18]; exact w17_78
  have w18_174 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m18]; exact w17_174
  clear w17_174 w17_78 w17_74 w17_70 w17_68 w17_64 w17_50 w17_44 g17_10 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
  -- 0x13EA: lw
  obtain ⟨n19, d19, u19⟩ := s18.lw E18.self sv_at_13ea (off' := 0x13EC) (by decide)
    (by rw [g18_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s19 : St n19.mem SV n19 0x13EC (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [u19.regs, upd_ne (by decide) (by decide), g18_8]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = x24 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
  have g19_10 : reg n19 a0 = w44 := by
    rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g18_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w18_44]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x420, 0x20), (0x420, 0x20)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m19]; exact w18_44
  have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m19]; exact w18_50
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m19]; exact w18_64
  have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m19]; exact w18_68
  have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m19]; exact w18_70
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m19]; exact w18_74
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m19]; exact w18_78
  have w19_174 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m19]; exact w18_174
  clear w18_174 w18_78 w18_74 w18_70 w18_68 w18_64 w18_50 w18_44 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_10 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  -- 0x13EC
  obtain ⟨n20, c20, u20⟩ := s19.block svTsig13ec E19.self svTsig13ec_end
    ⟨trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0x13EE (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svTsig13ec (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans c20
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by
    rw [rb20, runBlock_reg _ _ _ sp s19.zero (by decide), g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb20, runBlock_reg _ _ _ (3 : Fin 32) s19.zero (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb20, runBlock_reg _ _ _ (4 : Fin 32) s19.zero (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
  have g20_18 : reg n20 (18 : Fin 32) = out := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by
    rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = x20 := by
    rw [rb20, runBlock_reg _ _ _ (20 : Fin 32) s19.zero (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by
    rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = x22 := by
    rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = x23 := by
    rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = x24 := by
    rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by
    rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = x27 := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_10 : reg n20 a0 = (w44) + BitVec.ofNat 32 0x1 := by
    rw [rb20, ← g19_10]; rfl
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x420, 0x20), (0x420, 0x20)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m20]; exact w19_44
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m20]; exact w19_50
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m20]; exact w19_64
  have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m20]; exact w19_68
  have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m20]; exact w19_70
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m20]; exact w19_74
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m20]; exact w19_78
  have w20_174 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m20]; exact w19_174
  clear w19_174 w19_78 w19_74 w19_70 w19_68 w19_64 w19_50 w19_44 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0x13EE: lw
  obtain ⟨n21, d21, u21⟩ := s20.lw E20.self sv_at_13ee (off' := 0x13F0) (by decide)
    (by rw [g20_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s21 : St n21.mem SV n21 0x13F0 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [u21.regs, upd_ne (by decide) (by decide), g20_8]
  have g21_10 : reg n21 a0 = (w44) + BitVec.ofNat 32 0x1 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_10]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = x24 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
  have g21_11 : reg n21 a1 = w50 := by
    rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g20_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w20_50]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x420, 0x20), (0x420, 0x20)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m21]; exact w20_44
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m21]; exact w20_50
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m21]; exact w20_64
  have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m21]; exact w20_68
  have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m21]; exact w20_70
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m21]; exact w20_74
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m21]; exact w20_78
  have w21_174 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m21]; exact w20_174
  clear w20_174 w20_78 w20_74 w20_70 w20_68 w20_64 w20_50 w20_44 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0x13F0
  obtain ⟨n22, c22, u22⟩ := s21.block svTsig13f0 E21.self svTsig13f0_end
    ⟨trivial, trivial⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have s22 : St n22.mem SV n22 0x13F2 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have rb22 : ∀ q, reg n22 q = (runBlock svTsig13f0 (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans c22
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by
    rw [rb22, runBlock_reg _ _ _ sp s21.zero (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb22, runBlock_reg _ _ _ (3 : Fin 32) s21.zero (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb22, runBlock_reg _ _ _ (4 : Fin 32) s21.zero (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by
    rw [rb22, runBlock_reg _ _ _ (8 : Fin 32) s21.zero (by decide), g21_8]
  have g22_10 : reg n22 a0 = (w44) + BitVec.ofNat 32 0x1 := by
    rw [rb22, runBlock_reg _ _ _ a0 s21.zero (by decide), g21_10]
  have g22_18 : reg n22 (18 : Fin 32) = out := by
    rw [rb22, runBlock_reg _ _ _ (18 : Fin 32) s21.zero (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by
    rw [rb22, runBlock_reg _ _ _ (19 : Fin 32) s21.zero (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = x20 := by
    rw [rb22, runBlock_reg _ _ _ (20 : Fin 32) s21.zero (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by
    rw [rb22, runBlock_reg _ _ _ (21 : Fin 32) s21.zero (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = x22 := by
    rw [rb22, runBlock_reg _ _ _ (22 : Fin 32) s21.zero (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = x23 := by
    rw [rb22, runBlock_reg _ _ _ (23 : Fin 32) s21.zero (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = x24 := by
    rw [rb22, runBlock_reg _ _ _ (24 : Fin 32) s21.zero (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by
    rw [rb22, runBlock_reg _ _ _ (25 : Fin 32) s21.zero (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
    rw [rb22, runBlock_reg _ _ _ (26 : Fin 32) s21.zero (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = x27 := by
    rw [rb22, runBlock_reg _ _ _ (27 : Fin 32) s21.zero (by decide), g21_27]
  have g22_11 : reg n22 a1 = (w50) + BitVec.ofNat 32 0xFFFFFFFF := by
    rw [rb22, ← g21_11]; rfl
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x420, 0x20), (0x420, 0x20)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m22]; exact w21_44
  have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m22]; exact w21_50
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m22]; exact w21_64
  have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m22]; exact w21_68
  have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m22]; exact w21_70
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m22]; exact w21_74
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m22]; exact w21_78
  have w22_174 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m22]; exact w21_174
  clear w21_174 w21_78 w21_74 w21_70 w21_68 w21_64 w21_50 w21_44 g21_11 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_10 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
  -- 0x13F2
  obtain ⟨n23, c23, u23⟩ := s22.block svTsig13f2 E22.self svTsig13f2_end
    ⟨trivial, trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0x13FA (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svTsig13f2 (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans c23
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by
    rw [rb23, runBlock_reg _ _ _ sp s22.zero (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb23, runBlock_reg _ _ _ (3 : Fin 32) s22.zero (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb23, runBlock_reg _ _ _ (4 : Fin 32) s22.zero (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by
    rw [rb23, runBlock_reg _ _ _ (8 : Fin 32) s22.zero (by decide), g22_8]
  have g23_10 : reg n23 a0 = (w44) + BitVec.ofNat 32 0x1 := by
    rw [rb23, runBlock_reg _ _ _ a0 s22.zero (by decide), g22_10]
  have g23_11 : reg n23 a1 = (w50) + BitVec.ofNat 32 0xFFFFFFFF := by
    rw [rb23, runBlock_reg _ _ _ a1 s22.zero (by decide), g22_11]
  have g23_18 : reg n23 (18 : Fin 32) = out := by
    rw [rb23, runBlock_reg _ _ _ (18 : Fin 32) s22.zero (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by
    rw [rb23, runBlock_reg _ _ _ (19 : Fin 32) s22.zero (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = x20 := by
    rw [rb23, runBlock_reg _ _ _ (20 : Fin 32) s22.zero (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by
    rw [rb23, runBlock_reg _ _ _ (21 : Fin 32) s22.zero (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by
    rw [rb23, runBlock_reg _ _ _ (22 : Fin 32) s22.zero (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by
    rw [rb23, runBlock_reg _ _ _ (23 : Fin 32) s22.zero (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = x24 := by
    rw [rb23, runBlock_reg _ _ _ (24 : Fin 32) s22.zero (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by
    rw [rb23, runBlock_reg _ _ _ (25 : Fin 32) s22.zero (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = x27 := by
    rw [rb23, runBlock_reg _ _ _ (27 : Fin 32) s22.zero (by decide), g22_27]
  have g23_12 : reg n23 a2 = BitVec.ofNat 32 (img% svConstCmsAddress + 0x14) := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svTsig13f2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_10, g22_11, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x420, 0x20), (0x420, 0x20)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m23]; exact w22_44
  have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m23]; exact w22_50
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m23]; exact w22_64
  have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m23]; exact w22_68
  have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m23]; exact w22_70
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m23]; exact w22_74
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m23]; exact w22_78
  have w23_174 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m23]; exact w22_174
  clear w22_174 w22_78 w22_74 w22_70 w22_68 w22_64 w22_50 w22_44 g22_11 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_10 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22
  -- 0x13FA
  obtain ⟨n24, c24, u24⟩ := s23.block svTsig13fa E23.self svTsig13fa_end
    ⟨trivial, trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem SV n24 0x13FE (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock svTsig13fa (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans c24
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by
    rw [rb24, runBlock_reg _ _ _ sp s23.zero (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb24, runBlock_reg _ _ _ (3 : Fin 32) s23.zero (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb24, runBlock_reg _ _ _ (4 : Fin 32) s23.zero (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by
    rw [rb24, runBlock_reg _ _ _ (8 : Fin 32) s23.zero (by decide), g23_8]
  have g24_10 : reg n24 a0 = (w44) + BitVec.ofNat 32 0x1 := by
    rw [rb24, runBlock_reg _ _ _ a0 s23.zero (by decide), g23_10]
  have g24_11 : reg n24 a1 = (w50) + BitVec.ofNat 32 0xFFFFFFFF := by
    rw [rb24, runBlock_reg _ _ _ a1 s23.zero (by decide), g23_11]
  have g24_12 : reg n24 a2 = BitVec.ofNat 32 (img% svConstCmsAddress + 0x14) := by
    rw [rb24, runBlock_reg _ _ _ a2 s23.zero (by decide), g23_12]
  have g24_18 : reg n24 (18 : Fin 32) = out := by
    rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by
    rw [rb24, runBlock_reg _ _ _ (19 : Fin 32) s23.zero (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = x20 := by
    rw [rb24, runBlock_reg _ _ _ (20 : Fin 32) s23.zero (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by
    rw [rb24, runBlock_reg _ _ _ (21 : Fin 32) s23.zero (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = x22 := by
    rw [rb24, runBlock_reg _ _ _ (22 : Fin 32) s23.zero (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = x23 := by
    rw [rb24, runBlock_reg _ _ _ (23 : Fin 32) s23.zero (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = x24 := by
    rw [rb24, runBlock_reg _ _ _ (24 : Fin 32) s23.zero (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by
    rw [rb24, runBlock_reg _ _ _ (25 : Fin 32) s23.zero (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
    rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = x27 := by
    rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
  have g24_13 : reg n24 a3 = BitVec.ofNat 32 0x1 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svTsig13fa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_10, g23_11, g23_12, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g24_14 : reg n24 a4 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svTsig13fa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_10, g23_11, g23_12, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x420, 0x20), (0x420, 0x20)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m24]; exact w23_44
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m24]; exact w23_50
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m24]; exact w23_64
  have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m24]; exact w23_68
  have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m24]; exact w23_70
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m24]; exact w23_74
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m24]; exact w23_78
  have w24_174 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m24]; exact w23_174
  clear w23_174 w23_78 w23_74 w23_70 w23_68 w23_64 w23_50 w23_44 g23_12 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_11 g23_10 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0x13FE: sw
  obtain ⟨n25, d25, s25, fr25, K25, W25, rg25⟩ := sv_sw F E24 s24 sv_at_13fe (off' := 0x1400) (c := 0x380)
    (by decide) (by rw [g24_14]; sv_addr) (by decide) (by decide)
  have t25 : Steps n0 n25 := t24.trans d25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keep K25 (by decide)
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [rg25 sp, g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg25 (3 : Fin 32), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg25 (4 : Fin 32), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [rg25 (8 : Fin 32), g24_8]
  have g25_10 : reg n25 a0 = (w44) + BitVec.ofNat 32 0x1 := by rw [rg25 a0, g24_10]
  have g25_11 : reg n25 a1 = (w50) + BitVec.ofNat 32 0xFFFFFFFF := by rw [rg25 a1, g24_11]
  have g25_12 : reg n25 a2 = BitVec.ofNat 32 (img% svConstCmsAddress + 0x14) := by rw [rg25 a2, g24_12]
  have g25_13 : reg n25 a3 = BitVec.ofNat 32 0x1 := by rw [rg25 a3, g24_13]
  have g25_14 : reg n25 a4 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg25 a4, g24_14]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rg25 (18 : Fin 32), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rg25 (19 : Fin 32), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = x20 := by rw [rg25 (20 : Fin 32), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by rw [rg25 (21 : Fin 32), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = x22 := by rw [rg25 (22 : Fin 32), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = x23 := by rw [rg25 (23 : Fin 32), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = x24 := by rw [rg25 (24 : Fin 32), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by rw [rg25 (25 : Fin 32), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rg25 (26 : Fin 32), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = x27 := by rw [rg25 (27 : Fin 32), g24_27]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x420, 0x20), (0x420, 0x20), (0x380, 0x4)] := keep_kk24.trans K25.toL
  clear keep_kk24
  have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K25.w32 (by decide) (by decide)).trans w24_44
  have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K25.w32 (by decide) (by decide)).trans w24_50
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K25.w32 (by decide) (by decide)).trans w24_64
  have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K25.w32 (by decide) (by decide)).trans w24_68
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K25.w32 (by decide) (by decide)).trans w24_70
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K25.w32 (by decide) (by decide)).trans w24_74
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := (K25.w32 (by decide) (by decide)).trans w24_78
  have w25_174 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := (K25.w32 (by decide) (by decide)).trans w24_174
  have w25_380 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = BitVec.ofNat 32 (img% svConstCmsAddress + 0x14) := by rw [W25, g24_12]
  clear w24_174 w24_78 w24_74 w24_70 w24_68 w24_64 w24_50 w24_44 g24_14 g24_13 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_12 g24_11 g24_10 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  -- 0x1400: sw
  obtain ⟨n26, d26, s26, fr26, K26, W26, rg26⟩ := sv_sw F E25 s25 sv_at_1400 (off' := 0x1402) (c := 0x384)
    (by decide) (by rw [g25_14]; sv_addr) (by decide) (by decide)
  have t26 : Steps n0 n26 := t25.trans d26
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.keep K26 (by decide)
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [rg26 sp, g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg26 (3 : Fin 32), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg26 (4 : Fin 32), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [rg26 (8 : Fin 32), g25_8]
  have g26_10 : reg n26 a0 = (w44) + BitVec.ofNat 32 0x1 := by rw [rg26 a0, g25_10]
  have g26_11 : reg n26 a1 = (w50) + BitVec.ofNat 32 0xFFFFFFFF := by rw [rg26 a1, g25_11]
  have g26_12 : reg n26 a2 = BitVec.ofNat 32 (img% svConstCmsAddress + 0x14) := by rw [rg26 a2, g25_12]
  have g26_13 : reg n26 a3 = BitVec.ofNat 32 0x1 := by rw [rg26 a3, g25_13]
  have g26_14 : reg n26 a4 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg26 a4, g25_14]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [rg26 (18 : Fin 32), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [rg26 (19 : Fin 32), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [rg26 (20 : Fin 32), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [rg26 (21 : Fin 32), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [rg26 (22 : Fin 32), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [rg26 (23 : Fin 32), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = x24 := by rw [rg26 (24 : Fin 32), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [rg26 (25 : Fin 32), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rg26 (26 : Fin 32), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = x27 := by rw [rg26 (27 : Fin 32), g25_27]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x420, 0x20), (0x420, 0x20), (0x380, 0x4), (0x384, 0x4)] := keep_kk25.trans K26.toL
  clear keep_kk25
  have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K26.w32 (by decide) (by decide)).trans w25_44
  have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K26.w32 (by decide) (by decide)).trans w25_50
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K26.w32 (by decide) (by decide)).trans w25_64
  have w26_68 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K26.w32 (by decide) (by decide)).trans w25_68
  have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K26.w32 (by decide) (by decide)).trans w25_70
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K26.w32 (by decide) (by decide)).trans w25_74
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := (K26.w32 (by decide) (by decide)).trans w25_78
  have w26_174 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := (K26.w32 (by decide) (by decide)).trans w25_174
  have w26_380 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = BitVec.ofNat 32 (img% svConstCmsAddress + 0x14) := (K26.w32 (by decide) (by decide)).trans w25_380
  have w26_384 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = BitVec.ofNat 32 0x1 := by rw [W26, g25_13]
  clear w25_380 w25_174 w25_78 w25_74 w25_70 w25_68 w25_64 w25_50 w25_44 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_14 g25_13 g25_12 g25_11 g25_10 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 rg25 W25 K25 fr25 s25 d25
  -- 0x1402: sw
  obtain ⟨n27, d27, s27, fr27, K27, W27, rg27⟩ := sv_sw F E26 s26 sv_at_1402 (off' := 0x1404) (c := 0x388)
    (by decide) (by rw [g26_14]; sv_addr) (by decide) (by decide)
  have t27 : Steps n0 n27 := t26.trans d27
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.keep K27 (by decide)
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [rg27 sp, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg27 (3 : Fin 32), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg27 (4 : Fin 32), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [rg27 (8 : Fin 32), g26_8]
  have g27_10 : reg n27 a0 = (w44) + BitVec.ofNat 32 0x1 := by rw [rg27 a0, g26_10]
  have g27_11 : reg n27 a1 = (w50) + BitVec.ofNat 32 0xFFFFFFFF := by rw [rg27 a1, g26_11]
  have g27_12 : reg n27 a2 = BitVec.ofNat 32 (img% svConstCmsAddress + 0x14) := by rw [rg27 a2, g26_12]
  have g27_13 : reg n27 a3 = BitVec.ofNat 32 0x1 := by rw [rg27 a3, g26_13]
  have g27_14 : reg n27 a4 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg27 a4, g26_14]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [rg27 (18 : Fin 32), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [rg27 (19 : Fin 32), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [rg27 (20 : Fin 32), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [rg27 (21 : Fin 32), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [rg27 (22 : Fin 32), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [rg27 (23 : Fin 32), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = x24 := by rw [rg27 (24 : Fin 32), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [rg27 (25 : Fin 32), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rg27 (26 : Fin 32), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = x27 := by rw [rg27 (27 : Fin 32), g26_27]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x420, 0x20), (0x420, 0x20), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4)] := keep_kk26.trans K27.toL
  clear keep_kk26
  have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K27.w32 (by decide) (by decide)).trans w26_44
  have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K27.w32 (by decide) (by decide)).trans w26_50
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K27.w32 (by decide) (by decide)).trans w26_64
  have w27_68 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K27.w32 (by decide) (by decide)).trans w26_68
  have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K27.w32 (by decide) (by decide)).trans w26_70
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K27.w32 (by decide) (by decide)).trans w26_74
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := (K27.w32 (by decide) (by decide)).trans w26_78
  have w27_174 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := (K27.w32 (by decide) (by decide)).trans w26_174
  have w27_380 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = BitVec.ofNat 32 (img% svConstCmsAddress + 0x14) := (K27.w32 (by decide) (by decide)).trans w26_380
  have w27_384 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = BitVec.ofNat 32 0x1 := (K27.w32 (by decide) (by decide)).trans w26_384
  have w27_388 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (w44) + BitVec.ofNat 32 0x1 := by rw [W27, g26_10]
  clear w26_384 w26_380 w26_174 w26_78 w26_74 w26_70 w26_68 w26_64 w26_50 w26_44 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_14 g26_13 g26_12 g26_11 g26_10 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 rg26 W26 K26 fr26 s26 d26
  -- 0x1404: sw
  obtain ⟨n28, d28, s28, fr28, K28, W28, rg28⟩ := sv_sw F E27 s27 sv_at_1404 (off' := 0x1406) (c := 0x38C)
    (by decide) (by rw [g27_14]; sv_addr) (by decide) (by decide)
  have t28 : Steps n0 n28 := t27.trans d28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.keep K28 (by decide)
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [rg28 sp, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg28 (3 : Fin 32), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg28 (4 : Fin 32), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [rg28 (8 : Fin 32), g27_8]
  have g28_10 : reg n28 a0 = (w44) + BitVec.ofNat 32 0x1 := by rw [rg28 a0, g27_10]
  have g28_11 : reg n28 a1 = (w50) + BitVec.ofNat 32 0xFFFFFFFF := by rw [rg28 a1, g27_11]
  have g28_12 : reg n28 a2 = BitVec.ofNat 32 (img% svConstCmsAddress + 0x14) := by rw [rg28 a2, g27_12]
  have g28_13 : reg n28 a3 = BitVec.ofNat 32 0x1 := by rw [rg28 a3, g27_13]
  have g28_14 : reg n28 a4 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by rw [rg28 a4, g27_14]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [rg28 (18 : Fin 32), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [rg28 (19 : Fin 32), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [rg28 (20 : Fin 32), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [rg28 (21 : Fin 32), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [rg28 (22 : Fin 32), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [rg28 (23 : Fin 32), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = x24 := by rw [rg28 (24 : Fin 32), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [rg28 (25 : Fin 32), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rg28 (26 : Fin 32), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = x27 := by rw [rg28 (27 : Fin 32), g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x420, 0x20), (0x420, 0x20), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4)] := keep_kk27.trans K28.toL
  clear keep_kk27
  have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K28.w32 (by decide) (by decide)).trans w27_44
  have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K28.w32 (by decide) (by decide)).trans w27_50
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K28.w32 (by decide) (by decide)).trans w27_64
  have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K28.w32 (by decide) (by decide)).trans w27_68
  have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K28.w32 (by decide) (by decide)).trans w27_70
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K28.w32 (by decide) (by decide)).trans w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := (K28.w32 (by decide) (by decide)).trans w27_78
  have w28_174 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := (K28.w32 (by decide) (by decide)).trans w27_174
  have w28_380 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = BitVec.ofNat 32 (img% svConstCmsAddress + 0x14) := (K28.w32 (by decide) (by decide)).trans w27_380
  have w28_384 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = BitVec.ofNat 32 0x1 := (K28.w32 (by decide) (by decide)).trans w27_384
  have w28_388 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (w44) + BitVec.ofNat 32 0x1 := (K28.w32 (by decide) (by decide)).trans w27_388
  have w28_38c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (w50) + BitVec.ofNat 32 0xFFFFFFFF := by rw [W28, g27_11]
  clear w27_388 w27_384 w27_380 w27_174 w27_78 w27_74 w27_70 w27_68 w27_64 w27_50 w27_44 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_14 g27_13 g27_12 g27_11 g27_10 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 rg27 W27 K27 fr27 s27 d27
  -- 0x1406
  obtain ⟨n29, c29, u29⟩ := s28.block svTsig1406 E28.self svTsig1406_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have s29 : St n29.mem SV n29 0x140E (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have rb29 : ∀ q, reg n29 q = (runBlock svTsig1406 (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans c29
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by
    rw [rb29, runBlock_reg _ _ _ sp s28.zero (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb29, runBlock_reg _ _ _ (3 : Fin 32) s28.zero (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb29, runBlock_reg _ _ _ (4 : Fin 32) s28.zero (by decide), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by
    rw [rb29, runBlock_reg _ _ _ (8 : Fin 32) s28.zero (by decide), g28_8]
  have g29_13 : reg n29 a3 = BitVec.ofNat 32 0x1 := by
    rw [rb29, runBlock_reg _ _ _ a3 s28.zero (by decide), g28_13]
  have g29_14 : reg n29 a4 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by
    rw [rb29, runBlock_reg _ _ _ a4 s28.zero (by decide), g28_14]
  have g29_18 : reg n29 (18 : Fin 32) = out := by
    rw [rb29, runBlock_reg _ _ _ (18 : Fin 32) s28.zero (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by
    rw [rb29, runBlock_reg _ _ _ (19 : Fin 32) s28.zero (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = x20 := by
    rw [rb29, runBlock_reg _ _ _ (20 : Fin 32) s28.zero (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = x21 := by
    rw [rb29, runBlock_reg _ _ _ (21 : Fin 32) s28.zero (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = x22 := by
    rw [rb29, runBlock_reg _ _ _ (22 : Fin 32) s28.zero (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = x23 := by
    rw [rb29, runBlock_reg _ _ _ (23 : Fin 32) s28.zero (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = x24 := by
    rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = x25 := by
    rw [rb29, runBlock_reg _ _ _ (25 : Fin 32) s28.zero (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by
    rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = x27 := by
    rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
  have g29_10 : reg n29 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svTsig1406, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_10, g28_11, g28_12, g28_13, g28_14, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g29_11 : reg n29 a1 = B + 0x21A0 + BitVec.ofNat 32 0x380 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svTsig1406, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_10, g28_11, g28_12, g28_13, g28_14, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g29_12 : reg n29 a2 = BitVec.ofNat 32 0x2 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svTsig1406, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_10, g28_11, g28_12, g28_13, g28_14, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x420, 0x20), (0x420, 0x20), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m29]; exact w28_44
  have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m29]; exact w28_50
  have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := by rw [m29]; exact w28_64
  have w29_68 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m29]; exact w28_68
  have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m29]; exact w28_70
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m29]; exact w28_74
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m29]; exact w28_78
  have w29_174 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := by rw [m29]; exact w28_174
  have w29_380 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = BitVec.ofNat 32 (img% svConstCmsAddress + 0x14) := by rw [m29]; exact w28_380
  have w29_384 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = BitVec.ofNat 32 0x1 := by rw [m29]; exact w28_384
  have w29_388 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (w44) + BitVec.ofNat 32 0x1 := by rw [m29]; exact w28_388
  have w29_38c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (w50) + BitVec.ofNat 32 0xFFFFFFFF := by rw [m29]; exact w28_38c
  clear w28_38c w28_388 w28_384 w28_380 w28_174 w28_78 w28_74 w28_70 w28_68 w28_64 w28_50 w28_44 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_14 g28_13 g28_12 g28_11 g28_10 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 rg28 W28 K28 fr28 s28 d28
  -- 0x140E: sv_sha256P2F
  obtain ⟨n30, c30, s30, sp30, rk30, K30, D30, fr30⟩ := sv_sha256P2F (oc := 0x420) (pc := 0x380) (l0 := 1) (l1 := ((w50) + BitVec.ofNat 32 0xFFFFFFFF).toNat)
    FW E29 (S2.sv FW RS fR29) RS s29 sv_at_140e sv_at_1412 (by decide) (by decide) g29_2
    g29_10 g29_11 g29_12 (by decide) (by decide) (by decide)
    w29_380 w29_384 w29_388 (by rw [w29_38c, ofNat_toNat_self]) (.inr ⟨by decide, by decide⟩) (sa_drop1 sa_in hsa) (by decide) (sa_drop1_lt sa_in hsa)
  have t30 : Steps n0 n30 := t29.trans c30
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.keepL K30 (by decide)
  rw [sv_mbRo FW fR29 (.inr ⟨by decide, by decide⟩), sv_mbRo FW fR29 (sa_drop1 sa_in hsa)] at D30
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk30 (3 : Fin 32) (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk30 (4 : Fin 32) (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 0x1F := by rw [rk30 (8 : Fin 32) (by decide), g29_8]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [rk30 (18 : Fin 32) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [rk30 (19 : Fin 32) (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = x20 := by rw [rk30 (20 : Fin 32) (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [rk30 (21 : Fin 32) (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [rk30 (22 : Fin 32) (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [rk30 (23 : Fin 32) (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = x24 := by rw [rk30 (24 : Fin 32) (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = x25 := by rw [rk30 (25 : Fin 32) (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 := by rw [rk30 (26 : Fin 32) (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = x27 := by rw [rk30 (27 : Fin 32) (by decide), g29_27]
  have g30_2 : reg n30 sp = B + 0x21A0 := sp30
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x420, 0x20), (0x420, 0x20), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x20)] := keep_kk29.trans K30
  clear keep_kk29
  have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K30.w32 (by decide) (by decide)).trans w29_44
  have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K30.w32 (by decide) (by decide)).trans w29_50
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg := (K30.w32 (by decide) (by decide)).trans w29_64
  have w30_68 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K30.w32 (by decide) (by decide)).trans w29_68
  have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K30.w32 (by decide) (by decide)).trans w29_70
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K30.w32 (by decide) (by decide)).trans w29_74
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := (K30.w32 (by decide) (by decide)).trans w29_78
  have w30_174 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = tl := (K30.w32 (by decide) (by decide)).trans w29_174
  have w30_380 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = BitVec.ofNat 32 (img% svConstCmsAddress + 0x14) := (K30.w32 (by decide) (by decide)).trans w29_380
  have w30_384 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = BitVec.ofNat 32 0x1 := (K30.w32 (by decide) (by decide)).trans w29_384
  have w30_388 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (w44) + BitVec.ofNat 32 0x1 := (K30.w32 (by decide) (by decide)).trans w29_388
  have w30_38c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (w50) + BitVec.ofNat 32 0xFFFFFFFF := (K30.w32 (by decide) (by decide)).trans w29_38c
  clear w29_38c w29_388 w29_384 w29_380 w29_174 w29_78 w29_74 w29_70 w29_68 w29_64 w29_50 w29_44 g29_12 g29_11 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_14 g29_13 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29
  exact .inr ⟨htd, him, hsa, n30, t30, s30, E30, V30, fR30, g30_2, g30_3, g30_4, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, w30_44, w30_50, w30_64, w30_68, w30_70, w30_74, w30_78, w30_174, w30_380, w30_384, w30_388, w30_38c, D30, keep_kk30.mono (by decide)⟩

end C3.RV32.Sv
