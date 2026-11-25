import C3BootProofs.Proofs.SvCongr

/-!
# `sigstore::verify`: the issuer and the validity

From 0x1CA to the subject at 0x25A: the issuer, and the validity, a sequence of exactly two times.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svL41cc : List BInstr :=
  [.aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x27C, .aluImm .add a2 x0 0x30]
theorem svL41cc_end : blockEnd sigstoreVerifyCode 0x1CC svL41cc = some 0x1D4 := by
  simp only [svL41cc]
  rw [blockEnd, sv_at_1cc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1ce]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL41ea : List BInstr :=
  [.aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x27C]
theorem svL41ea_end : blockEnd sigstoreVerifyCode 0x1EA svL41ea = some 0x1EE := by
  simp only [svL41ea]
  rw [blockEnd, sv_at_1ea]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1ec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL4200 : List BInstr :=
  [.aluImm .add a1 sp 0x85, .aluImm .add a0 sp 0x3E5, .aluImm .add a2 x0 0xB]
theorem svL4200_end : blockEnd sigstoreVerifyCode 0x200 svL4200 = some 0x20A := by
  simp only [svL4200]
  rw [blockEnd, sv_at_200]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_204]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_208]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL421a : List BInstr :=
  [.aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x3E0]
theorem svL421a_end : blockEnd sigstoreVerifyCode 0x21A svL421a = some 0x21E := by
  simp only [svL421a]
  rw [blockEnd, sv_at_21a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_21c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL4236 : List BInstr :=
  [.aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x3E0]
theorem svL4236_end : blockEnd sigstoreVerifyCode 0x236 svL4236 = some 0x23A := by
  simp only [svL4236]
  rw [blockEnd, sv_at_236]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_238]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL414c : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x1]
theorem svL414c_end : blockEnd sigstoreVerifyCode 0x14C svL414c = some 0x14E := by
  simp only [svL414c]
  rw [blockEnd, sv_at_14c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_l4 {B out bp rootp dg lp ll rp rl tbp tbl sgp sgl arp arl sal sap : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x1CA (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = tbp)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = dg)
    (g0_21 : reg n0 (21 : Fin 32) = rootp)
    (g0_22 : reg n0 (22 : Fin 32) = ll)
    (g0_23 : reg n0 (23 : Fin 32) = sgp)
    (g0_25 : reg n0 (25 : Fin 32) = sgl)
    (g0_26 : reg n0 (26 : Fin 32) = lp)
    (g0_27 : reg n0 (27 : Fin 32) = tbl)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap)
    (w0_284 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = rp)
    (w0_288 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = rl)
    (tb_in : SvIn B (rp) (rl).toNat) :
    (¬ (∃ tl3, derElement 0x30 (memBytes M0 (rp) (rl).toNat) = .ok tl3 ∧ ∃ tl11, derElement 0x30 (memBytes M0 ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)).toNat) = .ok tl11 ∧ ∃ tm20 rs20, readTime (memBytes M0 (((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) (tl11.len)) = some (tm20, rs20) ∧ ∃ tm28 rs28, readTime rs20 = some (tm28, rs28) ∧ (rs28 = []) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl3, derElement 0x30 (memBytes M0 (rp) (rl).toNat) = .ok tl3 ∧
    ∃ tl11, derElement 0x30 (memBytes M0 ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)).toNat) = .ok tl11 ∧
    ∃ tm20 rs20, readTime (memBytes M0 (((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) (tl11.len)) = some (tm20, rs20) ∧
    ∃ tm28 rs28, readTime rs20 = some (tm28, rs28) ∧
    (rs28 = []) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x25A (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 ∧
        reg n' (9 : Fin 32) = tbp ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = dg ∧
        reg n' (21 : Fin 32) = rootp ∧
        reg n' (22 : Fin 32) = ll ∧
        reg n' (23 : Fin 32) = sgp ∧
        reg n' (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header ∧
        reg n' (25 : Fin 32) = sgl ∧
        reg n' (26 : Fin 32) = lp ∧
        reg n' (27 : Fin 32) = tbl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm28 / 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm28 % 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) ∧
        SvKeepL B n0.mem n'.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8), (0x58, 0x4), (0x54, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x1CA: sw
  obtain ⟨n1, d1, s1, fr1, K1, W1, rg1⟩ := sv_sw F E0 s0 sv_at_1ca (off' := 0x1CC) (c := 0x6C)
    (by decide) (by rw [g0_2]; sv_addr) (by decide) (by decide)
  have t1 : Steps n0 n1 := t0.trans d1
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.keep K1 (by decide)
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [rg1 sp, g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg1 (3 : Fin 32), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg1 (4 : Fin 32), g0_4]
  have g1_9 : reg n1 (9 : Fin 32) = tbp := by rw [rg1 (9 : Fin 32), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [rg1 (18 : Fin 32), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [rg1 (19 : Fin 32), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = dg := by rw [rg1 (20 : Fin 32), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = rootp := by rw [rg1 (21 : Fin 32), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = ll := by rw [rg1 (22 : Fin 32), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = sgp := by rw [rg1 (23 : Fin 32), g0_23]
  have g1_25 : reg n1 (25 : Fin 32) = sgl := by rw [rg1 (25 : Fin 32), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = lp := by rw [rg1 (26 : Fin 32), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = tbl := by rw [rg1 (27 : Fin 32), g0_27]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [(0x6C, 0x4)] := (SvKeepL.refl : SvKeepL B n0.mem n0.mem []).trans K1.toL
  have w1_70 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K1.w32 (by decide) (by decide)).trans w0_70
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K1.w32 (by decide) (by decide)).trans w0_74
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K1.w32 (by decide) (by decide)).trans w0_78
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K1.w32 (by decide) (by decide)).trans w0_7c
  have w1_284 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = rp := (K1.w32 (by decide) (by decide)).trans w0_284
  have w1_288 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = rl := (K1.w32 (by decide) (by decide)).trans w0_288
  have w1_6c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [W1, g0_26]
  -- 0x1CC
  obtain ⟨n2, c2, u2⟩ := s1.block svL41cc E1.self svL41cc_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have s2 : St n2.mem SV n2 0x1D4 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have rb2 : ∀ q, reg n2 q = (runBlock svL41cc (n1.mem, reg n1)).2 q := fun q => by rw [u2.regs]
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
  have g2_9 : reg n2 (9 : Fin 32) = tbp := by
    rw [rb2, runBlock_reg _ _ _ (9 : Fin 32) s1.zero (by decide), g1_9]
  have g2_18 : reg n2 (18 : Fin 32) = out := by
    rw [rb2, runBlock_reg _ _ _ (18 : Fin 32) s1.zero (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by
    rw [rb2, runBlock_reg _ _ _ (19 : Fin 32) s1.zero (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = dg := by
    rw [rb2, runBlock_reg _ _ _ (20 : Fin 32) s1.zero (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = rootp := by
    rw [rb2, runBlock_reg _ _ _ (21 : Fin 32) s1.zero (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = ll := by
    rw [rb2, runBlock_reg _ _ _ (22 : Fin 32) s1.zero (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = sgp := by
    rw [rb2, runBlock_reg _ _ _ (23 : Fin 32) s1.zero (by decide), g1_23]
  have g2_25 : reg n2 (25 : Fin 32) = sgl := by
    rw [rb2, runBlock_reg _ _ _ (25 : Fin 32) s1.zero (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = lp := by
    rw [rb2, runBlock_reg _ _ _ (26 : Fin 32) s1.zero (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = tbl := by
    rw [rb2, runBlock_reg _ _ _ (27 : Fin 32) s1.zero (by decide), g1_27]
  have g2_10 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, svL41cc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_9, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_25, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g2_11 : reg n2 a1 = B + 0x21A0 + BitVec.ofNat 32 0x27C := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, svL41cc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_9, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_25, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g2_12 : reg n2 a2 = BitVec.ofNat 32 0x30 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, svL41cc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_9, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_25, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x6C, 0x4)] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_6c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m2]; exact w1_6c
  have w2_70 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m2]; exact w1_70
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m2]; exact w1_74
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m2]; exact w1_78
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m2]; exact w1_7c
  have w2_284 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = rp := by rw [m2]; exact w1_284
  have w2_288 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = rl := by rw [m2]; exact w1_288
  clear w1_6c w1_288 w1_284 w1_7c w1_78 w1_74 w1_70 g1_27 g1_26 g1_25 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_9 g1_4 g1_3 g1_2 V1 E1 fR1 t1 rg1 W1 K1 fr1 s1 d1 g0_4 g0_3 fR0 t0
  -- 0x1D4: sv_elemF
  obtain ⟨n3, c3, s3, rk3, K3, Ok3, Er3, fr3⟩ := sv_elemF (oc := 0x80) (dc := 0x27C) (tag := 0x30)
    F E2 s2 sv_at_1d4 sv_at_1d8 (by decide) (by decide) g2_10 g2_11 g2_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w2_284 w2_288
  have t3 : Steps n0 n3 := t2.trans c3
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.keepL K3 (by decide)
  rw [sv_mb fR2 tb_in] at Ok3 Er3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [rk3 sp (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk3 (3 : Fin 32) (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk3 (4 : Fin 32) (by decide) (by decide), g2_4]
  have g3_9 : reg n3 (9 : Fin 32) = tbp := by rw [rk3 (9 : Fin 32) (by decide) (by decide), g2_9]
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by rw [rk3 a0 (by decide) (by decide), g2_10]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [rk3 (18 : Fin 32) (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [rk3 (19 : Fin 32) (by decide) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = dg := by rw [rk3 (20 : Fin 32) (by decide) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = rootp := by rw [rk3 (21 : Fin 32) (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = ll := by rw [rk3 (22 : Fin 32) (by decide) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = sgp := by rw [rk3 (23 : Fin 32) (by decide) (by decide), g2_23]
  have g3_25 : reg n3 (25 : Fin 32) = sgl := by rw [rk3 (25 : Fin 32) (by decide) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = lp := by rw [rk3 (26 : Fin 32) (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = tbl := by rw [rk3 (27 : Fin 32) (by decide) (by decide), g2_27]
  obtain ⟨r3, hr3⟩ : ∃ r, derElement 0x30 (memBytes M0 (rp) (rl).toNat) = r := ⟨_, rfl⟩
  rcases r3 with er3 | tl3
  · obtain ⟨zhr3, -⟩ := Er3 er3 hr3
    have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8)] := keep_kk2.trans K3
    clear keep_kk2
    have w3_6c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K3.w32 (by decide) (by decide)).trans w2_6c
    have w3_70 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K3.w32 (by decide) (by decide)).trans w2_70
    have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K3.w32 (by decide) (by decide)).trans w2_74
    have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K3.w32 (by decide) (by decide)).trans w2_78
    have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K3.w32 (by decide) (by decide)).trans w2_7c
    have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := zhr3
    clear w2_288 w2_284 w2_7c w2_78 w2_74 w2_70 w2_6c g2_12 g2_11 g2_10 g2_27 g2_26 g2_25 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_9 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 rb2 s2 m2 u2 c2
    -- 0x1DC: lw
    obtain ⟨n4, d4, u4⟩ := s3.lw E3.self sv_at_1dc (off' := 0x1DE) (by decide)
      (by rw [g3_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s4 : St n4.mem SV n4 0x1DE (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
    have g4_9 : reg n4 (9 : Fin 32) = tbp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_9]
    have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
    have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
    have g4_20 : reg n4 (20 : Fin 32) = dg := by rw [u4.regs, upd_ne (by decide) (by decide), g3_20]
    have g4_21 : reg n4 (21 : Fin 32) = rootp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
    have g4_22 : reg n4 (22 : Fin 32) = ll := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
    have g4_23 : reg n4 (23 : Fin 32) = sgp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_23]
    have g4_25 : reg n4 (25 : Fin 32) = sgl := by rw [u4.regs, upd_ne (by decide) (by decide), g3_25]
    have g4_26 : reg n4 (26 : Fin 32) = lp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_26]
    have g4_27 : reg n4 (27 : Fin 32) = tbl := by rw [u4.regs, upd_ne (by decide) (by decide), g3_27]
    have g4_10 : reg n4 a0 = 0 := by
      rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g3_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w3_80]
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m4]; exact w3_6c
    have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m4]; exact w3_70
    have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m4]; exact w3_74
    have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m4]; exact w3_78
    have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m4]; exact w3_7c
    have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m4]; exact w3_80
    clear w3_80 w3_7c w3_78 w3_74 w3_70 w3_6c zhr3
    -- 0x1DE: branch, taken
    obtain ⟨n5, d5, u5⟩ := s4.taken E4.self 0x7A0 sv_at_1de
      (by decide) (by rw [g4_10, s4.zero]; rfl)
    have s5 : St n5.mem SV n5 0x7A0 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
    have m5 : n5.mem = n4.mem := u5.mem
    have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
    have t5 : Steps n0 n5 := t4.trans (.single d5)
    have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
    have E5 : SvCode n5.mem := E4.fr F fr5
    have V5 : SvSaves B n5.mem v := V4.same m5
    have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, g4_2]
    have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, g4_3]
    have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, g4_4]
    have g5_9 : reg n5 (9 : Fin 32) = tbp := by rw [u5.regs, g4_9]
    have g5_10 : reg n5 a0 = 0 := by rw [u5.regs, g4_10]
    have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, g4_18]
    have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, g4_19]
    have g5_20 : reg n5 (20 : Fin 32) = dg := by rw [u5.regs, g4_20]
    have g5_21 : reg n5 (21 : Fin 32) = rootp := by rw [u5.regs, g4_21]
    have g5_22 : reg n5 (22 : Fin 32) = ll := by rw [u5.regs, g4_22]
    have g5_23 : reg n5 (23 : Fin 32) = sgp := by rw [u5.regs, g4_23]
    have g5_25 : reg n5 (25 : Fin 32) = sgl := by rw [u5.regs, g4_25]
    have g5_26 : reg n5 (26 : Fin 32) = lp := by rw [u5.regs, g4_26]
    have g5_27 : reg n5 (27 : Fin 32) = tbl := by rw [u5.regs, g4_27]
    have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8)] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m5]; exact w4_6c
    have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m5]; exact w4_70
    have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m5]; exact w4_74
    have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m5]; exact w4_78
    have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m5]; exact w4_7c
    have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m5]; exact w4_80
    clear w4_80 w4_7c w4_78 w4_74 w4_70 w4_6c g4_10 g4_27 g4_26 g4_25 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
    -- 0x7A0: lbu
    obtain ⟨n6, d6, u6⟩ := s5.lbu E5.self sv_at_7a0 (off' := 0x7A4) (by decide)
    have s6 : St n6.mem SV n6 0x7A4 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
    have t6 : Steps n0 n6 := t5.trans (.single d6)
    have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
    have E6 : SvCode n6.mem := E5.fr F fr6
    have V6 : SvSaves B n6.mem v := V5.same m6
    have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
    have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
    have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
    have g6_9 : reg n6 (9 : Fin 32) = tbp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_9]
    have g6_10 : reg n6 a0 = 0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_10]
    have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
    have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
    have g6_20 : reg n6 (20 : Fin 32) = dg := by rw [u6.regs, upd_ne (by decide) (by decide), g5_20]
    have g6_21 : reg n6 (21 : Fin 32) = rootp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
    have g6_22 : reg n6 (22 : Fin 32) = ll := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
    have g6_23 : reg n6 (23 : Fin 32) = sgp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
    have g6_25 : reg n6 (25 : Fin 32) = sgl := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
    have g6_26 : reg n6 (26 : Fin 32) = lp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
    have g6_27 : reg n6 (27 : Fin 32) = tbl := by rw [u6.regs, upd_ne (by decide) (by decide), g5_27]
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_6c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m6]; exact w5_6c
    have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m6]; exact w5_70
    have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m6]; exact w5_74
    have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m6]; exact w5_78
    have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m6]; exact w5_7c
    have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m6]; exact w5_80
    clear w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c g5_27 g5_26 g5_25 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_9 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
    exact .inl ⟨(fun ⟨tl3', h0', _⟩ => by rw [hr3] at h0'; cases h0'), sv_fail F E6 s6 t6 (fun x hx => (fR6 x hx).trans (fM x hx).symm) V6 hret g6_2 g6_18 hO g6_3 g6_4⟩
  obtain ⟨o0_3, o4_3, o8_3, o12_3, o16_3, d8_3, d12_3⟩ := Ok3 tl3 hr3
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8)] := keep_kk2.trans K3
  clear keep_kk2
  have w3_6c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K3.w32 (by decide) (by decide)).trans w2_6c
  have w3_70 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K3.w32 (by decide) (by decide)).trans w2_70
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K3.w32 (by decide) (by decide)).trans w2_74
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K3.w32 (by decide) (by decide)).trans w2_78
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K3.w32 (by decide) (by decide)).trans w2_7c
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (rp) + BitVec.ofNat 32 tl3.header := o0_3
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl3.len := o4_3
  have w3_88 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = rp := o8_3
  have w3_8c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl3.header + tl3.len) := o12_3
  have w3_284 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl3.header + tl3.len) := d8_3
  have w3_288 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl3.header + tl3.len) := d12_3
  have b3_90 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := o16_3
  clear w2_288 w2_284 w2_7c w2_78 w2_74 w2_70 w2_6c g2_12 g2_11 g2_10 g2_27 g2_26 g2_25 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_9 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 rb2 s2 m2 u2 c2
  -- 0x1DC: lw
  obtain ⟨n4, d4, u4⟩ := s3.lw E3.self sv_at_1dc (off' := 0x1DE) (by decide)
    (by rw [g3_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s4 : St n4.mem SV n4 0x1DE (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
  have g4_9 : reg n4 (9 : Fin 32) = tbp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = dg := by rw [u4.regs, upd_ne (by decide) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = rootp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = ll := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = sgp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_23]
  have g4_25 : reg n4 (25 : Fin 32) = sgl := by rw [u4.regs, upd_ne (by decide) (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = lp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = tbl := by rw [u4.regs, upd_ne (by decide) (by decide), g3_27]
  have g4_10 : reg n4 a0 = (rp) + BitVec.ofNat 32 tl3.header := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g3_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w3_80]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m4]; exact w3_6c
  have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m4]; exact w3_70
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m4]; exact w3_74
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m4]; exact w3_78
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m4]; exact w3_7c
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (rp) + BitVec.ofNat 32 tl3.header := by rw [m4]; exact w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl3.len := by rw [m4]; exact w3_84
  have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = rp := by rw [m4]; exact w3_88
  have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m4]; exact w3_8c
  have w4_284 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m4]; exact w3_284
  have w4_288 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m4]; exact w3_288
  have b4_90 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m4]; exact b3_90
  clear b3_90 w3_288 w3_284 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_74 w3_70 w3_6c d12_3 d8_3 o16_3 o12_3 o8_3 o4_3 o0_3 g3_27 g3_26 g3_25 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_9 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 Er3 Ok3 K3 rk3 s3 c3
  -- 0x1DE: branch, not taken
  obtain ⟨n5, d5, u5⟩ := s4.notTaken E4.self 0x1E2 sv_at_1de
    (by decide) (by rw [g4_10, s4.zero]; exact br_beq_f (tb_in.ok_ne hr3))
  have s5 : St n5.mem SV n5 0x1E2 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, g4_4]
  have g5_9 : reg n5 (9 : Fin 32) = tbp := by rw [u5.regs, g4_9]
  have g5_10 : reg n5 a0 = (rp) + BitVec.ofNat 32 tl3.header := by rw [u5.regs, g4_10]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = dg := by rw [u5.regs, g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = rootp := by rw [u5.regs, g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = ll := by rw [u5.regs, g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = sgp := by rw [u5.regs, g4_23]
  have g5_25 : reg n5 (25 : Fin 32) = sgl := by rw [u5.regs, g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = lp := by rw [u5.regs, g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = tbl := by rw [u5.regs, g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m5]; exact w4_6c
  have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m5]; exact w4_70
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m5]; exact w4_74
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m5]; exact w4_78
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m5]; exact w4_7c
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (rp) + BitVec.ofNat 32 tl3.header := by rw [m5]; exact w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl3.len := by rw [m5]; exact w4_84
  have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = rp := by rw [m5]; exact w4_88
  have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m5]; exact w4_8c
  have w5_284 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m5]; exact w4_284
  have w5_288 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m5]; exact w4_288
  have b5_90 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m5]; exact b4_90
  clear b4_90 w4_288 w4_284 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_74 w4_70 w4_6c g4_10 g4_27 g4_26 g4_25 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0x1E2: lw
  obtain ⟨n6, d6, u6⟩ := s5.lw E5.self sv_at_1e2 (off' := 0x1E4) (by decide)
    (by rw [g5_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s6 : St n6.mem SV n6 0x1E4 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
  have g6_9 : reg n6 (9 : Fin 32) = tbp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_9]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = dg := by rw [u6.regs, upd_ne (by decide) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = rootp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = ll := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = sgp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
  have g6_25 : reg n6 (25 : Fin 32) = sgl := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = lp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = tbl := by rw [u6.regs, upd_ne (by decide) (by decide), g5_27]
  have g6_10 : reg n6 a0 = rp := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g5_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr, w5_88]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_6c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m6]; exact w5_6c
  have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m6]; exact w5_70
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m6]; exact w5_74
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m6]; exact w5_78
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m6]; exact w5_7c
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (rp) + BitVec.ofNat 32 tl3.header := by rw [m6]; exact w5_80
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl3.len := by rw [m6]; exact w5_84
  have w6_88 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = rp := by rw [m6]; exact w5_88
  have w6_8c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m6]; exact w5_8c
  have w6_284 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m6]; exact w5_284
  have w6_288 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m6]; exact w5_288
  have b6_90 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m6]; exact b5_90
  clear b5_90 w5_288 w5_284 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c g5_27 g5_26 g5_25 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_10 g5_9 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0x1E4: sw
  obtain ⟨n7, d7, s7, fr7, K7, W7, rg7⟩ := sv_sw F E6 s6 sv_at_1e4 (off' := 0x1E6) (c := 0x68)
    (by decide) (by rw [g6_2]; sv_addr) (by decide) (by decide)
  have t7 : Steps n0 n7 := t6.trans d7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.keep K7 (by decide)
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [rg7 sp, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg7 (3 : Fin 32), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg7 (4 : Fin 32), g6_4]
  have g7_9 : reg n7 (9 : Fin 32) = tbp := by rw [rg7 (9 : Fin 32), g6_9]
  have g7_10 : reg n7 a0 = rp := by rw [rg7 a0, g6_10]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [rg7 (18 : Fin 32), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [rg7 (19 : Fin 32), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = dg := by rw [rg7 (20 : Fin 32), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = rootp := by rw [rg7 (21 : Fin 32), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = ll := by rw [rg7 (22 : Fin 32), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = sgp := by rw [rg7 (23 : Fin 32), g6_23]
  have g7_25 : reg n7 (25 : Fin 32) = sgl := by rw [rg7 (25 : Fin 32), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = lp := by rw [rg7 (26 : Fin 32), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = tbl := by rw [rg7 (27 : Fin 32), g6_27]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4)] := keep_kk6.trans K7.toL
  clear keep_kk6
  have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K7.w32 (by decide) (by decide)).trans w6_6c
  have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K7.w32 (by decide) (by decide)).trans w6_70
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K7.w32 (by decide) (by decide)).trans w6_74
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K7.w32 (by decide) (by decide)).trans w6_78
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K7.w32 (by decide) (by decide)).trans w6_7c
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (rp) + BitVec.ofNat 32 tl3.header := (K7.w32 (by decide) (by decide)).trans w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl3.len := (K7.w32 (by decide) (by decide)).trans w6_84
  have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = rp := (K7.w32 (by decide) (by decide)).trans w6_88
  have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl3.header + tl3.len) := (K7.w32 (by decide) (by decide)).trans w6_8c
  have w7_284 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl3.header + tl3.len) := (K7.w32 (by decide) (by decide)).trans w6_284
  have w7_288 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl3.header + tl3.len) := (K7.w32 (by decide) (by decide)).trans w6_288
  have b7_90 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := (K7.b8 (by decide) (by decide)).trans b6_90
  have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [W7, g6_10]
  clear b6_90 w6_288 w6_284 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c g6_10 g6_27 g6_26 g6_25 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0x1E6: lw
  obtain ⟨n8, d8, u8⟩ := s7.lw E7.self sv_at_1e6 (off' := 0x1E8) (by decide)
    (by rw [g7_2, show B + 0x21A0 + 0x8C = B + 0x21A0 + BitVec.ofNat 32 0x8C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s8 : St n8.mem SV n8 0x1E8 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
  have g8_9 : reg n8 (9 : Fin 32) = tbp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = dg := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = rootp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = ll := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = sgp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
  have g8_25 : reg n8 (25 : Fin 32) = sgl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = lp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = tbl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
  have g8_10 : reg n8 a0 = BitVec.ofNat 32 (tl3.header + tl3.len) := by
    rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g7_2, show B + 0x21A0 + 0x8C = B + 0x21A0 + BitVec.ofNat 32 0x8C by sv_addr, w7_8c]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m8]; exact w7_68
  have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m8]; exact w7_6c
  have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m8]; exact w7_70
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m8]; exact w7_74
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m8]; exact w7_78
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m8]; exact w7_7c
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (rp) + BitVec.ofNat 32 tl3.header := by rw [m8]; exact w7_80
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl3.len := by rw [m8]; exact w7_84
  have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = rp := by rw [m8]; exact w7_88
  have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m8]; exact w7_8c
  have w8_284 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m8]; exact w7_284
  have w8_288 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m8]; exact w7_288
  have b8_90 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m8]; exact b7_90
  clear w7_68 b7_90 w7_288 w7_284 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c g7_27 g7_26 g7_25 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_10 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 rg7 W7 K7 fr7 s7 d7
  -- 0x1E8: sw
  obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := sv_sw F E8 s8 sv_at_1e8 (off' := 0x1EA) (c := 0x64)
    (by decide) (by rw [g8_2]; sv_addr) (by decide) (by decide)
  have t9 : Steps n0 n9 := t8.trans d9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rg9 sp, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg9 (3 : Fin 32), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg9 (4 : Fin 32), g8_4]
  have g9_9 : reg n9 (9 : Fin 32) = tbp := by rw [rg9 (9 : Fin 32), g8_9]
  have g9_10 : reg n9 a0 = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [rg9 a0, g8_10]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rg9 (18 : Fin 32), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rg9 (19 : Fin 32), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = dg := by rw [rg9 (20 : Fin 32), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = rootp := by rw [rg9 (21 : Fin 32), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = ll := by rw [rg9 (22 : Fin 32), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = sgp := by rw [rg9 (23 : Fin 32), g8_23]
  have g9_25 : reg n9 (25 : Fin 32) = sgl := by rw [rg9 (25 : Fin 32), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = lp := by rw [rg9 (26 : Fin 32), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = tbl := by rw [rg9 (27 : Fin 32), g8_27]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4)] := keep_kk8.trans K9.toL
  clear keep_kk8
  have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := (K9.w32 (by decide) (by decide)).trans w8_68
  have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K9.w32 (by decide) (by decide)).trans w8_6c
  have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K9.w32 (by decide) (by decide)).trans w8_70
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K9.w32 (by decide) (by decide)).trans w8_74
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K9.w32 (by decide) (by decide)).trans w8_78
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K9.w32 (by decide) (by decide)).trans w8_7c
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (rp) + BitVec.ofNat 32 tl3.header := (K9.w32 (by decide) (by decide)).trans w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl3.len := (K9.w32 (by decide) (by decide)).trans w8_84
  have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = rp := (K9.w32 (by decide) (by decide)).trans w8_88
  have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl3.header + tl3.len) := (K9.w32 (by decide) (by decide)).trans w8_8c
  have w9_284 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl3.header + tl3.len) := (K9.w32 (by decide) (by decide)).trans w8_284
  have w9_288 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl3.header + tl3.len) := (K9.w32 (by decide) (by decide)).trans w8_288
  have b9_90 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := (K9.b8 (by decide) (by decide)).trans b8_90
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [W9, g8_10]
  clear b8_90 w8_288 w8_284 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 g8_10 g8_27 g8_26 g8_25 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
  -- 0x1EA
  obtain ⟨n10, c10, u10⟩ := s9.block svL41ea E9.self svL41ea_end
    ⟨trivial, trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0x1EE (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svL41ea (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
  have g10_9 : reg n10 (9 : Fin 32) = tbp := by
    rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
  have g10_18 : reg n10 (18 : Fin 32) = out := by
    rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by
    rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = dg := by
    rw [rb10, runBlock_reg _ _ _ (20 : Fin 32) s9.zero (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = rootp := by
    rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = ll := by
    rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = sgp := by
    rw [rb10, runBlock_reg _ _ _ (23 : Fin 32) s9.zero (by decide), g9_23]
  have g10_25 : reg n10 (25 : Fin 32) = sgl := by
    rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = lp := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = tbl := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svL41ea, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_9, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g10_11 : reg n10 a1 = B + 0x21A0 + BitVec.ofNat 32 0x27C := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svL41ea, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_9, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m10]; exact w9_64
  have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m10]; exact w9_68
  have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m10]; exact w9_6c
  have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m10]; exact w9_70
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m10]; exact w9_74
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m10]; exact w9_78
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m10]; exact w9_7c
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (rp) + BitVec.ofNat 32 tl3.header := by rw [m10]; exact w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl3.len := by rw [m10]; exact w9_84
  have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = rp := by rw [m10]; exact w9_88
  have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m10]; exact w9_8c
  have w10_284 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m10]; exact w9_284
  have w10_288 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m10]; exact w9_288
  have b10_90 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m10]; exact b9_90
  clear w9_64 b9_90 w9_288 w9_284 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 g9_27 g9_26 g9_25 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_9 g9_4 g9_3 g9_2 V9 E9 fR9 t9 rg9 W9 K9 fr9 s9 d9
  -- 0x1EE: sv_seqF
  obtain ⟨n11, c11, s11, sp11, rk11, K11, Ok11, Er11, fr11⟩ := sv_seqF (oc := 0x80) (dc := 0x27C)
    F E10 s10 sv_at_1ee sv_at_1f2 (by decide) (by decide) g10_2 g10_10 g10_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w10_284 w10_288 (tb_in.restW hr3)
  have t11 : Steps n0 n11 := t10.trans c11
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.keepL K11 (by decide)
  rw [sv_mb fR10 (tb_in.restW hr3)] at Ok11 Er11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [rk11 sp (by decide) (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk11 (3 : Fin 32) (by decide) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk11 (4 : Fin 32) (by decide) (by decide), g10_4]
  have g11_9 : reg n11 (9 : Fin 32) = tbp := by rw [rk11 (9 : Fin 32) (by decide) (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [rk11 (18 : Fin 32) (by decide) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [rk11 (19 : Fin 32) (by decide) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = dg := by rw [rk11 (20 : Fin 32) (by decide) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = rootp := by rw [rk11 (21 : Fin 32) (by decide) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = ll := by rw [rk11 (22 : Fin 32) (by decide) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = sgp := by rw [rk11 (23 : Fin 32) (by decide) (by decide), g10_23]
  have g11_25 : reg n11 (25 : Fin 32) = sgl := by rw [rk11 (25 : Fin 32) (by decide) (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = lp := by rw [rk11 (26 : Fin 32) (by decide) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = tbl := by rw [rk11 (27 : Fin 32) (by decide) (by decide), g10_27]
  obtain ⟨r11, hr11⟩ : ∃ r, derElement 0x30 (memBytes M0 ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)).toNat) = r := ⟨_, rfl⟩
  rcases r11 with er11 | tl11
  · obtain ⟨z11, -⟩ := Er11 er11 hr11
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8)] := keep_kk10.trans K11
    clear keep_kk10
    have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := (K11.w32 (by decide) (by decide)).trans w10_64
    have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := (K11.w32 (by decide) (by decide)).trans w10_68
    have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K11.w32 (by decide) (by decide)).trans w10_6c
    have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K11.w32 (by decide) (by decide)).trans w10_70
    have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K11.w32 (by decide) (by decide)).trans w10_74
    have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K11.w32 (by decide) (by decide)).trans w10_78
    have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K11.w32 (by decide) (by decide)).trans w10_7c
    have b11_90 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := (K11.b8 (by decide) (by decide)).trans b10_90
    have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := z11
    clear b10_90 w10_288 w10_284 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 g10_11 g10_10 g10_27 g10_26 g10_25 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
    -- 0x1F6: lw
    obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_1f6 (off' := 0x1F8) (by decide)
      (by rw [g11_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s12 : St n12.mem SV n12 0x1F8 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
    have g12_9 : reg n12 (9 : Fin 32) = tbp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
    have g12_20 : reg n12 (20 : Fin 32) = dg := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
    have g12_21 : reg n12 (21 : Fin 32) = rootp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = ll := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = sgp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
    have g12_25 : reg n12 (25 : Fin 32) = sgl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = lp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = tbl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
    have g12_24 : reg n12 (24 : Fin 32) = 0 := by
      rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g11_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w11_80]
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m12]; exact w11_64
    have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m12]; exact w11_68
    have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m12]; exact w11_6c
    have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m12]; exact w11_70
    have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m12]; exact w11_74
    have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m12]; exact w11_78
    have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m12]; exact w11_7c
    have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m12]; exact w11_80
    have b12_90 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m12]; exact b11_90
    clear w11_80 b11_90 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 z11
    -- 0x1F8: lbu
    obtain ⟨n13, d13, u13⟩ := s12.lbu E12.self sv_at_1f8 (off' := 0x1FC) (by decide)
    have s13 : St n13.mem SV n13 0x1FC (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
    have m13 : n13.mem = n12.mem := u13.mem
    have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
    have t13 : Steps n0 n13 := t12.trans (.single d13)
    have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
    have E13 : SvCode n13.mem := E12.fr F fr13
    have V13 : SvSaves B n13.mem v := V12.same m13
    have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_2]
    have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_3]
    have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_4]
    have g13_9 : reg n13 (9 : Fin 32) = tbp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_9]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, upd_ne (by decide) (by decide), g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_19]
    have g13_20 : reg n13 (20 : Fin 32) = dg := by rw [u13.regs, upd_ne (by decide) (by decide), g12_20]
    have g13_21 : reg n13 (21 : Fin 32) = rootp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = ll := by rw [u13.regs, upd_ne (by decide) (by decide), g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = sgp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = 0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_24]
    have g13_25 : reg n13 (25 : Fin 32) = sgl := by rw [u13.regs, upd_ne (by decide) (by decide), g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = lp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = tbl := by rw [u13.regs, upd_ne (by decide) (by decide), g12_27]
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8)] := by rw [m13]; exact keep_kk12
    clear keep_kk12
    have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m13]; exact w12_64
    have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m13]; exact w12_68
    have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m13]; exact w12_6c
    have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m13]; exact w12_70
    have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m13]; exact w12_74
    have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m13]; exact w12_78
    have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m13]; exact w12_7c
    have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m13]; exact w12_80
    have b13_90 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m13]; exact b12_90
    clear b12_90 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 g12_24 g12_27 g12_26 g12_25 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
    -- 0x1FC: branch, taken
    obtain ⟨n14, d14, u14⟩ := s13.taken E13.self 0x7A4 sv_at_1fc
      (by decide) (by rw [g13_24, s13.zero]; rfl)
    have s14 : St n14.mem SV n14 0x7A4 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
    have m14 : n14.mem = n13.mem := u14.mem
    have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
    have t14 : Steps n0 n14 := t13.trans (.single d14)
    have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
    have E14 : SvCode n14.mem := E13.fr F fr14
    have V14 : SvSaves B n14.mem v := V13.same m14
    have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, g13_2]
    have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, g13_3]
    have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, g13_4]
    have g14_9 : reg n14 (9 : Fin 32) = tbp := by rw [u14.regs, g13_9]
    have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, g13_18]
    have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, g13_19]
    have g14_20 : reg n14 (20 : Fin 32) = dg := by rw [u14.regs, g13_20]
    have g14_21 : reg n14 (21 : Fin 32) = rootp := by rw [u14.regs, g13_21]
    have g14_22 : reg n14 (22 : Fin 32) = ll := by rw [u14.regs, g13_22]
    have g14_23 : reg n14 (23 : Fin 32) = sgp := by rw [u14.regs, g13_23]
    have g14_24 : reg n14 (24 : Fin 32) = 0 := by rw [u14.regs, g13_24]
    have g14_25 : reg n14 (25 : Fin 32) = sgl := by rw [u14.regs, g13_25]
    have g14_26 : reg n14 (26 : Fin 32) = lp := by rw [u14.regs, g13_26]
    have g14_27 : reg n14 (27 : Fin 32) = tbl := by rw [u14.regs, g13_27]
    have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8)] := by rw [m14]; exact keep_kk13
    clear keep_kk13
    have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m14]; exact w13_64
    have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m14]; exact w13_68
    have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m14]; exact w13_6c
    have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m14]; exact w13_70
    have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m14]; exact w13_74
    have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m14]; exact w13_78
    have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m14]; exact w13_7c
    have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m14]; exact w13_80
    have b14_90 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m14]; exact b13_90
    clear b13_90 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
    exact .inl ⟨(fun ⟨tl3', h0', tl11', h1', _⟩ => by rw [hr3] at h0'; cases h0'; rw [hr11] at h1'; cases h1'), sv_fail F E14 s14 t14 (fun x hx => (fR14 x hx).trans (fM x hx).symm) V14 hret g14_2 g14_18 hO g14_3 g14_4⟩
  obtain ⟨o0_11, o4_11, o8_11, o12_11, d8_11, d12_11⟩ := Ok11 tl11 hr11
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8)] := keep_kk10.trans K11
  clear keep_kk10
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := (K11.w32 (by decide) (by decide)).trans w10_64
  have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := (K11.w32 (by decide) (by decide)).trans w10_68
  have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K11.w32 (by decide) (by decide)).trans w10_6c
  have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K11.w32 (by decide) (by decide)).trans w10_70
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K11.w32 (by decide) (by decide)).trans w10_74
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K11.w32 (by decide) (by decide)).trans w10_78
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K11.w32 (by decide) (by decide)).trans w10_7c
  have b11_90 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := (K11.b8 (by decide) (by decide)).trans b10_90
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := o0_11
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl11.len := o4_11
  have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := o8_11
  have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl11.len := o12_11
  have w11_284 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := d8_11
  have w11_288 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := d12_11
  clear b10_90 w10_288 w10_284 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 g10_11 g10_10 g10_27 g10_26 g10_25 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0x1F6: lw
  obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_1f6 (off' := 0x1F8) (by decide)
    (by rw [g11_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s12 : St n12.mem SV n12 0x1F8 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
  have g12_9 : reg n12 (9 : Fin 32) = tbp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = dg := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = rootp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = ll := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = sgp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
  have g12_25 : reg n12 (25 : Fin 32) = sgl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = lp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = tbl := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
  have g12_24 : reg n12 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w11_80]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m12]; exact w11_64
  have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m12]; exact w11_68
  have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m12]; exact w11_6c
  have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m12]; exact w11_70
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m12]; exact w11_74
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m12]; exact w11_78
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m12]; exact w11_7c
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m12]; exact w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl11.len := by rw [m12]; exact w11_84
  have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m12]; exact w11_88
  have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl11.len := by rw [m12]; exact w11_8c
  have w12_284 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m12]; exact w11_284
  have w12_288 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m12]; exact w11_288
  have b12_90 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m12]; exact b11_90
  clear w11_288 w11_284 w11_8c w11_88 w11_84 w11_80 b11_90 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 d12_11 d8_11 o12_11 o8_11 o4_11 o0_11 g11_27 g11_26 g11_25 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 Er11 Ok11 K11 rk11 sp11 s11 c11
  -- 0x1F8: lbu
  obtain ⟨n13, d13, u13⟩ := s12.lbu E12.self sv_at_1f8 (off' := 0x1FC) (by decide)
  have b12_84 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by
    have h := byte_of_ld w12_84
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr]; exact h.1
  have s13 : St n13.mem SV n13 0x1FC (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_4]
  have g13_9 : reg n13 (9 : Fin 32) = tbp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, upd_ne (by decide) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = dg := by rw [u13.regs, upd_ne (by decide) (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = rootp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = ll := by rw [u13.regs, upd_ne (by decide) (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = sgp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u13.regs, upd_ne (by decide) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = sgl := by rw [u13.regs, upd_ne (by decide) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = lp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = tbl := by rw [u13.regs, upd_ne (by decide) (by decide), g12_27]
  have g13_8 : reg n13 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g12_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, b12_84]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m13]; exact w12_64
  have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m13]; exact w12_68
  have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m13]; exact w12_6c
  have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m13]; exact w12_70
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m13]; exact w12_74
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m13]; exact w12_78
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m13]; exact w12_7c
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m13]; exact w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl11.len := by rw [m13]; exact w12_84
  have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m13]; exact w12_88
  have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl11.len := by rw [m13]; exact w12_8c
  have w13_284 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m13]; exact w12_284
  have w13_288 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m13]; exact w12_288
  have b13_84 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m13]; exact b12_84
  have b13_90 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m13]; exact b12_90
  clear b12_90 w12_288 w12_284 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 g12_24 g12_27 g12_26 g12_25 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0x1FC: branch, not taken
  obtain ⟨n14, d14, u14⟩ := s13.notTaken E13.self 0x200 sv_at_1fc
    (by decide) (by rw [g13_24, s13.zero]; exact br_beq_f ((tb_in.restW hr3).ok_ne hr11))
  have s14 : St n14.mem SV n14 0x200 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans (.single d14)
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u14.regs, g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = tbp := by rw [u14.regs, g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = dg := by rw [u14.regs, g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = rootp := by rw [u14.regs, g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = ll := by rw [u14.regs, g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = sgp := by rw [u14.regs, g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u14.regs, g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = sgl := by rw [u14.regs, g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = lp := by rw [u14.regs, g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = tbl := by rw [u14.regs, g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m14]; exact w13_64
  have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m14]; exact w13_68
  have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m14]; exact w13_6c
  have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m14]; exact w13_70
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m14]; exact w13_74
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m14]; exact w13_78
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m14]; exact w13_7c
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m14]; exact w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl11.len := by rw [m14]; exact w13_84
  have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m14]; exact w13_88
  have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl11.len := by rw [m14]; exact w13_8c
  have w14_284 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m14]; exact w13_284
  have w14_288 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m14]; exact w13_288
  have b14_84 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m14]; exact b13_84
  have b14_90 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m14]; exact b13_90
  clear b13_90 b13_84 w13_288 w13_284 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 g13_8 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 b12_84 u13 d13
  -- 0x200
  obtain ⟨n15, c15, u15⟩ := s14.block svL4200 E14.self svL4200_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have s15 : St n15.mem SV n15 0x20A (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have rb15 : ∀ q, reg n15 q = (runBlock svL4200 (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans c15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by
    rw [rb15, runBlock_reg _ _ _ sp s14.zero (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb15, runBlock_reg _ _ _ (3 : Fin 32) s14.zero (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb15, runBlock_reg _ _ _ (4 : Fin 32) s14.zero (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb15, runBlock_reg _ _ _ (8 : Fin 32) s14.zero (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = tbp := by
    rw [rb15, runBlock_reg _ _ _ (9 : Fin 32) s14.zero (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = out := by
    rw [rb15, runBlock_reg _ _ _ (18 : Fin 32) s14.zero (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by
    rw [rb15, runBlock_reg _ _ _ (19 : Fin 32) s14.zero (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = dg := by
    rw [rb15, runBlock_reg _ _ _ (20 : Fin 32) s14.zero (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = rootp := by
    rw [rb15, runBlock_reg _ _ _ (21 : Fin 32) s14.zero (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = ll := by
    rw [rb15, runBlock_reg _ _ _ (22 : Fin 32) s14.zero (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = sgp := by
    rw [rb15, runBlock_reg _ _ _ (23 : Fin 32) s14.zero (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by
    rw [rb15, runBlock_reg _ _ _ (24 : Fin 32) s14.zero (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = sgl := by
    rw [rb15, runBlock_reg _ _ _ (25 : Fin 32) s14.zero (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = lp := by
    rw [rb15, runBlock_reg _ _ _ (26 : Fin 32) s14.zero (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = tbl := by
    rw [rb15, runBlock_reg _ _ _ (27 : Fin 32) s14.zero (by decide), g14_27]
  have g15_10 : reg n15 a0 = B + 0x21A0 + BitVec.ofNat 32 0x3E5 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svL4200, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g15_11 : reg n15 a1 = B + 0x21A0 + BitVec.ofNat 32 0x85 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svL4200, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g15_12 : reg n15 a2 = BitVec.ofNat 32 0xB := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svL4200, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m15]; exact w14_64
  have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m15]; exact w14_68
  have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m15]; exact w14_6c
  have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m15]; exact w14_70
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m15]; exact w14_74
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m15]; exact w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m15]; exact w14_7c
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m15]; exact w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl11.len := by rw [m15]; exact w14_84
  have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m15]; exact w14_88
  have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl11.len := by rw [m15]; exact w14_8c
  have w15_284 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m15]; exact w14_284
  have w15_288 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m15]; exact w14_288
  have b15_84 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m15]; exact b14_84
  have b15_90 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m15]; exact b14_90
  clear b14_90 b14_84 w14_288 w14_284 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
  have b15_85 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by
    have h := byte_of_ld w15_84
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x85 = B + 0x21A0 + BitVec.ofNat 32 0x84 + 1 by sv_addr]; exact h.2.1
  have b15_86 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by
    have h := byte_of_ld w15_84
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x86 = B + 0x21A0 + BitVec.ofNat 32 0x84 + 2 by sv_addr]; exact h.2.2.1
  have b15_87 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by
    have h := byte_of_ld w15_84
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x87 = B + 0x21A0 + BitVec.ofNat 32 0x84 + 3 by sv_addr]; exact h.2.2.2
  -- 0x20A: memcpy
  obtain ⟨n16, P16, K16, X16⟩ := sv_mc (c := 0x3E5) (d := 0x85) (N := 0xB) F E15 s15 sv_at_20a sv_at_20e
    (by decide) (by decide) g15_2 g15_10 g15_11 g15_12
    (by decide) (by decide) (by decide)
  have s16 := P16.st
  have fr16 := P16.fr
  have t16 : Steps n0 n16 := t15.trans P16.steps
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [P16.regs sp (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P16.regs (3 : Fin 32) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P16.regs (4 : Fin 32) (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [P16.regs (8 : Fin 32) (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = tbp := by rw [P16.regs (9 : Fin 32) (by decide), g15_9]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [P16.regs (18 : Fin 32) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [P16.regs (19 : Fin 32) (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = dg := by rw [P16.regs (20 : Fin 32) (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = rootp := by rw [P16.regs (21 : Fin 32) (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = ll := by rw [P16.regs (22 : Fin 32) (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = sgp := by rw [P16.regs (23 : Fin 32) (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [P16.regs (24 : Fin 32) (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = sgl := by rw [P16.regs (25 : Fin 32) (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = lp := by rw [P16.regs (26 : Fin 32) (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = tbl := by rw [P16.regs (27 : Fin 32) (by decide), g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := (K16.w32 (by decide) (by decide)).trans w15_64
  have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := (K16.w32 (by decide) (by decide)).trans w15_68
  have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K16.w32 (by decide) (by decide)).trans w15_6c
  have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K16.w32 (by decide) (by decide)).trans w15_70
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K16.w32 (by decide) (by decide)).trans w15_74
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K16.w32 (by decide) (by decide)).trans w15_78
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K16.w32 (by decide) (by decide)).trans w15_7c
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K16.w32 (by decide) (by decide)).trans w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl11.len := (K16.w32 (by decide) (by decide)).trans w15_84
  have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K16.w32 (by decide) (by decide)).trans w15_88
  have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl11.len := (K16.w32 (by decide) (by decide)).trans w15_8c
  have w16_284 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := (K16.w32 (by decide) (by decide)).trans w15_284
  have w16_288 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := (K16.w32 (by decide) (by decide)).trans w15_288
  have b16_84 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := (K16.b8 (by decide) (by decide)).trans b15_84
  have b16_85 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := (K16.b8 (by decide) (by decide)).trans b15_85
  have b16_86 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := (K16.b8 (by decide) (by decide)).trans b15_86
  have b16_87 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := (K16.b8 (by decide) (by decide)).trans b15_87
  have b16_90 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := (K16.b8 (by decide) (by decide)).trans b15_90
  have w16_3e8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by
    rw [← w15_88]
    exact ld_cp fun q hq => by
      have := X16 (0x3 + q) (by omega)
      rwa [show 0x3E5 + (0x3 + q) = 0x3E8 + q by omega,
        show 0x85 + (0x3 + q) = 0x88 + q by omega] at this
  have w16_3ec : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 tl11.len := by
    rw [← w15_8c]
    exact ld_cp fun q hq => by
      have := X16 (0x7 + q) (by omega)
      rwa [show 0x3E5 + (0x7 + q) = 0x3EC + q by omega,
        show 0x85 + (0x7 + q) = 0x8C + q by omega] at this
  have b16_3e5 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [show 0x3E5 = 0x3E5 + 0x0 from rfl, X16 0x0 (by decide)]; exact b15_85
  have b16_3e6 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [show 0x3E6 = 0x3E5 + 0x1 from rfl, X16 0x1 (by decide)]; exact b15_86
  have b16_3e7 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [show 0x3E7 = 0x3E5 + 0x2 from rfl, X16 0x2 (by decide)]; exact b15_87
  clear b15_90 b15_84 w15_288 w15_284 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 g15_12 g15_11 g15_10 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
  -- 0x212: sw
  obtain ⟨n17, d17, s17, fr17, K17, W17, rg17⟩ := sv_sw F E16 s16 sv_at_212 (off' := 0x216) (c := 0x3E0)
    (by decide) (by rw [g16_2]; sv_addr) (by decide) (by decide)
  have t17 : Steps n0 n17 := t16.trans d17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keep K17 (by decide)
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [rg17 sp, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg17 (3 : Fin 32), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg17 (4 : Fin 32), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg17 (8 : Fin 32), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = tbp := by rw [rg17 (9 : Fin 32), g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [rg17 (18 : Fin 32), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [rg17 (19 : Fin 32), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = dg := by rw [rg17 (20 : Fin 32), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = rootp := by rw [rg17 (21 : Fin 32), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = ll := by rw [rg17 (22 : Fin 32), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = sgp := by rw [rg17 (23 : Fin 32), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [rg17 (24 : Fin 32), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = sgl := by rw [rg17 (25 : Fin 32), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = lp := by rw [rg17 (26 : Fin 32), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = tbl := by rw [rg17 (27 : Fin 32), g16_27]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4)] := keep_kk16.trans K17.toL
  clear keep_kk16
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := (K17.w32 (by decide) (by decide)).trans w16_64
  have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := (K17.w32 (by decide) (by decide)).trans w16_68
  have w17_6c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K17.w32 (by decide) (by decide)).trans w16_6c
  have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K17.w32 (by decide) (by decide)).trans w16_70
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K17.w32 (by decide) (by decide)).trans w16_74
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K17.w32 (by decide) (by decide)).trans w16_78
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K17.w32 (by decide) (by decide)).trans w16_7c
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K17.w32 (by decide) (by decide)).trans w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl11.len := (K17.w32 (by decide) (by decide)).trans w16_84
  have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K17.w32 (by decide) (by decide)).trans w16_88
  have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl11.len := (K17.w32 (by decide) (by decide)).trans w16_8c
  have w17_284 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := (K17.w32 (by decide) (by decide)).trans w16_284
  have w17_288 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := (K17.w32 (by decide) (by decide)).trans w16_288
  have w17_3e8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K17.w32 (by decide) (by decide)).trans w16_3e8
  have w17_3ec : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 tl11.len := (K17.w32 (by decide) (by decide)).trans w16_3ec
  have b17_84 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := (K17.b8 (by decide) (by decide)).trans b16_84
  have b17_85 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := (K17.b8 (by decide) (by decide)).trans b16_85
  have b17_86 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := (K17.b8 (by decide) (by decide)).trans b16_86
  have b17_87 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := (K17.b8 (by decide) (by decide)).trans b16_87
  have b17_90 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := (K17.b8 (by decide) (by decide)).trans b16_90
  have b17_3e5 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := (K17.b8 (by decide) (by decide)).trans b16_3e5
  have b17_3e6 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := (K17.b8 (by decide) (by decide)).trans b16_3e6
  have b17_3e7 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := (K17.b8 (by decide) (by decide)).trans b16_3e7
  have w17_3e0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [W17, g16_24]
  clear b16_3e7 b16_3e6 b16_3e5 w16_3ec w16_3e8 b16_90 b16_87 b16_86 b16_85 b16_84 w16_288 w16_284 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_74 w16_70 w16_6c w16_68 w16_64 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 s16 X16 K16 P16 b15_87 b15_86 b15_85
  -- 0x216: sb
  obtain ⟨n18, d18, s18, fr18, K18, W18, rg18⟩ := sv_sb F E17 s17 sv_at_216 (off' := 0x21A) (c := 0x3E4)
    (by decide) (by rw [g17_2]; sv_addr) (by decide)
  have t18 : Steps n0 n18 := t17.trans d18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keep K18 (by decide)
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [rg18 sp, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg18 (3 : Fin 32), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg18 (4 : Fin 32), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg18 (8 : Fin 32), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = tbp := by rw [rg18 (9 : Fin 32), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [rg18 (18 : Fin 32), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [rg18 (19 : Fin 32), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = dg := by rw [rg18 (20 : Fin 32), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = rootp := by rw [rg18 (21 : Fin 32), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = ll := by rw [rg18 (22 : Fin 32), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = sgp := by rw [rg18 (23 : Fin 32), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [rg18 (24 : Fin 32), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = sgl := by rw [rg18 (25 : Fin 32), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = lp := by rw [rg18 (26 : Fin 32), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = tbl := by rw [rg18 (27 : Fin 32), g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1)] := keep_kk17.trans K18.toL
  clear keep_kk17
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := (K18.w32 (by decide) (by decide)).trans w17_64
  have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := (K18.w32 (by decide) (by decide)).trans w17_68
  have w18_6c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K18.w32 (by decide) (by decide)).trans w17_6c
  have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K18.w32 (by decide) (by decide)).trans w17_70
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K18.w32 (by decide) (by decide)).trans w17_74
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K18.w32 (by decide) (by decide)).trans w17_78
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K18.w32 (by decide) (by decide)).trans w17_7c
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K18.w32 (by decide) (by decide)).trans w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl11.len := (K18.w32 (by decide) (by decide)).trans w17_84
  have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K18.w32 (by decide) (by decide)).trans w17_88
  have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl11.len := (K18.w32 (by decide) (by decide)).trans w17_8c
  have w18_284 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := (K18.w32 (by decide) (by decide)).trans w17_284
  have w18_288 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := (K18.w32 (by decide) (by decide)).trans w17_288
  have w18_3e0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K18.w32 (by decide) (by decide)).trans w17_3e0
  have w18_3e8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K18.w32 (by decide) (by decide)).trans w17_3e8
  have w18_3ec : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 tl11.len := (K18.w32 (by decide) (by decide)).trans w17_3ec
  have b18_84 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_84
  have b18_85 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := (K18.b8 (by decide) (by decide)).trans b17_85
  have b18_86 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := (K18.b8 (by decide) (by decide)).trans b17_86
  have b18_87 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := (K18.b8 (by decide) (by decide)).trans b17_87
  have b18_90 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := (K18.b8 (by decide) (by decide)).trans b17_90
  have b18_3e5 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := (K18.b8 (by decide) (by decide)).trans b17_3e5
  have b18_3e6 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := (K18.b8 (by decide) (by decide)).trans b17_3e6
  have b18_3e7 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := (K18.b8 (by decide) (by decide)).trans b17_3e7
  have b18_3e4 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [W18, g17_8, lbu_low]
  clear w17_3e0 b17_3e7 b17_3e6 b17_3e5 b17_90 b17_87 b17_86 b17_85 b17_84 w17_3ec w17_3e8 w17_288 w17_284 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_74 w17_70 w17_6c w17_68 w17_64 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 rg17 W17 K17 fr17 s17 d17
  -- 0x21A
  obtain ⟨n19, c19, u19⟩ := s18.block svL421a E18.self svL421a_end
    ⟨trivial, trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem SV n19 0x21E (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock svL421a (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
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
  have g19_8 : reg n19 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb19, runBlock_reg _ _ _ (8 : Fin 32) s18.zero (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = tbp := by
    rw [rb19, runBlock_reg _ _ _ (9 : Fin 32) s18.zero (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = out := by
    rw [rb19, runBlock_reg _ _ _ (18 : Fin 32) s18.zero (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by
    rw [rb19, runBlock_reg _ _ _ (19 : Fin 32) s18.zero (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = dg := by
    rw [rb19, runBlock_reg _ _ _ (20 : Fin 32) s18.zero (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = rootp := by
    rw [rb19, runBlock_reg _ _ _ (21 : Fin 32) s18.zero (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = ll := by
    rw [rb19, runBlock_reg _ _ _ (22 : Fin 32) s18.zero (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = sgp := by
    rw [rb19, runBlock_reg _ _ _ (23 : Fin 32) s18.zero (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by
    rw [rb19, runBlock_reg _ _ _ (24 : Fin 32) s18.zero (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = sgl := by
    rw [rb19, runBlock_reg _ _ _ (25 : Fin 32) s18.zero (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = lp := by
    rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = tbl := by
    rw [rb19, runBlock_reg _ _ _ (27 : Fin 32) s18.zero (by decide), g18_27]
  have g19_10 : reg n19 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svL421a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g19_11 : reg n19 a1 = B + 0x21A0 + BitVec.ofNat 32 0x3E0 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svL421a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m19]; exact w18_64
  have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m19]; exact w18_68
  have w19_6c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m19]; exact w18_6c
  have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m19]; exact w18_70
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m19]; exact w18_74
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m19]; exact w18_78
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m19]; exact w18_7c
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m19]; exact w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl11.len := by rw [m19]; exact w18_84
  have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m19]; exact w18_88
  have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl11.len := by rw [m19]; exact w18_8c
  have w19_284 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m19]; exact w18_284
  have w19_288 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m19]; exact w18_288
  have w19_3e0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m19]; exact w18_3e0
  have w19_3e8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m19]; exact w18_3e8
  have w19_3ec : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 tl11.len := by rw [m19]; exact w18_3ec
  have b19_84 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m19]; exact b18_84
  have b19_85 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m19]; exact b18_85
  have b19_86 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m19]; exact b18_86
  have b19_87 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m19]; exact b18_87
  have b19_90 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m19]; exact b18_90
  have b19_3e4 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m19]; exact b18_3e4
  have b19_3e5 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m19]; exact b18_3e5
  have b19_3e6 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m19]; exact b18_3e6
  have b19_3e7 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m19]; exact b18_3e7
  clear b18_3e4 b18_3e7 b18_3e6 b18_3e5 b18_90 b18_87 b18_86 b18_85 b18_84 w18_3ec w18_3e8 w18_3e0 w18_288 w18_284 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_74 w18_70 w18_6c w18_68 w18_64 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 rg18 W18 K18 fr18 s18 d18
  -- 0x21E: sv_rtF
  obtain ⟨n20, c20, s20, sp20, rk20, K20, Ok20, Er20, fr20⟩ := sv_rtF (oc := 0x80) (dc := 0x3E0) (rl := tl11.len)
    F E19 s19 sv_at_21e sv_at_222 (by decide) (by decide) g19_2 g19_10 g19_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w19_3e8 w19_3ec ((tb_in.restW hr3).content hr11)
  have t20 : Steps n0 n20 := t19.trans c20
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.keepL K20 (by decide)
  rw [sv_mb fR19 ((tb_in.restW hr3).content hr11)] at Ok20 Er20
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk20 (3 : Fin 32) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk20 (4 : Fin 32) (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk20 (8 : Fin 32) (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = tbp := by rw [rk20 (9 : Fin 32) (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [rk20 (18 : Fin 32) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [rk20 (19 : Fin 32) (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = dg := by rw [rk20 (20 : Fin 32) (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = rootp := by rw [rk20 (21 : Fin 32) (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = ll := by rw [rk20 (22 : Fin 32) (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = sgp := by rw [rk20 (23 : Fin 32) (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [rk20 (24 : Fin 32) (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = sgl := by rw [rk20 (25 : Fin 32) (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = lp := by rw [rk20 (26 : Fin 32) (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = tbl := by rw [rk20 (27 : Fin 32) (by decide), g19_27]
  have g20_2 : reg n20 sp = B + 0x21A0 := sp20
  obtain ⟨r20, hr20⟩ : ∃ r, readTime (memBytes M0 (((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) (tl11.len)) = r := ⟨_, rfl⟩
  rcases r20 with _ | ⟨tm20, rs20⟩
  · have y0_20 := Er20 hr20
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8)] := keep_kk19.trans K20
    clear keep_kk19
    have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := (K20.w32 (by decide) (by decide)).trans w19_64
    have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := (K20.w32 (by decide) (by decide)).trans w19_68
    have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K20.w32 (by decide) (by decide)).trans w19_6c
    have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K20.w32 (by decide) (by decide)).trans w19_70
    have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K20.w32 (by decide) (by decide)).trans w19_74
    have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K20.w32 (by decide) (by decide)).trans w19_78
    have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K20.w32 (by decide) (by decide)).trans w19_7c
    have w20_284 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := (K20.w32 (by decide) (by decide)).trans w19_284
    have w20_288 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := (K20.w32 (by decide) (by decide)).trans w19_288
    have w20_3e0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K20.w32 (by decide) (by decide)).trans w19_3e0
    have b20_90 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := (K20.b8 (by decide) (by decide)).trans b19_90
    have b20_3e4 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := (K20.b8 (by decide) (by decide)).trans b19_3e4
    have b20_3e5 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := (K20.b8 (by decide) (by decide)).trans b19_3e5
    have b20_3e6 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := (K20.b8 (by decide) (by decide)).trans b19_3e6
    have b20_3e7 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := (K20.b8 (by decide) (by decide)).trans b19_3e7
    have b20_80 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (1 : BitVec 8) := y0_20
    clear b19_3e7 b19_3e6 b19_3e5 b19_3e4 b19_90 b19_87 b19_86 b19_85 b19_84 w19_3ec w19_3e8 w19_3e0 w19_288 w19_284 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 g19_11 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
    -- 0x226: lbu
    obtain ⟨n21, d21, u21⟩ := s20.lbu E20.self sv_at_226 (off' := 0x22A) (by decide)
    have s21 : St n21.mem SV n21 0x22A (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
    have t21 : Steps n0 n21 := t20.trans (.single d21)
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.same m21
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
    have g21_8 : reg n21 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_8]
    have g21_9 : reg n21 (9 : Fin 32) = tbp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_9]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
    have g21_20 : reg n21 (20 : Fin 32) = dg := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
    have g21_21 : reg n21 (21 : Fin 32) = rootp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = ll := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = sgp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = sgl := by rw [u21.regs, upd_ne (by decide) (by decide), g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = lp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = tbl := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
    have g21_10 : reg n21 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g20_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, b20_80]
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m21]; exact w20_64
    have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m21]; exact w20_68
    have w21_6c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m21]; exact w20_6c
    have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m21]; exact w20_70
    have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m21]; exact w20_74
    have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m21]; exact w20_78
    have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m21]; exact w20_7c
    have w21_284 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m21]; exact w20_284
    have w21_288 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m21]; exact w20_288
    have w21_3e0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m21]; exact w20_3e0
    have b21_80 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (1 : BitVec 8) := by rw [m21]; exact b20_80
    have b21_90 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m21]; exact b20_90
    have b21_3e4 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m21]; exact b20_3e4
    have b21_3e5 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m21]; exact b20_3e5
    have b21_3e6 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m21]; exact b20_3e6
    have b21_3e7 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m21]; exact b20_3e7
    clear b20_80 b20_3e7 b20_3e6 b20_3e5 b20_3e4 b20_90 w20_3e0 w20_288 w20_284 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 y0_20
    -- 0x22A: branch, taken
    obtain ⟨n22, d22, u22⟩ := s21.taken E21.self 0x110 sv_at_22a
      (by decide) (by rw [g21_10, s21.zero]; decide)
    have s22 : St n22.mem SV n22 0x110 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
    have g22_8 : reg n22 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u22.regs, g21_8]
    have g22_9 : reg n22 (9 : Fin 32) = tbp := by rw [u22.regs, g21_9]
    have g22_10 : reg n22 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u22.regs, g21_10]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = dg := by rw [u22.regs, g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = rootp := by rw [u22.regs, g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = ll := by rw [u22.regs, g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = sgp := by rw [u22.regs, g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u22.regs, g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = sgl := by rw [u22.regs, g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = lp := by rw [u22.regs, g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = tbl := by rw [u22.regs, g21_27]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m22]; exact w21_64
    have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m22]; exact w21_68
    have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m22]; exact w21_6c
    have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m22]; exact w21_70
    have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m22]; exact w21_74
    have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m22]; exact w21_78
    have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m22]; exact w21_7c
    have w22_284 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m22]; exact w21_284
    have w22_288 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m22]; exact w21_288
    have w22_3e0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m22]; exact w21_3e0
    have b22_80 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (1 : BitVec 8) := by rw [m22]; exact b21_80
    have b22_90 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m22]; exact b21_90
    have b22_3e4 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m22]; exact b21_3e4
    have b22_3e5 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m22]; exact b21_3e5
    have b22_3e6 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m22]; exact b21_3e6
    have b22_3e7 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m22]; exact b21_3e7
    clear b21_3e7 b21_3e6 b21_3e5 b21_3e4 b21_90 b21_80 w21_3e0 w21_288 w21_284 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 g21_10 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
    -- 0x110: lbu
    obtain ⟨n23, d23, u23⟩ := s22.lbu E22.self sv_at_110 (off' := 0x114) (by decide)
    have s23 : St n23.mem SV n23 0x114 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
    have m23 : n23.mem = n22.mem := u23.mem
    have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
    have t23 : Steps n0 n23 := t22.trans (.single d23)
    have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
    have E23 : SvCode n23.mem := E22.fr F fr23
    have V23 : SvSaves B n23.mem v := V22.same m23
    have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
    have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
    have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
    have g23_9 : reg n23 (9 : Fin 32) = tbp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
    have g23_10 : reg n23 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_10]
    have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
    have g23_20 : reg n23 (20 : Fin 32) = dg := by rw [u23.regs, upd_ne (by decide) (by decide), g22_20]
    have g23_21 : reg n23 (21 : Fin 32) = rootp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
    have g23_22 : reg n23 (22 : Fin 32) = ll := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
    have g23_23 : reg n23 (23 : Fin 32) = sgp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
    have g23_24 : reg n23 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
    have g23_25 : reg n23 (25 : Fin 32) = sgl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
    have g23_26 : reg n23 (26 : Fin 32) = lp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
    have g23_27 : reg n23 (27 : Fin 32) = tbl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
    have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m23]; exact keep_kk22
    clear keep_kk22
    have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m23]; exact w22_64
    have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m23]; exact w22_68
    have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m23]; exact w22_6c
    have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m23]; exact w22_70
    have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m23]; exact w22_74
    have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m23]; exact w22_78
    have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m23]; exact w22_7c
    have w23_284 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m23]; exact w22_284
    have w23_288 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m23]; exact w22_288
    have w23_3e0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m23]; exact w22_3e0
    have b23_80 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (1 : BitVec 8) := by rw [m23]; exact b22_80
    have b23_90 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m23]; exact b22_90
    have b23_3e4 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m23]; exact b22_3e4
    have b23_3e5 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m23]; exact b22_3e5
    have b23_3e6 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m23]; exact b22_3e6
    have b23_3e7 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m23]; exact b22_3e7
    clear b22_3e7 b22_3e6 b22_3e5 b22_3e4 b22_90 b22_80 w22_3e0 w22_288 w22_284 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
    -- 0x114: j
    obtain ⟨n24, d24, u24⟩ := s23.jump E23.self sv_at_114 (off' := 0x7A4) (by decide)
      (by rw [s23.pc]; decide)
    have s24 : St n24.mem SV n24 0x7A4 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
    have m24 : n24.mem = n23.mem := u24.mem
    have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
    have t24 : Steps n0 n24 := t23.trans (.single d24)
    have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
    have E24 : SvCode n24.mem := E23.fr F fr24
    have V24 : SvSaves B n24.mem v := V23.same m24
    have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
    have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
    have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
    have g24_9 : reg n24 (9 : Fin 32) = tbp := by rw [u24.regs, g23_9]
    have g24_10 : reg n24 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u24.regs, g23_10]
    have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
    have g24_20 : reg n24 (20 : Fin 32) = dg := by rw [u24.regs, g23_20]
    have g24_21 : reg n24 (21 : Fin 32) = rootp := by rw [u24.regs, g23_21]
    have g24_22 : reg n24 (22 : Fin 32) = ll := by rw [u24.regs, g23_22]
    have g24_23 : reg n24 (23 : Fin 32) = sgp := by rw [u24.regs, g23_23]
    have g24_24 : reg n24 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u24.regs, g23_24]
    have g24_25 : reg n24 (25 : Fin 32) = sgl := by rw [u24.regs, g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = lp := by rw [u24.regs, g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = tbl := by rw [u24.regs, g23_27]
    have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m24]; exact keep_kk23
    clear keep_kk23
    have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m24]; exact w23_64
    have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m24]; exact w23_68
    have w24_6c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m24]; exact w23_6c
    have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m24]; exact w23_70
    have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m24]; exact w23_74
    have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m24]; exact w23_78
    have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m24]; exact w23_7c
    have w24_284 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m24]; exact w23_284
    have w24_288 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m24]; exact w23_288
    have w24_3e0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m24]; exact w23_3e0
    have b24_80 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (1 : BitVec 8) := by rw [m24]; exact b23_80
    have b24_90 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m24]; exact b23_90
    have b24_3e4 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m24]; exact b23_3e4
    have b24_3e5 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m24]; exact b23_3e5
    have b24_3e6 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m24]; exact b23_3e6
    have b24_3e7 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m24]; exact b23_3e7
    clear b23_3e7 b23_3e6 b23_3e5 b23_3e4 b23_90 b23_80 w23_3e0 w23_288 w23_284 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_10 g23_9 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
    exact .inl ⟨(fun ⟨tl3', h0', tl11', h1', tm20', rs20', h2', _⟩ => by rw [hr3] at h0'; cases h0'; rw [hr11] at h1'; cases h1'; rw [hr20] at h2'; cases h2'), sv_fail F E24 s24 t24 (fun x hx => (fR24 x hx).trans (fM x hx).symm) V24 hret g24_2 g24_18 hO g24_3 g24_4⟩
  obtain ⟨h64_20, y0_20, y8_20, y12_20, kk20, hkk20, d8_20, d12_20, hrb20⟩ := Ok20 tm20 rs20 hr20
  rw [sv_mb fR19 (((tb_in.restW hr3).content hr11).drop hkk20)] at hrb20
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8)] := keep_kk19.trans K20
  clear keep_kk19
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := (K20.w32 (by decide) (by decide)).trans w19_64
  have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := (K20.w32 (by decide) (by decide)).trans w19_68
  have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K20.w32 (by decide) (by decide)).trans w19_6c
  have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K20.w32 (by decide) (by decide)).trans w19_70
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K20.w32 (by decide) (by decide)).trans w19_74
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K20.w32 (by decide) (by decide)).trans w19_78
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K20.w32 (by decide) (by decide)).trans w19_7c
  have w20_284 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := (K20.w32 (by decide) (by decide)).trans w19_284
  have w20_288 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := (K20.w32 (by decide) (by decide)).trans w19_288
  have w20_3e0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K20.w32 (by decide) (by decide)).trans w19_3e0
  have b20_90 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := (K20.b8 (by decide) (by decide)).trans b19_90
  have b20_3e4 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := (K20.b8 (by decide) (by decide)).trans b19_3e4
  have b20_3e5 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := (K20.b8 (by decide) (by decide)).trans b19_3e5
  have b20_3e6 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := (K20.b8 (by decide) (by decide)).trans b19_3e6
  have b20_3e7 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := (K20.b8 (by decide) (by decide)).trans b19_3e7
  have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := y8_20
  have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := y12_20
  have w20_3e8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20 := d8_20
  have w20_3ec : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 ((tl11.len) - kk20) := d12_20
  have b20_80 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := y0_20
  clear b19_3e7 b19_3e6 b19_3e5 b19_3e4 b19_90 b19_87 b19_86 b19_85 b19_84 w19_3ec w19_3e8 w19_3e0 w19_288 w19_284 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 g19_11 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
  -- 0x226: lbu
  obtain ⟨n21, d21, u21⟩ := s20.lbu E20.self sv_at_226 (off' := 0x22A) (by decide)
  have s21 : St n21.mem SV n21 0x22A (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = tbp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = dg := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = rootp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = ll := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = sgp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = sgl := by rw [u21.regs, upd_ne (by decide) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = lp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = tbl := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
  have g21_10 : reg n21 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g20_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, b20_80]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m21]; exact w20_64
  have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m21]; exact w20_68
  have w21_6c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m21]; exact w20_6c
  have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m21]; exact w20_70
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m21]; exact w20_74
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m21]; exact w20_78
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m21]; exact w20_7c
  have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m21]; exact w20_88
  have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m21]; exact w20_8c
  have w21_284 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m21]; exact w20_284
  have w21_288 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m21]; exact w20_288
  have w21_3e0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m21]; exact w20_3e0
  have w21_3e8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20 := by rw [m21]; exact w20_3e8
  have w21_3ec : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 ((tl11.len) - kk20) := by rw [m21]; exact w20_3ec
  have b21_80 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m21]; exact b20_80
  have b21_90 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m21]; exact b20_90
  have b21_3e4 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m21]; exact b20_3e4
  have b21_3e5 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m21]; exact b20_3e5
  have b21_3e6 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m21]; exact b20_3e6
  have b21_3e7 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m21]; exact b20_3e7
  clear b20_80 w20_3ec w20_3e8 w20_8c w20_88 b20_3e7 b20_3e6 b20_3e5 b20_3e4 b20_90 w20_3e0 w20_288 w20_284 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 d12_20 d8_20 y12_20 y8_20 y0_20 g20_2 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 V20 E20 fR20 t20 fr20 Er20 Ok20 K20 rk20 sp20 s20 c20
  -- 0x22A: branch, not taken
  obtain ⟨n22, d22, u22⟩ := s21.notTaken E21.self 0x22E sv_at_22a
    (by decide) (by rw [g21_10, s21.zero]; decide)
  have s22 : St n22.mem SV n22 0x22E (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u22.regs, g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = tbp := by rw [u22.regs, g21_9]
  have g22_10 : reg n22 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u22.regs, g21_10]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = dg := by rw [u22.regs, g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = rootp := by rw [u22.regs, g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = ll := by rw [u22.regs, g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = sgp := by rw [u22.regs, g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u22.regs, g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = sgl := by rw [u22.regs, g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = lp := by rw [u22.regs, g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = tbl := by rw [u22.regs, g21_27]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m22]; exact w21_64
  have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m22]; exact w21_68
  have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m22]; exact w21_6c
  have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m22]; exact w21_70
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m22]; exact w21_74
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m22]; exact w21_78
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m22]; exact w21_7c
  have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m22]; exact w21_88
  have w22_8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m22]; exact w21_8c
  have w22_284 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m22]; exact w21_284
  have w22_288 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m22]; exact w21_288
  have w22_3e0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m22]; exact w21_3e0
  have w22_3e8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20 := by rw [m22]; exact w21_3e8
  have w22_3ec : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 ((tl11.len) - kk20) := by rw [m22]; exact w21_3ec
  have b22_80 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m22]; exact b21_80
  have b22_90 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m22]; exact b21_90
  have b22_3e4 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m22]; exact b21_3e4
  have b22_3e5 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m22]; exact b21_3e5
  have b22_3e6 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m22]; exact b21_3e6
  have b22_3e7 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m22]; exact b21_3e7
  clear b21_3e7 b21_3e6 b21_3e5 b21_3e4 b21_90 b21_80 w21_3ec w21_3e8 w21_3e0 w21_288 w21_284 w21_8c w21_88 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 g21_10 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
  -- 0x22E: lw
  obtain ⟨n23, d23, u23⟩ := s22.lw E22.self sv_at_22e (off' := 0x230) (by decide)
    (by rw [g22_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s23 : St n23.mem SV n23 0x230 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = tbp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = dg := by rw [u23.regs, upd_ne (by decide) (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = rootp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = ll := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = sgp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = sgl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = lp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = tbl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
  have g23_10 : reg n23 a0 = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by
    rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g22_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr, w22_88]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m23]; exact w22_64
  have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m23]; exact w22_68
  have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m23]; exact w22_6c
  have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m23]; exact w22_70
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m23]; exact w22_74
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m23]; exact w22_78
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m23]; exact w22_7c
  have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m23]; exact w22_88
  have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m23]; exact w22_8c
  have w23_284 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m23]; exact w22_284
  have w23_288 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m23]; exact w22_288
  have w23_3e0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m23]; exact w22_3e0
  have w23_3e8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20 := by rw [m23]; exact w22_3e8
  have w23_3ec : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 ((tl11.len) - kk20) := by rw [m23]; exact w22_3ec
  have b23_80 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m23]; exact b22_80
  have b23_90 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m23]; exact b22_90
  have b23_3e4 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m23]; exact b22_3e4
  have b23_3e5 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m23]; exact b22_3e5
  have b23_3e6 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m23]; exact b22_3e6
  have b23_3e7 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m23]; exact b22_3e7
  clear b22_3e7 b22_3e6 b22_3e5 b22_3e4 b22_90 b22_80 w22_3ec w22_3e8 w22_3e0 w22_288 w22_284 w22_8c w22_88 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  -- 0x230: sw
  obtain ⟨n24, d24, s24, fr24, K24, W24, rg24⟩ := sv_sw F E23 s23 sv_at_230 (off' := 0x232) (c := 0x60)
    (by decide) (by rw [g23_2]; sv_addr) (by decide) (by decide)
  have t24 : Steps n0 n24 := t23.trans d24
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.keep K24 (by decide)
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [rg24 sp, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg24 (3 : Fin 32), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg24 (4 : Fin 32), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg24 (8 : Fin 32), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = tbp := by rw [rg24 (9 : Fin 32), g23_9]
  have g24_10 : reg n24 a0 = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [rg24 a0, g23_10]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [rg24 (18 : Fin 32), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [rg24 (19 : Fin 32), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = dg := by rw [rg24 (20 : Fin 32), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = rootp := by rw [rg24 (21 : Fin 32), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = ll := by rw [rg24 (22 : Fin 32), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = sgp := by rw [rg24 (23 : Fin 32), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [rg24 (24 : Fin 32), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = sgl := by rw [rg24 (25 : Fin 32), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = lp := by rw [rg24 (26 : Fin 32), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = tbl := by rw [rg24 (27 : Fin 32), g23_27]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4)] := keep_kk23.trans K24.toL
  clear keep_kk23
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := (K24.w32 (by decide) (by decide)).trans w23_64
  have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := (K24.w32 (by decide) (by decide)).trans w23_68
  have w24_6c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K24.w32 (by decide) (by decide)).trans w23_6c
  have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K24.w32 (by decide) (by decide)).trans w23_70
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K24.w32 (by decide) (by decide)).trans w23_74
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K24.w32 (by decide) (by decide)).trans w23_78
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K24.w32 (by decide) (by decide)).trans w23_7c
  have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := (K24.w32 (by decide) (by decide)).trans w23_88
  have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := (K24.w32 (by decide) (by decide)).trans w23_8c
  have w24_284 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := (K24.w32 (by decide) (by decide)).trans w23_284
  have w24_288 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := (K24.w32 (by decide) (by decide)).trans w23_288
  have w24_3e0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K24.w32 (by decide) (by decide)).trans w23_3e0
  have w24_3e8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20 := (K24.w32 (by decide) (by decide)).trans w23_3e8
  have w24_3ec : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 ((tl11.len) - kk20) := (K24.w32 (by decide) (by decide)).trans w23_3ec
  have b24_80 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := (K24.b8 (by decide) (by decide)).trans b23_80
  have b24_90 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := (K24.b8 (by decide) (by decide)).trans b23_90
  have b24_3e4 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := (K24.b8 (by decide) (by decide)).trans b23_3e4
  have b24_3e5 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := (K24.b8 (by decide) (by decide)).trans b23_3e5
  have b24_3e6 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := (K24.b8 (by decide) (by decide)).trans b23_3e6
  have b24_3e7 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := (K24.b8 (by decide) (by decide)).trans b23_3e7
  have w24_60 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [W24, g23_10]
  clear b23_3e7 b23_3e6 b23_3e5 b23_3e4 b23_90 b23_80 w23_3ec w23_3e8 w23_3e0 w23_288 w23_284 w23_8c w23_88 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 g23_10 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  -- 0x232: lw
  obtain ⟨n25, d25, u25⟩ := s24.lw E24.self sv_at_232 (off' := 0x234) (by decide)
    (by rw [g24_2, show B + 0x21A0 + 0x8C = B + 0x21A0 + BitVec.ofNat 32 0x8C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s25 : St n25.mem SV n25 0x234 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans (.single d25)
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = tbp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, upd_ne (by decide) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = dg := by rw [u25.regs, upd_ne (by decide) (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = rootp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = ll := by rw [u25.regs, upd_ne (by decide) (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = sgp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u25.regs, upd_ne (by decide) (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = sgl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = lp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = tbl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_27]
  have g25_10 : reg n25 a0 = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by
    rw [u25.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g24_2, show B + 0x21A0 + 0x8C = B + 0x21A0 + BitVec.ofNat 32 0x8C by sv_addr, w24_8c]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_60 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m25]; exact w24_60
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m25]; exact w24_64
  have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m25]; exact w24_68
  have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m25]; exact w24_6c
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m25]; exact w24_70
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m25]; exact w24_74
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m25]; exact w24_78
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m25]; exact w24_7c
  have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m25]; exact w24_88
  have w25_8c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m25]; exact w24_8c
  have w25_284 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m25]; exact w24_284
  have w25_288 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m25]; exact w24_288
  have w25_3e0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m25]; exact w24_3e0
  have w25_3e8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20 := by rw [m25]; exact w24_3e8
  have w25_3ec : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 ((tl11.len) - kk20) := by rw [m25]; exact w24_3ec
  have b25_80 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m25]; exact b24_80
  have b25_90 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m25]; exact b24_90
  have b25_3e4 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m25]; exact b24_3e4
  have b25_3e5 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m25]; exact b24_3e5
  have b25_3e6 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m25]; exact b24_3e6
  have b25_3e7 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m25]; exact b24_3e7
  clear w24_60 b24_3e7 b24_3e6 b24_3e5 b24_3e4 b24_90 b24_80 w24_3ec w24_3e8 w24_3e0 w24_288 w24_284 w24_8c w24_88 w24_7c w24_78 w24_74 w24_70 w24_6c w24_68 w24_64 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 rg24 W24 K24 fr24 s24 d24
  -- 0x234: sw
  obtain ⟨n26, d26, s26, fr26, K26, W26, rg26⟩ := sv_sw F E25 s25 sv_at_234 (off' := 0x236) (c := 0x5C)
    (by decide) (by rw [g25_2]; sv_addr) (by decide) (by decide)
  have t26 : Steps n0 n26 := t25.trans d26
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.keep K26 (by decide)
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [rg26 sp, g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg26 (3 : Fin 32), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg26 (4 : Fin 32), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg26 (8 : Fin 32), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = tbp := by rw [rg26 (9 : Fin 32), g25_9]
  have g26_10 : reg n26 a0 = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [rg26 a0, g25_10]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [rg26 (18 : Fin 32), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [rg26 (19 : Fin 32), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = dg := by rw [rg26 (20 : Fin 32), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = rootp := by rw [rg26 (21 : Fin 32), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = ll := by rw [rg26 (22 : Fin 32), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = sgp := by rw [rg26 (23 : Fin 32), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [rg26 (24 : Fin 32), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = sgl := by rw [rg26 (25 : Fin 32), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = lp := by rw [rg26 (26 : Fin 32), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = tbl := by rw [rg26 (27 : Fin 32), g25_27]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4)] := keep_kk25.trans K26.toL
  clear keep_kk25
  have w26_60 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := (K26.w32 (by decide) (by decide)).trans w25_60
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := (K26.w32 (by decide) (by decide)).trans w25_64
  have w26_68 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := (K26.w32 (by decide) (by decide)).trans w25_68
  have w26_6c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K26.w32 (by decide) (by decide)).trans w25_6c
  have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K26.w32 (by decide) (by decide)).trans w25_70
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K26.w32 (by decide) (by decide)).trans w25_74
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K26.w32 (by decide) (by decide)).trans w25_78
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K26.w32 (by decide) (by decide)).trans w25_7c
  have w26_88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := (K26.w32 (by decide) (by decide)).trans w25_88
  have w26_8c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := (K26.w32 (by decide) (by decide)).trans w25_8c
  have w26_284 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := (K26.w32 (by decide) (by decide)).trans w25_284
  have w26_288 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := (K26.w32 (by decide) (by decide)).trans w25_288
  have w26_3e0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K26.w32 (by decide) (by decide)).trans w25_3e0
  have w26_3e8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20 := (K26.w32 (by decide) (by decide)).trans w25_3e8
  have w26_3ec : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 ((tl11.len) - kk20) := (K26.w32 (by decide) (by decide)).trans w25_3ec
  have b26_80 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := (K26.b8 (by decide) (by decide)).trans b25_80
  have b26_90 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := (K26.b8 (by decide) (by decide)).trans b25_90
  have b26_3e4 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := (K26.b8 (by decide) (by decide)).trans b25_3e4
  have b26_3e5 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := (K26.b8 (by decide) (by decide)).trans b25_3e5
  have b26_3e6 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := (K26.b8 (by decide) (by decide)).trans b25_3e6
  have b26_3e7 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := (K26.b8 (by decide) (by decide)).trans b25_3e7
  have w26_5c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [W26, g25_10]
  clear b25_3e7 b25_3e6 b25_3e5 b25_3e4 b25_90 b25_80 w25_3ec w25_3e8 w25_3e0 w25_288 w25_284 w25_8c w25_88 w25_7c w25_78 w25_74 w25_70 w25_6c w25_68 w25_64 w25_60 g25_10 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
  -- 0x236
  obtain ⟨n27, c27, u27⟩ := s26.block svL4236 E26.self svL4236_end
    ⟨trivial, trivial, trivial⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have s27 : St n27.mem SV n27 0x23A (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have rb27 : ∀ q, reg n27 q = (runBlock svL4236 (n26.mem, reg n26)).2 q := fun q => by rw [u27.regs]
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans c27
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by
    rw [rb27, runBlock_reg _ _ _ sp s26.zero (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb27, runBlock_reg _ _ _ (3 : Fin 32) s26.zero (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb27, runBlock_reg _ _ _ (4 : Fin 32) s26.zero (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb27, runBlock_reg _ _ _ (8 : Fin 32) s26.zero (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = tbp := by
    rw [rb27, runBlock_reg _ _ _ (9 : Fin 32) s26.zero (by decide), g26_9]
  have g27_18 : reg n27 (18 : Fin 32) = out := by
    rw [rb27, runBlock_reg _ _ _ (18 : Fin 32) s26.zero (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by
    rw [rb27, runBlock_reg _ _ _ (19 : Fin 32) s26.zero (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = dg := by
    rw [rb27, runBlock_reg _ _ _ (20 : Fin 32) s26.zero (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = rootp := by
    rw [rb27, runBlock_reg _ _ _ (21 : Fin 32) s26.zero (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = ll := by
    rw [rb27, runBlock_reg _ _ _ (22 : Fin 32) s26.zero (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = sgp := by
    rw [rb27, runBlock_reg _ _ _ (23 : Fin 32) s26.zero (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by
    rw [rb27, runBlock_reg _ _ _ (24 : Fin 32) s26.zero (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = sgl := by
    rw [rb27, runBlock_reg _ _ _ (25 : Fin 32) s26.zero (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = lp := by
    rw [rb27, runBlock_reg _ _ _ (26 : Fin 32) s26.zero (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = tbl := by
    rw [rb27, runBlock_reg _ _ _ (27 : Fin 32) s26.zero (by decide), g26_27]
  have g27_10 : reg n27 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svL4236, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_10, g26_18, g26_19, g26_20, g26_21, g26_22, g26_23, g26_24, g26_25, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g27_11 : reg n27 a1 = B + 0x21A0 + BitVec.ofNat 32 0x3E0 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svL4236, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_10, g26_18, g26_19, g26_20, g26_21, g26_22, g26_23, g26_24, g26_25, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_5c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m27]; exact w26_5c
  have w27_60 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m27]; exact w26_60
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m27]; exact w26_64
  have w27_68 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m27]; exact w26_68
  have w27_6c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m27]; exact w26_6c
  have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m27]; exact w26_70
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m27]; exact w26_74
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m27]; exact w26_78
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m27]; exact w26_7c
  have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m27]; exact w26_88
  have w27_8c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m27]; exact w26_8c
  have w27_284 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m27]; exact w26_284
  have w27_288 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m27]; exact w26_288
  have w27_3e0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m27]; exact w26_3e0
  have w27_3e8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20 := by rw [m27]; exact w26_3e8
  have w27_3ec : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 ((tl11.len) - kk20) := by rw [m27]; exact w26_3ec
  have b27_80 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m27]; exact b26_80
  have b27_90 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m27]; exact b26_90
  have b27_3e4 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m27]; exact b26_3e4
  have b27_3e5 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m27]; exact b26_3e5
  have b27_3e6 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m27]; exact b26_3e6
  have b27_3e7 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m27]; exact b26_3e7
  clear w26_5c b26_3e7 b26_3e6 b26_3e5 b26_3e4 b26_90 b26_80 w26_3ec w26_3e8 w26_3e0 w26_288 w26_284 w26_8c w26_88 w26_7c w26_78 w26_74 w26_70 w26_6c w26_68 w26_64 w26_60 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_10 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 rg26 W26 K26 fr26 s26 d26
  -- 0x23A: sv_rtF
  obtain ⟨n28, c28, s28, sp28, rk28, K28, Ok28, Er28, fr28⟩ := sv_rtF (oc := 0x80) (dc := 0x3E0) (rl := (tl11.len) - kk20)
    F E27 s27 sv_at_23a sv_at_23e (by decide) (by decide) g27_2 g27_10 g27_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w27_3e8 w27_3ec (((tb_in.restW hr3).content hr11).drop hkk20)
  have t28 : Steps n0 n28 := t27.trans c28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.keepL K28 (by decide)
  rw [sv_mb fR27 (((tb_in.restW hr3).content hr11).drop hkk20)] at Ok28 Er28
  rw [← hrb20] at Ok28 Er28
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk28 (3 : Fin 32) (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk28 (4 : Fin 32) (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk28 (8 : Fin 32) (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = tbp := by rw [rk28 (9 : Fin 32) (by decide), g27_9]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [rk28 (18 : Fin 32) (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [rk28 (19 : Fin 32) (by decide), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = dg := by rw [rk28 (20 : Fin 32) (by decide), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = rootp := by rw [rk28 (21 : Fin 32) (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = ll := by rw [rk28 (22 : Fin 32) (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = sgp := by rw [rk28 (23 : Fin 32) (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [rk28 (24 : Fin 32) (by decide), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = sgl := by rw [rk28 (25 : Fin 32) (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = lp := by rw [rk28 (26 : Fin 32) (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = tbl := by rw [rk28 (27 : Fin 32) (by decide), g27_27]
  have g28_2 : reg n28 sp = B + 0x21A0 := sp28
  obtain ⟨r28, hr28⟩ : ∃ r, readTime rs20 = r := ⟨_, rfl⟩
  rcases r28 with _ | ⟨tm28, rs28⟩
  · have y0_28 := Er28 hr28
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8)] := keep_kk27.trans K28
    clear keep_kk27
    have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := (K28.w32 (by decide) (by decide)).trans w27_5c
    have w28_60 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := (K28.w32 (by decide) (by decide)).trans w27_60
    have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := (K28.w32 (by decide) (by decide)).trans w27_64
    have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := (K28.w32 (by decide) (by decide)).trans w27_68
    have w28_6c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K28.w32 (by decide) (by decide)).trans w27_6c
    have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K28.w32 (by decide) (by decide)).trans w27_70
    have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K28.w32 (by decide) (by decide)).trans w27_74
    have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K28.w32 (by decide) (by decide)).trans w27_78
    have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K28.w32 (by decide) (by decide)).trans w27_7c
    have w28_284 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := (K28.w32 (by decide) (by decide)).trans w27_284
    have w28_288 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := (K28.w32 (by decide) (by decide)).trans w27_288
    have w28_3e0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K28.w32 (by decide) (by decide)).trans w27_3e0
    have b28_90 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := (K28.b8 (by decide) (by decide)).trans b27_90
    have b28_3e4 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_3e4
    have b28_3e5 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := (K28.b8 (by decide) (by decide)).trans b27_3e5
    have b28_3e6 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := (K28.b8 (by decide) (by decide)).trans b27_3e6
    have b28_3e7 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := (K28.b8 (by decide) (by decide)).trans b27_3e7
    have b28_80 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (1 : BitVec 8) := y0_28
    clear b27_3e7 b27_3e6 b27_3e5 b27_3e4 b27_90 b27_80 w27_3ec w27_3e8 w27_3e0 w27_288 w27_284 w27_8c w27_88 w27_7c w27_78 w27_74 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c g27_11 g27_10 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
    -- 0x242: lbu
    obtain ⟨n29, d29, u29⟩ := s28.lbu E28.self sv_at_242 (off' := 0x246) (by decide)
    have s29 : St n29.mem SV n29 0x246 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
    have t29 : Steps n0 n29 := t28.trans (.single d29)
    have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
    have E29 : SvCode n29.mem := E28.fr F fr29
    have V29 : SvSaves B n29.mem v := V28.same m29
    have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
    have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
    have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
    have g29_8 : reg n29 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = tbp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = dg := by rw [u29.regs, upd_ne (by decide) (by decide), g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = rootp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = ll := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = sgp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = sgl := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = lp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = tbl := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
    have g29_10 : reg n29 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g28_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, b28_80]
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_5c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m29]; exact w28_5c
    have w29_60 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m29]; exact w28_60
    have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m29]; exact w28_64
    have w29_68 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m29]; exact w28_68
    have w29_6c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m29]; exact w28_6c
    have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m29]; exact w28_70
    have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m29]; exact w28_74
    have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m29]; exact w28_78
    have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m29]; exact w28_7c
    have w29_284 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m29]; exact w28_284
    have w29_288 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m29]; exact w28_288
    have w29_3e0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m29]; exact w28_3e0
    have b29_80 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (1 : BitVec 8) := by rw [m29]; exact b28_80
    have b29_90 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m29]; exact b28_90
    have b29_3e4 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m29]; exact b28_3e4
    have b29_3e5 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m29]; exact b28_3e5
    have b29_3e6 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m29]; exact b28_3e6
    have b29_3e7 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m29]; exact b28_3e7
    clear b28_80 b28_3e7 b28_3e6 b28_3e5 b28_3e4 b28_90 w28_3e0 w28_288 w28_284 w28_7c w28_78 w28_74 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c y0_28
    -- 0x246: branch, taken
    obtain ⟨n30, d30, u30⟩ := s29.taken E29.self 0x110 sv_at_246
      (by decide) (by rw [g29_10, s29.zero]; decide)
    have s30 : St n30.mem SV n30 0x110 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
    have m30 : n30.mem = n29.mem := u30.mem
    have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
    have t30 : Steps n0 n30 := t29.trans (.single d30)
    have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.same m30
    have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
    have g30_8 : reg n30 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u30.regs, g29_8]
    have g30_9 : reg n30 (9 : Fin 32) = tbp := by rw [u30.regs, g29_9]
    have g30_10 : reg n30 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u30.regs, g29_10]
    have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
    have g30_20 : reg n30 (20 : Fin 32) = dg := by rw [u30.regs, g29_20]
    have g30_21 : reg n30 (21 : Fin 32) = rootp := by rw [u30.regs, g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = ll := by rw [u30.regs, g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = sgp := by rw [u30.regs, g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u30.regs, g29_24]
    have g30_25 : reg n30 (25 : Fin 32) = sgl := by rw [u30.regs, g29_25]
    have g30_26 : reg n30 (26 : Fin 32) = lp := by rw [u30.regs, g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = tbl := by rw [u30.regs, g29_27]
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m30]; exact keep_kk29
    clear keep_kk29
    have w30_5c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m30]; exact w29_5c
    have w30_60 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m30]; exact w29_60
    have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m30]; exact w29_64
    have w30_68 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m30]; exact w29_68
    have w30_6c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m30]; exact w29_6c
    have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m30]; exact w29_70
    have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m30]; exact w29_74
    have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m30]; exact w29_78
    have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m30]; exact w29_7c
    have w30_284 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m30]; exact w29_284
    have w30_288 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m30]; exact w29_288
    have w30_3e0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m30]; exact w29_3e0
    have b30_80 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (1 : BitVec 8) := by rw [m30]; exact b29_80
    have b30_90 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m30]; exact b29_90
    have b30_3e4 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m30]; exact b29_3e4
    have b30_3e5 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m30]; exact b29_3e5
    have b30_3e6 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m30]; exact b29_3e6
    have b30_3e7 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m30]; exact b29_3e7
    clear b29_3e7 b29_3e6 b29_3e5 b29_3e4 b29_90 b29_80 w29_3e0 w29_288 w29_284 w29_7c w29_78 w29_74 w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
    -- 0x110: lbu
    obtain ⟨n31, d31, u31⟩ := s30.lbu E30.self sv_at_110 (off' := 0x114) (by decide)
    have s31 : St n31.mem SV n31 0x114 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
    have t31 : Steps n0 n31 := t30.trans (.single d31)
    have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
    have E31 : SvCode n31.mem := E30.fr F fr31
    have V31 : SvSaves B n31.mem v := V30.same m31
    have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
    have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
    have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
    have g31_9 : reg n31 (9 : Fin 32) = tbp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_9]
    have g31_10 : reg n31 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_10]
    have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, upd_ne (by decide) (by decide), g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = dg := by rw [u31.regs, upd_ne (by decide) (by decide), g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = rootp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = ll := by rw [u31.regs, upd_ne (by decide) (by decide), g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = sgp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u31.regs, upd_ne (by decide) (by decide), g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = sgl := by rw [u31.regs, upd_ne (by decide) (by decide), g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = lp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = tbl := by rw [u31.regs, upd_ne (by decide) (by decide), g30_27]
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_5c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m31]; exact w30_5c
    have w31_60 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m31]; exact w30_60
    have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m31]; exact w30_64
    have w31_68 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m31]; exact w30_68
    have w31_6c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m31]; exact w30_6c
    have w31_70 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m31]; exact w30_70
    have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m31]; exact w30_74
    have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m31]; exact w30_78
    have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m31]; exact w30_7c
    have w31_284 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m31]; exact w30_284
    have w31_288 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m31]; exact w30_288
    have w31_3e0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m31]; exact w30_3e0
    have b31_80 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (1 : BitVec 8) := by rw [m31]; exact b30_80
    have b31_90 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m31]; exact b30_90
    have b31_3e4 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m31]; exact b30_3e4
    have b31_3e5 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m31]; exact b30_3e5
    have b31_3e6 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m31]; exact b30_3e6
    have b31_3e7 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m31]; exact b30_3e7
    clear b30_3e7 b30_3e6 b30_3e5 b30_3e4 b30_90 b30_80 w30_3e0 w30_288 w30_284 w30_7c w30_78 w30_74 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
    -- 0x114: j
    obtain ⟨n32, d32, u32⟩ := s31.jump E31.self sv_at_114 (off' := 0x7A4) (by decide)
      (by rw [s31.pc]; decide)
    have s32 : St n32.mem SV n32 0x7A4 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
    have g32_9 : reg n32 (9 : Fin 32) = tbp := by rw [u32.regs, g31_9]
    have g32_10 : reg n32 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u32.regs, g31_10]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = dg := by rw [u32.regs, g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = rootp := by rw [u32.regs, g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = ll := by rw [u32.regs, g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = sgp := by rw [u32.regs, g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u32.regs, g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = sgl := by rw [u32.regs, g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = lp := by rw [u32.regs, g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = tbl := by rw [u32.regs, g31_27]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m32]; exact w31_5c
    have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m32]; exact w31_60
    have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m32]; exact w31_64
    have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m32]; exact w31_68
    have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m32]; exact w31_6c
    have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m32]; exact w31_70
    have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m32]; exact w31_74
    have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m32]; exact w31_78
    have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m32]; exact w31_7c
    have w32_284 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m32]; exact w31_284
    have w32_288 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m32]; exact w31_288
    have w32_3e0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m32]; exact w31_3e0
    have b32_80 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (1 : BitVec 8) := by rw [m32]; exact b31_80
    have b32_90 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m32]; exact b31_90
    have b32_3e4 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m32]; exact b31_3e4
    have b32_3e5 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m32]; exact b31_3e5
    have b32_3e6 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m32]; exact b31_3e6
    have b32_3e7 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m32]; exact b31_3e7
    clear b31_3e7 b31_3e6 b31_3e5 b31_3e4 b31_90 b31_80 w31_3e0 w31_288 w31_284 w31_7c w31_78 w31_74 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_10 g31_9 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
    exact .inl ⟨(fun ⟨tl3', h0', tl11', h1', tm20', rs20', h2', tm28', rs28', h3', _⟩ => by rw [hr3] at h0'; cases h0'; rw [hr11] at h1'; cases h1'; rw [hr20] at h2'; cases h2'; rw [hr28] at h3'; cases h3'), sv_fail F E32 s32 t32 (fun x hx => (fR32 x hx).trans (fM x hx).symm) V32 hret g32_2 g32_18 hO g32_3 g32_4⟩
  obtain ⟨h64_28, y0_28, y8_28, y12_28, kk28, hkk28, d8_28, d12_28, hrb28⟩ := Ok28 tm28 rs28 hr28
  rw [sv_mb fR27 ((((tb_in.restW hr3).content hr11).drop hkk20).drop hkk28)] at hrb28
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8)] := keep_kk27.trans K28
  clear keep_kk27
  have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := (K28.w32 (by decide) (by decide)).trans w27_5c
  have w28_60 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := (K28.w32 (by decide) (by decide)).trans w27_60
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := (K28.w32 (by decide) (by decide)).trans w27_64
  have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := (K28.w32 (by decide) (by decide)).trans w27_68
  have w28_6c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K28.w32 (by decide) (by decide)).trans w27_6c
  have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K28.w32 (by decide) (by decide)).trans w27_70
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K28.w32 (by decide) (by decide)).trans w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K28.w32 (by decide) (by decide)).trans w27_78
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K28.w32 (by decide) (by decide)).trans w27_7c
  have w28_284 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := (K28.w32 (by decide) (by decide)).trans w27_284
  have w28_288 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := (K28.w32 (by decide) (by decide)).trans w27_288
  have w28_3e0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K28.w32 (by decide) (by decide)).trans w27_3e0
  have b28_90 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := (K28.b8 (by decide) (by decide)).trans b27_90
  have b28_3e4 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_3e4
  have b28_3e5 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := (K28.b8 (by decide) (by decide)).trans b27_3e5
  have b28_3e6 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := (K28.b8 (by decide) (by decide)).trans b27_3e6
  have b28_3e7 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := (K28.b8 (by decide) (by decide)).trans b27_3e7
  have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm28 % 2 ^ 32) := y8_28
  have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm28 / 2 ^ 32) := y12_28
  have w28_3e8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20) + BitVec.ofNat 32 kk28 := d8_28
  have w28_3ec : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := d12_28
  have b28_80 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := y0_28
  clear b27_3e7 b27_3e6 b27_3e5 b27_3e4 b27_90 b27_80 w27_3ec w27_3e8 w27_3e0 w27_288 w27_284 w27_8c w27_88 w27_7c w27_78 w27_74 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c g27_11 g27_10 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
  -- 0x242: lbu
  obtain ⟨n29, d29, u29⟩ := s28.lbu E28.self sv_at_242 (off' := 0x246) (by decide)
  have s29 : St n29.mem SV n29 0x246 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = tbp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = dg := by rw [u29.regs, upd_ne (by decide) (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = rootp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = ll := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = sgp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = sgl := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = lp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = tbl := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
  have g29_10 : reg n29 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g28_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, b28_80]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_5c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m29]; exact w28_5c
  have w29_60 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m29]; exact w28_60
  have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m29]; exact w28_64
  have w29_68 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m29]; exact w28_68
  have w29_6c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m29]; exact w28_6c
  have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m29]; exact w28_70
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m29]; exact w28_74
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m29]; exact w28_78
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m29]; exact w28_7c
  have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm28 % 2 ^ 32) := by rw [m29]; exact w28_88
  have w29_8c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm28 / 2 ^ 32) := by rw [m29]; exact w28_8c
  have w29_284 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m29]; exact w28_284
  have w29_288 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m29]; exact w28_288
  have w29_3e0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m29]; exact w28_3e0
  have w29_3e8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20) + BitVec.ofNat 32 kk28 := by rw [m29]; exact w28_3e8
  have w29_3ec : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := by rw [m29]; exact w28_3ec
  have b29_80 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m29]; exact b28_80
  have b29_90 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m29]; exact b28_90
  have b29_3e4 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m29]; exact b28_3e4
  have b29_3e5 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m29]; exact b28_3e5
  have b29_3e6 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m29]; exact b28_3e6
  have b29_3e7 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m29]; exact b28_3e7
  clear b28_80 w28_3ec w28_3e8 w28_8c w28_88 b28_3e7 b28_3e6 b28_3e5 b28_3e4 b28_90 w28_3e0 w28_288 w28_284 w28_7c w28_78 w28_74 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c d12_28 d8_28 y12_28 y8_28 y0_28 g28_2 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 V28 E28 fR28 t28 fr28 Er28 Ok28 K28 rk28 sp28 s28 c28
  -- 0x246: branch, not taken
  obtain ⟨n30, d30, u30⟩ := s29.notTaken E29.self 0x24A sv_at_246
    (by decide) (by rw [g29_10, s29.zero]; decide)
  have s30 : St n30.mem SV n30 0x24A (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans (.single d30)
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u30.regs, g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = tbp := by rw [u30.regs, g29_9]
  have g30_10 : reg n30 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u30.regs, g29_10]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = dg := by rw [u30.regs, g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = rootp := by rw [u30.regs, g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = ll := by rw [u30.regs, g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = sgp := by rw [u30.regs, g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u30.regs, g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = sgl := by rw [u30.regs, g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = lp := by rw [u30.regs, g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = tbl := by rw [u30.regs, g29_27]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m30]; exact keep_kk29
  clear keep_kk29
  have w30_5c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m30]; exact w29_5c
  have w30_60 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m30]; exact w29_60
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m30]; exact w29_64
  have w30_68 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m30]; exact w29_68
  have w30_6c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m30]; exact w29_6c
  have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m30]; exact w29_70
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m30]; exact w29_74
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m30]; exact w29_78
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m30]; exact w29_7c
  have w30_88 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm28 % 2 ^ 32) := by rw [m30]; exact w29_88
  have w30_8c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm28 / 2 ^ 32) := by rw [m30]; exact w29_8c
  have w30_284 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m30]; exact w29_284
  have w30_288 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m30]; exact w29_288
  have w30_3e0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m30]; exact w29_3e0
  have w30_3e8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20) + BitVec.ofNat 32 kk28 := by rw [m30]; exact w29_3e8
  have w30_3ec : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := by rw [m30]; exact w29_3ec
  have b30_80 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m30]; exact b29_80
  have b30_90 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m30]; exact b29_90
  have b30_3e4 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m30]; exact b29_3e4
  have b30_3e5 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m30]; exact b29_3e5
  have b30_3e6 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m30]; exact b29_3e6
  have b30_3e7 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m30]; exact b29_3e7
  clear b29_3e7 b29_3e6 b29_3e5 b29_3e4 b29_90 b29_80 w29_3ec w29_3e8 w29_3e0 w29_288 w29_284 w29_8c w29_88 w29_7c w29_78 w29_74 w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
  -- 0x24A: lw
  obtain ⟨n31, d31, u31⟩ := s30.lw E30.self sv_at_24a (off' := 0x24E) (by decide)
    (by rw [g30_2, show B + 0x21A0 + 0x3EC = B + 0x21A0 + BitVec.ofNat 32 0x3EC by sv_addr]; exact sv_al F (by decide) (by decide))
  have s31 : St n31.mem SV n31 0x24E (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = tbp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_9]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, upd_ne (by decide) (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = dg := by rw [u31.regs, upd_ne (by decide) (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = rootp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = ll := by rw [u31.regs, upd_ne (by decide) (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = sgp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u31.regs, upd_ne (by decide) (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = sgl := by rw [u31.regs, upd_ne (by decide) (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = lp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = tbl := by rw [u31.regs, upd_ne (by decide) (by decide), g30_27]
  have g31_10 : reg n31 a0 = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := by
    rw [u31.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g30_2, show B + 0x21A0 + 0x3EC = B + 0x21A0 + BitVec.ofNat 32 0x3EC by sv_addr, w30_3ec]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_5c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m31]; exact w30_5c
  have w31_60 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m31]; exact w30_60
  have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m31]; exact w30_64
  have w31_68 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m31]; exact w30_68
  have w31_6c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m31]; exact w30_6c
  have w31_70 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m31]; exact w30_70
  have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m31]; exact w30_74
  have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m31]; exact w30_78
  have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m31]; exact w30_7c
  have w31_88 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm28 % 2 ^ 32) := by rw [m31]; exact w30_88
  have w31_8c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm28 / 2 ^ 32) := by rw [m31]; exact w30_8c
  have w31_284 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m31]; exact w30_284
  have w31_288 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m31]; exact w30_288
  have w31_3e0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m31]; exact w30_3e0
  have w31_3e8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20) + BitVec.ofNat 32 kk28 := by rw [m31]; exact w30_3e8
  have w31_3ec : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := by rw [m31]; exact w30_3ec
  have b31_80 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m31]; exact b30_80
  have b31_90 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m31]; exact b30_90
  have b31_3e4 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m31]; exact b30_3e4
  have b31_3e5 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m31]; exact b30_3e5
  have b31_3e6 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m31]; exact b30_3e6
  have b31_3e7 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m31]; exact b30_3e7
  clear b30_3e7 b30_3e6 b30_3e5 b30_3e4 b30_90 b30_80 w30_3ec w30_3e8 w30_3e0 w30_288 w30_284 w30_8c w30_88 w30_7c w30_78 w30_74 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
  by_cases hz_31 : rs28 = []
  rotate_left
  · -- 0x24E: branch, taken
    obtain ⟨n32, d32, u32⟩ := s31.taken E31.self 0x14C sv_at_24e
      (by decide) (by rw [g31_10, s31.zero]; exact br_bne_t (rest_ne (by have := ((((tb_in.restW hr3).content hr11).drop hkk20).drop hkk28).fit; omega) hrb28 hz_31))
    have s32 : St n32.mem SV n32 0x14C (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
    have g32_8 : reg n32 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u32.regs, g31_8]
    have g32_9 : reg n32 (9 : Fin 32) = tbp := by rw [u32.regs, g31_9]
    have g32_10 : reg n32 a0 = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := by rw [u32.regs, g31_10]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = dg := by rw [u32.regs, g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = rootp := by rw [u32.regs, g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = ll := by rw [u32.regs, g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = sgp := by rw [u32.regs, g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u32.regs, g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = sgl := by rw [u32.regs, g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = lp := by rw [u32.regs, g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = tbl := by rw [u32.regs, g31_27]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m32]; exact w31_5c
    have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m32]; exact w31_60
    have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m32]; exact w31_64
    have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m32]; exact w31_68
    have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m32]; exact w31_6c
    have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m32]; exact w31_70
    have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m32]; exact w31_74
    have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m32]; exact w31_78
    have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m32]; exact w31_7c
    have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm28 % 2 ^ 32) := by rw [m32]; exact w31_88
    have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm28 / 2 ^ 32) := by rw [m32]; exact w31_8c
    have w32_284 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m32]; exact w31_284
    have w32_288 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m32]; exact w31_288
    have w32_3e0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m32]; exact w31_3e0
    have w32_3e8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20) + BitVec.ofNat 32 kk28 := by rw [m32]; exact w31_3e8
    have w32_3ec : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := by rw [m32]; exact w31_3ec
    have b32_80 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m32]; exact b31_80
    have b32_90 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m32]; exact b31_90
    have b32_3e4 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m32]; exact b31_3e4
    have b32_3e5 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m32]; exact b31_3e5
    have b32_3e6 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m32]; exact b31_3e6
    have b32_3e7 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m32]; exact b31_3e7
    clear b31_3e7 b31_3e6 b31_3e5 b31_3e4 b31_90 b31_80 w31_3ec w31_3e8 w31_3e0 w31_288 w31_284 w31_8c w31_88 w31_7c w31_78 w31_74 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c g31_10 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
    -- 0x14C
    obtain ⟨n33, c33, u33⟩ := s32.block svL414c E32.self svL414c_end
      ⟨trivial, trivial⟩
    have m33 : n33.mem = n32.mem := u33.mem
    have s33 : St n33.mem SV n33 0x14E (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
    have rb33 : ∀ q, reg n33 q = (runBlock svL414c (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
    have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
    have t33 : Steps n0 n33 := t32.trans c33
    have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
    have E33 : SvCode n33.mem := E32.fr F fr33
    have V33 : SvSaves B n33.mem v := V32.same m33
    have g33_2 : reg n33 sp = B + 0x21A0 := by
      rw [rb33, runBlock_reg _ _ _ sp s32.zero (by decide), g32_2]
    have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb33, runBlock_reg _ _ _ (3 : Fin 32) s32.zero (by decide), g32_3]
    have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb33, runBlock_reg _ _ _ (4 : Fin 32) s32.zero (by decide), g32_4]
    have g33_9 : reg n33 (9 : Fin 32) = tbp := by
      rw [rb33, runBlock_reg _ _ _ (9 : Fin 32) s32.zero (by decide), g32_9]
    have g33_10 : reg n33 a0 = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := by
      rw [rb33, runBlock_reg _ _ _ a0 s32.zero (by decide), g32_10]
    have g33_18 : reg n33 (18 : Fin 32) = out := by
      rw [rb33, runBlock_reg _ _ _ (18 : Fin 32) s32.zero (by decide), g32_18]
    have g33_19 : reg n33 (19 : Fin 32) = bp := by
      rw [rb33, runBlock_reg _ _ _ (19 : Fin 32) s32.zero (by decide), g32_19]
    have g33_20 : reg n33 (20 : Fin 32) = dg := by
      rw [rb33, runBlock_reg _ _ _ (20 : Fin 32) s32.zero (by decide), g32_20]
    have g33_21 : reg n33 (21 : Fin 32) = rootp := by
      rw [rb33, runBlock_reg _ _ _ (21 : Fin 32) s32.zero (by decide), g32_21]
    have g33_22 : reg n33 (22 : Fin 32) = ll := by
      rw [rb33, runBlock_reg _ _ _ (22 : Fin 32) s32.zero (by decide), g32_22]
    have g33_23 : reg n33 (23 : Fin 32) = sgp := by
      rw [rb33, runBlock_reg _ _ _ (23 : Fin 32) s32.zero (by decide), g32_23]
    have g33_24 : reg n33 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by
      rw [rb33, runBlock_reg _ _ _ (24 : Fin 32) s32.zero (by decide), g32_24]
    have g33_25 : reg n33 (25 : Fin 32) = sgl := by
      rw [rb33, runBlock_reg _ _ _ (25 : Fin 32) s32.zero (by decide), g32_25]
    have g33_26 : reg n33 (26 : Fin 32) = lp := by
      rw [rb33, runBlock_reg _ _ _ (26 : Fin 32) s32.zero (by decide), g32_26]
    have g33_27 : reg n33 (27 : Fin 32) = tbl := by
      rw [rb33, runBlock_reg _ _ _ (27 : Fin 32) s32.zero (by decide), g32_27]
    have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb33]; simp +decide only [runBlock, BInstr.run, svL414c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_10, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m33]; exact keep_kk32
    clear keep_kk32
    have w33_5c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m33]; exact w32_5c
    have w33_60 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m33]; exact w32_60
    have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m33]; exact w32_64
    have w33_68 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m33]; exact w32_68
    have w33_6c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m33]; exact w32_6c
    have w33_70 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m33]; exact w32_70
    have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m33]; exact w32_74
    have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m33]; exact w32_78
    have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m33]; exact w32_7c
    have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm28 % 2 ^ 32) := by rw [m33]; exact w32_88
    have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm28 / 2 ^ 32) := by rw [m33]; exact w32_8c
    have w33_284 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m33]; exact w32_284
    have w33_288 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m33]; exact w32_288
    have w33_3e0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m33]; exact w32_3e0
    have w33_3e8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20) + BitVec.ofNat 32 kk28 := by rw [m33]; exact w32_3e8
    have w33_3ec : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := by rw [m33]; exact w32_3ec
    have b33_80 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m33]; exact b32_80
    have b33_90 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m33]; exact b32_90
    have b33_3e4 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m33]; exact b32_3e4
    have b33_3e5 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m33]; exact b32_3e5
    have b33_3e6 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m33]; exact b32_3e6
    have b33_3e7 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m33]; exact b32_3e7
    clear b32_3e7 b32_3e6 b32_3e5 b32_3e4 b32_90 b32_80 w32_3ec w32_3e8 w32_3e0 w32_288 w32_284 w32_8c w32_88 w32_7c w32_78 w32_74 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_10 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
    -- 0x14E: j
    obtain ⟨n34, d34, u34⟩ := s33.jump E33.self sv_at_14e (off' := 0x7A4) (by decide)
      (by rw [s33.pc]; decide)
    have s34 : St n34.mem SV n34 0x7A4 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
    have m34 : n34.mem = n33.mem := u34.mem
    have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
    have t34 : Steps n0 n34 := t33.trans (.single d34)
    have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
    have E34 : SvCode n34.mem := E33.fr F fr34
    have V34 : SvSaves B n34.mem v := V33.same m34
    have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, g33_2]
    have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, g33_3]
    have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, g33_4]
    have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u34.regs, g33_8]
    have g34_9 : reg n34 (9 : Fin 32) = tbp := by rw [u34.regs, g33_9]
    have g34_10 : reg n34 a0 = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := by rw [u34.regs, g33_10]
    have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, g33_18]
    have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, g33_19]
    have g34_20 : reg n34 (20 : Fin 32) = dg := by rw [u34.regs, g33_20]
    have g34_21 : reg n34 (21 : Fin 32) = rootp := by rw [u34.regs, g33_21]
    have g34_22 : reg n34 (22 : Fin 32) = ll := by rw [u34.regs, g33_22]
    have g34_23 : reg n34 (23 : Fin 32) = sgp := by rw [u34.regs, g33_23]
    have g34_24 : reg n34 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u34.regs, g33_24]
    have g34_25 : reg n34 (25 : Fin 32) = sgl := by rw [u34.regs, g33_25]
    have g34_26 : reg n34 (26 : Fin 32) = lp := by rw [u34.regs, g33_26]
    have g34_27 : reg n34 (27 : Fin 32) = tbl := by rw [u34.regs, g33_27]
    have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m34]; exact keep_kk33
    clear keep_kk33
    have w34_5c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m34]; exact w33_5c
    have w34_60 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m34]; exact w33_60
    have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m34]; exact w33_64
    have w34_68 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m34]; exact w33_68
    have w34_6c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m34]; exact w33_6c
    have w34_70 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m34]; exact w33_70
    have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m34]; exact w33_74
    have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m34]; exact w33_78
    have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m34]; exact w33_7c
    have w34_88 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm28 % 2 ^ 32) := by rw [m34]; exact w33_88
    have w34_8c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm28 / 2 ^ 32) := by rw [m34]; exact w33_8c
    have w34_284 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m34]; exact w33_284
    have w34_288 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m34]; exact w33_288
    have w34_3e0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m34]; exact w33_3e0
    have w34_3e8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20) + BitVec.ofNat 32 kk28 := by rw [m34]; exact w33_3e8
    have w34_3ec : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := by rw [m34]; exact w33_3ec
    have b34_80 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m34]; exact b33_80
    have b34_90 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m34]; exact b33_90
    have b34_3e4 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m34]; exact b33_3e4
    have b34_3e5 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m34]; exact b33_3e5
    have b34_3e6 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m34]; exact b33_3e6
    have b34_3e7 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m34]; exact b33_3e7
    clear b33_3e7 b33_3e6 b33_3e5 b33_3e4 b33_90 b33_80 w33_3ec w33_3e8 w33_3e0 w33_288 w33_284 w33_8c w33_88 w33_7c w33_78 w33_74 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c g33_8 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_10 g33_9 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
    exact .inl ⟨(fun ⟨tl3', h0', tl11', h1', tm20', rs20', h2', tm28', rs28', h3', h4', _⟩ => by rw [hr3] at h0'; cases h0'; rw [hr11] at h1'; cases h1'; rw [hr20] at h2'; cases h2'; rw [hr28] at h3'; cases h3'; exact hz_31 h4'), sv_fail F E34 s34 t34 (fun x hx => (fR34 x hx).trans (fM x hx).symm) V34 hret g34_2 g34_18 hO g34_3 g34_4⟩
  -- 0x24E: branch, not taken
  obtain ⟨n32, d32, u32⟩ := s31.notTaken E31.self 0x252 sv_at_24e
    (by decide) (by rw [g31_10, s31.zero]; exact br_bne_f (rest_eq hrb28 hz_31))
  have s32 : St n32.mem SV n32 0x252 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u32.regs, g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = tbp := by rw [u32.regs, g31_9]
  have g32_10 : reg n32 a0 = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := by rw [u32.regs, g31_10]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = dg := by rw [u32.regs, g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = rootp := by rw [u32.regs, g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = ll := by rw [u32.regs, g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = sgp := by rw [u32.regs, g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u32.regs, g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = sgl := by rw [u32.regs, g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = lp := by rw [u32.regs, g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = tbl := by rw [u32.regs, g31_27]
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m32]; exact w31_5c
  have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m32]; exact w31_60
  have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m32]; exact w31_64
  have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m32]; exact w31_68
  have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m32]; exact w31_6c
  have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m32]; exact w31_70
  have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m32]; exact w31_74
  have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m32]; exact w31_78
  have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m32]; exact w31_7c
  have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm28 % 2 ^ 32) := by rw [m32]; exact w31_88
  have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm28 / 2 ^ 32) := by rw [m32]; exact w31_8c
  have w32_284 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m32]; exact w31_284
  have w32_288 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m32]; exact w31_288
  have w32_3e0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m32]; exact w31_3e0
  have w32_3e8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20) + BitVec.ofNat 32 kk28 := by rw [m32]; exact w31_3e8
  have w32_3ec : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := by rw [m32]; exact w31_3ec
  have b32_80 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m32]; exact b31_80
  have b32_90 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m32]; exact b31_90
  have b32_3e4 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m32]; exact b31_3e4
  have b32_3e5 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m32]; exact b31_3e5
  have b32_3e6 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m32]; exact b31_3e6
  have b32_3e7 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m32]; exact b31_3e7
  clear b31_3e7 b31_3e6 b31_3e5 b31_3e4 b31_90 b31_80 w31_3ec w31_3e8 w31_3e0 w31_288 w31_284 w31_8c w31_88 w31_7c w31_78 w31_74 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c g31_10 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
  -- 0x252: lw
  obtain ⟨n33, d33, u33⟩ := s32.lw E32.self sv_at_252 (off' := 0x254) (by decide)
    (by rw [g32_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s33 : St n33.mem SV n33 0x254 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
  have t33 : Steps n0 n33 := t32.trans (.single d33)
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.same m33
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, upd_ne (by decide) (by decide), g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, upd_ne (by decide) (by decide), g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = tbp := by rw [u33.regs, upd_ne (by decide) (by decide), g32_9]
  have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, upd_ne (by decide) (by decide), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, upd_ne (by decide) (by decide), g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = dg := by rw [u33.regs, upd_ne (by decide) (by decide), g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = rootp := by rw [u33.regs, upd_ne (by decide) (by decide), g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = ll := by rw [u33.regs, upd_ne (by decide) (by decide), g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = sgp := by rw [u33.regs, upd_ne (by decide) (by decide), g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u33.regs, upd_ne (by decide) (by decide), g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = sgl := by rw [u33.regs, upd_ne (by decide) (by decide), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = lp := by rw [u33.regs, upd_ne (by decide) (by decide), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = tbl := by rw [u33.regs, upd_ne (by decide) (by decide), g32_27]
  have g33_10 : reg n33 a0 = BitVec.ofNat 32 (tm28 % 2 ^ 32) := by
    rw [u33.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g32_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr, w32_88]
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have w33_5c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m33]; exact w32_5c
  have w33_60 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m33]; exact w32_60
  have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m33]; exact w32_64
  have w33_68 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m33]; exact w32_68
  have w33_6c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m33]; exact w32_6c
  have w33_70 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m33]; exact w32_70
  have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m33]; exact w32_74
  have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m33]; exact w32_78
  have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m33]; exact w32_7c
  have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm28 % 2 ^ 32) := by rw [m33]; exact w32_88
  have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm28 / 2 ^ 32) := by rw [m33]; exact w32_8c
  have w33_284 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m33]; exact w32_284
  have w33_288 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m33]; exact w32_288
  have w33_3e0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m33]; exact w32_3e0
  have w33_3e8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20) + BitVec.ofNat 32 kk28 := by rw [m33]; exact w32_3e8
  have w33_3ec : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := by rw [m33]; exact w32_3ec
  have b33_80 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m33]; exact b32_80
  have b33_90 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m33]; exact b32_90
  have b33_3e4 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m33]; exact b32_3e4
  have b33_3e5 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m33]; exact b32_3e5
  have b33_3e6 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m33]; exact b32_3e6
  have b33_3e7 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m33]; exact b32_3e7
  clear b32_3e7 b32_3e6 b32_3e5 b32_3e4 b32_90 b32_80 w32_3ec w32_3e8 w32_3e0 w32_288 w32_284 w32_8c w32_88 w32_7c w32_78 w32_74 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_10 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
  -- 0x254: sw
  obtain ⟨n34, d34, s34, fr34, K34, W34, rg34⟩ := sv_sw F E33 s33 sv_at_254 (off' := 0x256) (c := 0x58)
    (by decide) (by rw [g33_2]; sv_addr) (by decide) (by decide)
  have t34 : Steps n0 n34 := t33.trans d34
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.keep K34 (by decide)
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [rg34 sp, g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg34 (3 : Fin 32), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg34 (4 : Fin 32), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg34 (8 : Fin 32), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = tbp := by rw [rg34 (9 : Fin 32), g33_9]
  have g34_10 : reg n34 a0 = BitVec.ofNat 32 (tm28 % 2 ^ 32) := by rw [rg34 a0, g33_10]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [rg34 (18 : Fin 32), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [rg34 (19 : Fin 32), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = dg := by rw [rg34 (20 : Fin 32), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = rootp := by rw [rg34 (21 : Fin 32), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = ll := by rw [rg34 (22 : Fin 32), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = sgp := by rw [rg34 (23 : Fin 32), g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [rg34 (24 : Fin 32), g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = sgl := by rw [rg34 (25 : Fin 32), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = lp := by rw [rg34 (26 : Fin 32), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = tbl := by rw [rg34 (27 : Fin 32), g33_27]
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8), (0x58, 0x4)] := keep_kk33.trans K34.toL
  clear keep_kk33
  have w34_5c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := (K34.w32 (by decide) (by decide)).trans w33_5c
  have w34_60 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := (K34.w32 (by decide) (by decide)).trans w33_60
  have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := (K34.w32 (by decide) (by decide)).trans w33_64
  have w34_68 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := (K34.w32 (by decide) (by decide)).trans w33_68
  have w34_6c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K34.w32 (by decide) (by decide)).trans w33_6c
  have w34_70 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K34.w32 (by decide) (by decide)).trans w33_70
  have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K34.w32 (by decide) (by decide)).trans w33_74
  have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K34.w32 (by decide) (by decide)).trans w33_78
  have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K34.w32 (by decide) (by decide)).trans w33_7c
  have w34_88 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm28 % 2 ^ 32) := (K34.w32 (by decide) (by decide)).trans w33_88
  have w34_8c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm28 / 2 ^ 32) := (K34.w32 (by decide) (by decide)).trans w33_8c
  have w34_284 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := (K34.w32 (by decide) (by decide)).trans w33_284
  have w34_288 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := (K34.w32 (by decide) (by decide)).trans w33_288
  have w34_3e0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K34.w32 (by decide) (by decide)).trans w33_3e0
  have w34_3e8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20) + BitVec.ofNat 32 kk28 := (K34.w32 (by decide) (by decide)).trans w33_3e8
  have w34_3ec : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := (K34.w32 (by decide) (by decide)).trans w33_3ec
  have b34_80 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := (K34.b8 (by decide) (by decide)).trans b33_80
  have b34_90 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := (K34.b8 (by decide) (by decide)).trans b33_90
  have b34_3e4 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := (K34.b8 (by decide) (by decide)).trans b33_3e4
  have b34_3e5 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := (K34.b8 (by decide) (by decide)).trans b33_3e5
  have b34_3e6 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := (K34.b8 (by decide) (by decide)).trans b33_3e6
  have b34_3e7 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := (K34.b8 (by decide) (by decide)).trans b33_3e7
  have w34_58 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm28 % 2 ^ 32) := by rw [W34, g33_10]
  clear b33_3e7 b33_3e6 b33_3e5 b33_3e4 b33_90 b33_80 w33_3ec w33_3e8 w33_3e0 w33_288 w33_284 w33_8c w33_88 w33_7c w33_78 w33_74 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c g33_10 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 m33 s33 u33 d33
  -- 0x256: lw
  obtain ⟨n35, d35, u35⟩ := s34.lw E34.self sv_at_256 (off' := 0x258) (by decide)
    (by rw [g34_2, show B + 0x21A0 + 0x8C = B + 0x21A0 + BitVec.ofNat 32 0x8C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s35 : St n35.mem SV n35 0x258 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
  have t35 : Steps n0 n35 := t34.trans (.single d35)
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.same m35
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, upd_ne (by decide) (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, upd_ne (by decide) (by decide), g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [u35.regs, upd_ne (by decide) (by decide), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = tbp := by rw [u35.regs, upd_ne (by decide) (by decide), g34_9]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, upd_ne (by decide) (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, upd_ne (by decide) (by decide), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = dg := by rw [u35.regs, upd_ne (by decide) (by decide), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = rootp := by rw [u35.regs, upd_ne (by decide) (by decide), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = ll := by rw [u35.regs, upd_ne (by decide) (by decide), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = sgp := by rw [u35.regs, upd_ne (by decide) (by decide), g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [u35.regs, upd_ne (by decide) (by decide), g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = sgl := by rw [u35.regs, upd_ne (by decide) (by decide), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = lp := by rw [u35.regs, upd_ne (by decide) (by decide), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = tbl := by rw [u35.regs, upd_ne (by decide) (by decide), g34_27]
  have g35_10 : reg n35 a0 = BitVec.ofNat 32 (tm28 / 2 ^ 32) := by
    rw [u35.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g34_2, show B + 0x21A0 + 0x8C = B + 0x21A0 + BitVec.ofNat 32 0x8C by sv_addr, w34_8c]
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8), (0x58, 0x4)] := by rw [m35]; exact keep_kk34
  clear keep_kk34
  have w35_58 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm28 % 2 ^ 32) := by rw [m35]; exact w34_58
  have w35_5c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := by rw [m35]; exact w34_5c
  have w35_60 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := by rw [m35]; exact w34_60
  have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := by rw [m35]; exact w34_64
  have w35_68 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := by rw [m35]; exact w34_68
  have w35_6c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m35]; exact w34_6c
  have w35_70 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := by rw [m35]; exact w34_70
  have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := by rw [m35]; exact w34_74
  have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := by rw [m35]; exact w34_78
  have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := by rw [m35]; exact w34_7c
  have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm28 % 2 ^ 32) := by rw [m35]; exact w34_88
  have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm28 / 2 ^ 32) := by rw [m35]; exact w34_8c
  have w35_284 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m35]; exact w34_284
  have w35_288 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := by rw [m35]; exact w34_288
  have w35_3e0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [m35]; exact w34_3e0
  have w35_3e8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20) + BitVec.ofNat 32 kk28 := by rw [m35]; exact w34_3e8
  have w35_3ec : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := by rw [m35]; exact w34_3ec
  have b35_80 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := by rw [m35]; exact b34_80
  have b35_90 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := by rw [m35]; exact b34_90
  have b35_3e4 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := by rw [m35]; exact b34_3e4
  have b35_3e5 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := by rw [m35]; exact b34_3e5
  have b35_3e6 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := by rw [m35]; exact b34_3e6
  have b35_3e7 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := by rw [m35]; exact b34_3e7
  clear w34_58 b34_3e7 b34_3e6 b34_3e5 b34_3e4 b34_90 b34_80 w34_3ec w34_3e8 w34_3e0 w34_288 w34_284 w34_8c w34_88 w34_7c w34_78 w34_74 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_10 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 rg34 W34 K34 fr34 s34 d34
  -- 0x258: sw
  obtain ⟨n36, d36, s36, fr36, K36, W36, rg36⟩ := sv_sw F E35 s35 sv_at_258 (off' := 0x25A) (c := 0x54)
    (by decide) (by rw [g35_2]; sv_addr) (by decide) (by decide)
  have t36 : Steps n0 n36 := t35.trans d36
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.keep K36 (by decide)
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [rg36 sp, g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg36 (3 : Fin 32), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg36 (4 : Fin 32), g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = ((BitVec.ofNat 32 tl11.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg36 (8 : Fin 32), g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = tbp := by rw [rg36 (9 : Fin 32), g35_9]
  have g36_10 : reg n36 a0 = BitVec.ofNat 32 (tm28 / 2 ^ 32) := by rw [rg36 a0, g35_10]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [rg36 (18 : Fin 32), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [rg36 (19 : Fin 32), g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = dg := by rw [rg36 (20 : Fin 32), g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = rootp := by rw [rg36 (21 : Fin 32), g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = ll := by rw [rg36 (22 : Fin 32), g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = sgp := by rw [rg36 (23 : Fin 32), g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := by rw [rg36 (24 : Fin 32), g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = sgl := by rw [rg36 (25 : Fin 32), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = lp := by rw [rg36 (26 : Fin 32), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = tbl := by rw [rg36 (27 : Fin 32), g35_27]
  have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x6C, 0x4), (0x80, 0x11), (0x284, 0x8), (0x68, 0x4), (0x64, 0x4), (0x80, 0x10), (0x284, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x80, 0x10), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x80, 0x10), (0x3E8, 0x8), (0x58, 0x4), (0x54, 0x4)] := keep_kk35.trans K36.toL
  clear keep_kk35
  have w36_58 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm28 % 2 ^ 32) := (K36.w32 (by decide) (by decide)).trans w35_58
  have w36_5c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 (tm20 / 2 ^ 32) := (K36.w32 (by decide) (by decide)).trans w35_5c
  have w36_60 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 (tm20 % 2 ^ 32) := (K36.w32 (by decide) (by decide)).trans w35_60
  have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (tl3.header + tl3.len) := (K36.w32 (by decide) (by decide)).trans w35_64
  have w36_68 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = rp := (K36.w32 (by decide) (by decide)).trans w35_68
  have w36_6c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K36.w32 (by decide) (by decide)).trans w35_6c
  have w36_70 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arl := (K36.w32 (by decide) (by decide)).trans w35_70
  have w36_74 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arp := (K36.w32 (by decide) (by decide)).trans w35_74
  have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = sal := (K36.w32 (by decide) (by decide)).trans w35_78
  have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sap := (K36.w32 (by decide) (by decide)).trans w35_7c
  have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = BitVec.ofNat 32 (tm28 % 2 ^ 32) := (K36.w32 (by decide) (by decide)).trans w35_88
  have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tm28 / 2 ^ 32) := (K36.w32 (by decide) (by decide)).trans w35_8c
  have w36_284 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 (tl11.header + tl11.len) := (K36.w32 (by decide) (by decide)).trans w35_284
  have w36_288 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl3.header + tl3.len)) - BitVec.ofNat 32 (tl11.header + tl11.len) := (K36.w32 (by decide) (by decide)).trans w35_288
  have w36_3e0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header := (K36.w32 (by decide) (by decide)).trans w35_3e0
  have w36_3e8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((rp) + BitVec.ofNat 32 (tl3.header + tl3.len)) + BitVec.ofNat 32 tl11.header) + BitVec.ofNat 32 kk20) + BitVec.ofNat 32 kk28 := (K36.w32 (by decide) (by decide)).trans w35_3e8
  have w36_3ec : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 (((tl11.len) - kk20) - kk28) := (K36.w32 (by decide) (by decide)).trans w35_3ec
  have b36_80 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (0 : BitVec 8) := (K36.b8 (by decide) (by decide)).trans b35_80
  have b36_90 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl3.tag := (K36.b8 (by decide) (by decide)).trans b35_90
  have b36_3e4 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl11.len).extractLsb' 0 8 := (K36.b8 (by decide) (by decide)).trans b35_3e4
  have b36_3e5 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl11.len).extractLsb' 8 8 := (K36.b8 (by decide) (by decide)).trans b35_3e5
  have b36_3e6 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl11.len).extractLsb' 16 8 := (K36.b8 (by decide) (by decide)).trans b35_3e6
  have b36_3e7 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl11.len).extractLsb' 24 8 := (K36.b8 (by decide) (by decide)).trans b35_3e7
  have w36_54 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm28 / 2 ^ 32) := by rw [W36, g35_10]
  clear b35_3e7 b35_3e6 b35_3e5 b35_3e4 b35_90 b35_80 w35_3ec w35_3e8 w35_3e0 w35_288 w35_284 w35_8c w35_88 w35_7c w35_78 w35_74 w35_70 w35_6c w35_68 w35_64 w35_60 w35_5c w35_58 g35_10 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 m35 s35 u35 d35
  exact .inr ⟨tl3, hr3, tl11, hr11, tm20, rs20, hr20, tm28, rs28, hr28, hz_31, n36, t36, s36, E36, V36, fR36, g36_2, g36_3, g36_4, g36_8, g36_9, g36_18, g36_19, g36_20, g36_21, g36_22, g36_23, g36_24, g36_25, g36_26, g36_27, w36_54, w36_58, w36_5c, w36_60, w36_64, w36_68, w36_6c, w36_70, w36_74, w36_78, w36_7c, w36_284, w36_288, keep_kk36.mono (by decide)⟩

end C3.RV32.Sv
