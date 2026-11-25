import C3BootProofs.Proofs.SvSha2

/-!
# `sigstore::verify`: the signed attributes loop's start

From 0xE7C to the signed attributes loop's head at 0xEA0: the signed attributes aren't empty, no digest or content type is seen yet, and the loop's reader covers them.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTr7e80 : List BInstr :=
  [.aluImm .add a2 sp 0x400]
theorem svTr7e80_end : blockEnd sigstoreVerifyCode 0xE80 svTr7e80 = some 0xE84 := by
  simp only [svTr7e80]
  rw [blockEnd, sv_at_e80]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr7e90 : List BInstr :=
  [.aluImm .add a1 sp 0x200]
theorem svTr7e90_end : blockEnd sigstoreVerifyCode 0xE90 svTr7e90 = some 0xE92 := by
  simp only [svTr7e90]
  rw [blockEnd, sv_at_e90]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr7e94 : List BInstr :=
  [.alu .add a2 x0 (24 : Fin 32)]
theorem svTr7e94_end : blockEnd sigstoreVerifyCode 0xE94 svTr7e94 = some 0xE96 := by
  simp only [svTr7e94]
  rw [blockEnd, sv_at_e94]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr71002 : List BInstr :=
  [.alu .sltu a0 x0 a0]
theorem svTr71002_end : blockEnd sigstoreVerifyCode 0x1002 svTr71002 = some 0x1006 := by
  simp only [svTr71002]
  rw [blockEnd, sv_at_1002]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr71008 : List BInstr :=
  [.alu .and a0 a0 a1]
theorem svTr71008_end : blockEnd sigstoreVerifyCode 0x1008 svTr71008 = some 0x100A := by
  simp only [svTr71008]
  rw [blockEnd, sv_at_1008]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr712b8 : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x18]
theorem svTr712b8_end : blockEnd sigstoreVerifyCode 0x12B8 svTr712b8 = some 0x12BA := by
  simp only [svTr712b8]
  rw [blockEnd, sv_at_12b8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_tr7 {B out bp x20 x21 x22 x23 x24 x25 x26 x27 ap al aq ah sip sil : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xE7C (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = ap)
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
    (w0_378 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip)
    (w0_37c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil)
    (w0_424 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap)
    (w0_428 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al)
    (w0_42c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq)
    (w0_430 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah)
    (a_in : SvIn B (ap) (al).toNat)
    (si_in : SvIn B (sip) (sil).toNat) :
    (¬ ((al ≠ 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((al ≠ 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xEA0 (reg n') ∧
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
        reg n' (24 : Fin 32) = al ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ap ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = al ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ap ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = al ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil ∧
        SvKeepL B n0.mem n'.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xE7C: sw
  obtain ⟨n1, d1, s1, fr1, K1, W1, rg1⟩ := sv_sw F E0 s0 sv_at_e7c (off' := 0xE7E) (c := 0x64)
    (by decide) (by rw [g0_2]; sv_addr) (by decide) (by decide)
  have t1 : Steps n0 n1 := t0.trans d1
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.keep K1 (by decide)
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [rg1 sp, g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg1 (3 : Fin 32), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg1 (4 : Fin 32), g0_4]
  have g1_10 : reg n1 a0 = ap := by rw [rg1 a0, g0_10]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [rg1 (18 : Fin 32), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [rg1 (19 : Fin 32), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = x20 := by rw [rg1 (20 : Fin 32), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by rw [rg1 (21 : Fin 32), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = x22 := by rw [rg1 (22 : Fin 32), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = x23 := by rw [rg1 (23 : Fin 32), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = x24 := by rw [rg1 (24 : Fin 32), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by rw [rg1 (25 : Fin 32), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [rg1 (26 : Fin 32), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = x27 := by rw [rg1 (27 : Fin 32), g0_27]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [(0x64, 0x4)] := (SvKeepL.refl : SvKeepL B n0.mem n0.mem []).trans K1.toL
  have w1_378 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := (K1.w32 (by decide) (by decide)).trans w0_378
  have w1_37c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := (K1.w32 (by decide) (by decide)).trans w0_37c
  have w1_424 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := (K1.w32 (by decide) (by decide)).trans w0_424
  have w1_428 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := (K1.w32 (by decide) (by decide)).trans w0_428
  have w1_42c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := (K1.w32 (by decide) (by decide)).trans w0_42c
  have w1_430 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := (K1.w32 (by decide) (by decide)).trans w0_430
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [W1, s0.zero]; rfl
  -- 0xE7E: sw
  obtain ⟨n2, d2, s2, fr2, K2, W2, rg2⟩ := sv_sw F E1 s1 sv_at_e7e (off' := 0xE80) (c := 0x7C)
    (by decide) (by rw [g1_2]; sv_addr) (by decide) (by decide)
  have t2 : Steps n0 n2 := t1.trans d2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keep K2 (by decide)
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [rg2 sp, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg2 (3 : Fin 32), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg2 (4 : Fin 32), g1_4]
  have g2_10 : reg n2 a0 = ap := by rw [rg2 a0, g1_10]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [rg2 (18 : Fin 32), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [rg2 (19 : Fin 32), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by rw [rg2 (20 : Fin 32), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [rg2 (21 : Fin 32), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by rw [rg2 (22 : Fin 32), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by rw [rg2 (23 : Fin 32), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = x24 := by rw [rg2 (24 : Fin 32), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by rw [rg2 (25 : Fin 32), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [rg2 (26 : Fin 32), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = x27 := by rw [rg2 (27 : Fin 32), g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x64, 0x4), (0x7C, 0x4)] := keep_kk1.trans K2.toL
  clear keep_kk1
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := (K2.w32 (by decide) (by decide)).trans w1_64
  have w2_378 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := (K2.w32 (by decide) (by decide)).trans w1_378
  have w2_37c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := (K2.w32 (by decide) (by decide)).trans w1_37c
  have w2_424 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := (K2.w32 (by decide) (by decide)).trans w1_424
  have w2_428 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := (K2.w32 (by decide) (by decide)).trans w1_428
  have w2_42c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := (K2.w32 (by decide) (by decide)).trans w1_42c
  have w2_430 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := (K2.w32 (by decide) (by decide)).trans w1_430
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [W2, s1.zero]; rfl
  clear w1_64 w1_430 w1_42c w1_428 w1_424 w1_37c w1_378 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_10 g1_4 g1_3 g1_2 V1 E1 fR1 t1 rg1 W1 K1 fr1 s1 d1 g0_4 g0_3 fR0 t0
  -- 0xE80
  obtain ⟨n3, c3, u3⟩ := s2.block svTr7e80 E2.self svTr7e80_end
    ⟨trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0xE84 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock svTr7e80 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans c3
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by
    rw [rb3, runBlock_reg _ _ _ sp s2.zero (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb3, runBlock_reg _ _ _ (3 : Fin 32) s2.zero (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb3, runBlock_reg _ _ _ (4 : Fin 32) s2.zero (by decide), g2_4]
  have g3_10 : reg n3 a0 = ap := by
    rw [rb3, runBlock_reg _ _ _ a0 s2.zero (by decide), g2_10]
  have g3_18 : reg n3 (18 : Fin 32) = out := by
    rw [rb3, runBlock_reg _ _ _ (18 : Fin 32) s2.zero (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by
    rw [rb3, runBlock_reg _ _ _ (19 : Fin 32) s2.zero (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = x20 := by
    rw [rb3, runBlock_reg _ _ _ (20 : Fin 32) s2.zero (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by
    rw [rb3, runBlock_reg _ _ _ (21 : Fin 32) s2.zero (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by
    rw [rb3, runBlock_reg _ _ _ (22 : Fin 32) s2.zero (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = x23 := by
    rw [rb3, runBlock_reg _ _ _ (23 : Fin 32) s2.zero (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = x24 := by
    rw [rb3, runBlock_reg _ _ _ (24 : Fin 32) s2.zero (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by
    rw [rb3, runBlock_reg _ _ _ (25 : Fin 32) s2.zero (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by
    rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = x27 := by
    rw [rb3, runBlock_reg _ _ _ (27 : Fin 32) s2.zero (by decide), g2_27]
  have g3_12 : reg n3 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svTr7e80, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_10, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x64, 0x4), (0x7C, 0x4)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m3]; exact w2_64
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [m3]; exact w2_7c
  have w3_378 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m3]; exact w2_378
  have w3_37c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m3]; exact w2_37c
  have w3_424 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := by rw [m3]; exact w2_424
  have w3_428 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := by rw [m3]; exact w2_428
  have w3_42c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := by rw [m3]; exact w2_42c
  have w3_430 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := by rw [m3]; exact w2_430
  clear w2_7c w2_430 w2_42c w2_428 w2_424 w2_37c w2_378 w2_64 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_10 g2_4 g2_3 g2_2 V2 E2 fR2 t2 rg2 W2 K2 fr2 s2 d2
  -- 0xE84: lw
  obtain ⟨n4, d4, u4⟩ := s3.lw E3.self sv_at_e84 (off' := 0xE88) (by decide)
    (by rw [g3_12, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s4 : St n4.mem SV n4 0xE88 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
  have g4_10 : reg n4 a0 = ap := by rw [u4.regs, upd_ne (by decide) (by decide), g3_10]
  have g4_12 : reg n4 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_12]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_23]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = x27 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_27]
  have g4_24 : reg n4 (24 : Fin 32) = al := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g3_12, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x28 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr, w3_428]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x64, 0x4), (0x7C, 0x4)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m4]; exact w3_64
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [m4]; exact w3_7c
  have w4_378 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m4]; exact w3_378
  have w4_37c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m4]; exact w3_37c
  have w4_424 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := by rw [m4]; exact w3_424
  have w4_428 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := by rw [m4]; exact w3_428
  have w4_42c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := by rw [m4]; exact w3_42c
  have w4_430 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := by rw [m4]; exact w3_430
  clear w3_430 w3_42c w3_428 w3_424 w3_37c w3_378 w3_7c w3_64 g3_12 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  -- 0xE88: lw
  obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_e88 (off' := 0xE8A) (by decide)
    (by rw [g4_12, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s5 : St n5.mem SV n5 0xE8A (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
  have g5_10 : reg n5 a0 = ap := by rw [u5.regs, upd_ne (by decide) (by decide), g4_10]
  have g5_12 : reg n5 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_12]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = al := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = x27 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
  have g5_11 : reg n5 a1 = aq := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g4_12, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x2C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr, w4_42c]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x64, 0x4), (0x7C, 0x4)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m5]; exact w4_64
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [m5]; exact w4_7c
  have w5_378 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m5]; exact w4_378
  have w5_37c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m5]; exact w4_37c
  have w5_424 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := by rw [m5]; exact w4_424
  have w5_428 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := by rw [m5]; exact w4_428
  have w5_42c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := by rw [m5]; exact w4_42c
  have w5_430 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := by rw [m5]; exact w4_430
  clear w4_430 w4_42c w4_428 w4_424 w4_37c w4_378 w4_7c w4_64 g4_24 g4_27 g4_26 g4_25 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_12 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0xE8A: sw
  obtain ⟨n6, d6, s6, fr6, K6, W6, rg6⟩ := sv_sw F E5 s5 sv_at_e8a (off' := 0xE8C) (c := 0x44)
    (by decide) (by rw [g5_2]; sv_addr) (by decide) (by decide)
  have t6 : Steps n0 n6 := t5.trans d6
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [rg6 sp, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg6 (3 : Fin 32), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg6 (4 : Fin 32), g5_4]
  have g6_10 : reg n6 a0 = ap := by rw [rg6 a0, g5_10]
  have g6_11 : reg n6 a1 = aq := by rw [rg6 a1, g5_11]
  have g6_12 : reg n6 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg6 a2, g5_12]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [rg6 (18 : Fin 32), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [rg6 (19 : Fin 32), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [rg6 (20 : Fin 32), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [rg6 (21 : Fin 32), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [rg6 (22 : Fin 32), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [rg6 (23 : Fin 32), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = al := by rw [rg6 (24 : Fin 32), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [rg6 (25 : Fin 32), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [rg6 (26 : Fin 32), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = x27 := by rw [rg6 (27 : Fin 32), g5_27]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4)] := keep_kk5.trans K6.toL
  clear keep_kk5
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := (K6.w32 (by decide) (by decide)).trans w5_64
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := (K6.w32 (by decide) (by decide)).trans w5_7c
  have w6_378 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := (K6.w32 (by decide) (by decide)).trans w5_378
  have w6_37c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := (K6.w32 (by decide) (by decide)).trans w5_37c
  have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := (K6.w32 (by decide) (by decide)).trans w5_424
  have w6_428 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := (K6.w32 (by decide) (by decide)).trans w5_428
  have w6_42c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := (K6.w32 (by decide) (by decide)).trans w5_42c
  have w6_430 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := (K6.w32 (by decide) (by decide)).trans w5_430
  have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := by rw [W6, g5_11]
  clear w5_430 w5_42c w5_428 w5_424 w5_37c w5_378 w5_7c w5_64 g5_11 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_12 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0xE8C: lw
  obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_e8c (off' := 0xE8E) (by decide)
    (by rw [g6_12, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x30 = B + 0x21A0 + BitVec.ofNat 32 0x430 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s7 : St n7.mem SV n7 0xE8E (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
  have g7_10 : reg n7 a0 = ap := by rw [u7.regs, upd_ne (by decide) (by decide), g6_10]
  have g7_12 : reg n7 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_12]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, upd_ne (by decide) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = al := by rw [u7.regs, upd_ne (by decide) (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = x27 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
  have g7_11 : reg n7 a1 = ah := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_12, show B + 0x21A0 + BitVec.ofNat 32 0x400 + 0x30 = B + 0x21A0 + BitVec.ofNat 32 0x430 by sv_addr, w6_430]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := by rw [m7]; exact w6_44
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m7]; exact w6_64
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [m7]; exact w6_7c
  have w7_378 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m7]; exact w6_378
  have w7_37c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m7]; exact w6_37c
  have w7_424 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := by rw [m7]; exact w6_424
  have w7_428 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := by rw [m7]; exact w6_428
  have w7_42c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := by rw [m7]; exact w6_42c
  have w7_430 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := by rw [m7]; exact w6_430
  clear w6_44 w6_430 w6_42c w6_428 w6_424 w6_37c w6_378 w6_7c w6_64 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_12 g6_11 g6_10 g6_4 g6_3 g6_2 V6 E6 fR6 t6 rg6 W6 K6 fr6 s6 d6
  -- 0xE8E: sw
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sw F E7 s7 sv_at_e8e (off' := 0xE90) (c := 0x50)
    (by decide) (by rw [g7_2]; sv_addr) (by decide) (by decide)
  have t8 : Steps n0 n8 := t7.trans d8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
  have g8_10 : reg n8 a0 = ap := by rw [rg8 a0, g7_10]
  have g8_11 : reg n8 a1 = ah := by rw [rg8 a1, g7_11]
  have g8_12 : reg n8 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg8 a2, g7_12]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rg8 (18 : Fin 32), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rg8 (19 : Fin 32), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [rg8 (20 : Fin 32), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [rg8 (21 : Fin 32), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [rg8 (22 : Fin 32), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [rg8 (23 : Fin 32), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = al := by rw [rg8 (24 : Fin 32), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by rw [rg8 (25 : Fin 32), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [rg8 (26 : Fin 32), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = x27 := by rw [rg8 (27 : Fin 32), g7_27]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := (K8.w32 (by decide) (by decide)).trans w7_44
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := (K8.w32 (by decide) (by decide)).trans w7_64
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := (K8.w32 (by decide) (by decide)).trans w7_7c
  have w8_378 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := (K8.w32 (by decide) (by decide)).trans w7_378
  have w8_37c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := (K8.w32 (by decide) (by decide)).trans w7_37c
  have w8_424 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := (K8.w32 (by decide) (by decide)).trans w7_424
  have w8_428 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := (K8.w32 (by decide) (by decide)).trans w7_428
  have w8_42c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := (K8.w32 (by decide) (by decide)).trans w7_42c
  have w8_430 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := (K8.w32 (by decide) (by decide)).trans w7_430
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := by rw [W8, g7_11]
  clear w7_430 w7_42c w7_428 w7_424 w7_37c w7_378 w7_7c w7_64 w7_44 g7_11 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_12 g7_10 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0xE90
  obtain ⟨n9, c9, u9⟩ := s8.block svTr7e90 E8.self svTr7e90_end
    ⟨trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem SV n9 0xE92 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock svTr7e90 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by
    rw [rb9, runBlock_reg _ _ _ sp s8.zero (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb9, runBlock_reg _ _ _ (3 : Fin 32) s8.zero (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb9, runBlock_reg _ _ _ (4 : Fin 32) s8.zero (by decide), g8_4]
  have g9_10 : reg n9 a0 = ap := by
    rw [rb9, runBlock_reg _ _ _ a0 s8.zero (by decide), g8_10]
  have g9_12 : reg n9 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb9, runBlock_reg _ _ _ a2 s8.zero (by decide), g8_12]
  have g9_18 : reg n9 (18 : Fin 32) = out := by
    rw [rb9, runBlock_reg _ _ _ (18 : Fin 32) s8.zero (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by
    rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by
    rw [rb9, runBlock_reg _ _ _ (20 : Fin 32) s8.zero (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by
    rw [rb9, runBlock_reg _ _ _ (21 : Fin 32) s8.zero (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by
    rw [rb9, runBlock_reg _ _ _ (22 : Fin 32) s8.zero (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by
    rw [rb9, runBlock_reg _ _ _ (23 : Fin 32) s8.zero (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = al := by
    rw [rb9, runBlock_reg _ _ _ (24 : Fin 32) s8.zero (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by
    rw [rb9, runBlock_reg _ _ _ (25 : Fin 32) s8.zero (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by
    rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = x27 := by
    rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
  have g9_11 : reg n9 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svTr7e90, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_10, g8_11, g8_12, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := by rw [m9]; exact w8_44
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := by rw [m9]; exact w8_50
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m9]; exact w8_64
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [m9]; exact w8_7c
  have w9_378 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m9]; exact w8_378
  have w9_37c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m9]; exact w8_37c
  have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := by rw [m9]; exact w8_424
  have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := by rw [m9]; exact w8_428
  have w9_42c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := by rw [m9]; exact w8_42c
  have w9_430 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := by rw [m9]; exact w8_430
  clear w8_50 w8_430 w8_42c w8_428 w8_424 w8_37c w8_378 w8_7c w8_64 w8_44 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_12 g8_11 g8_10 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
  -- 0xE92: sw
  obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := sv_sw F E9 s9 sv_at_e92 (off' := 0xE94) (c := 0x25C)
    (by decide) (by rw [g9_11]; sv_addr) (by decide) (by decide)
  have t10 : Steps n0 n10 := t9.trans d10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rg10 sp, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg10 (3 : Fin 32), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg10 (4 : Fin 32), g9_4]
  have g10_10 : reg n10 a0 = ap := by rw [rg10 a0, g9_10]
  have g10_11 : reg n10 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by rw [rg10 a1, g9_11]
  have g10_12 : reg n10 a2 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg10 a2, g9_12]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [rg10 (18 : Fin 32), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [rg10 (19 : Fin 32), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [rg10 (20 : Fin 32), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [rg10 (21 : Fin 32), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [rg10 (22 : Fin 32), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [rg10 (23 : Fin 32), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = al := by rw [rg10 (24 : Fin 32), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [rg10 (25 : Fin 32), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [rg10 (26 : Fin 32), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = x27 := by rw [rg10 (27 : Fin 32), g9_27]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4)] := keep_kk9.trans K10.toL
  clear keep_kk9
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := (K10.w32 (by decide) (by decide)).trans w9_44
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := (K10.w32 (by decide) (by decide)).trans w9_50
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := (K10.w32 (by decide) (by decide)).trans w9_64
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := (K10.w32 (by decide) (by decide)).trans w9_7c
  have w10_378 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := (K10.w32 (by decide) (by decide)).trans w9_378
  have w10_37c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := (K10.w32 (by decide) (by decide)).trans w9_37c
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := (K10.w32 (by decide) (by decide)).trans w9_424
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := (K10.w32 (by decide) (by decide)).trans w9_428
  have w10_42c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := (K10.w32 (by decide) (by decide)).trans w9_42c
  have w10_430 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := (K10.w32 (by decide) (by decide)).trans w9_430
  have w10_25c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ap := by rw [W10, g9_10]
  clear w9_430 w9_42c w9_428 w9_424 w9_37c w9_378 w9_7c w9_64 w9_50 w9_44 g9_11 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_12 g9_10 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0xE94
  obtain ⟨n11, c11, u11⟩ := s10.block svTr7e94 E10.self svTr7e94_end
    ⟨trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem SV n11 0xE96 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock svTr7e94 (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans c11
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by
    rw [rb11, runBlock_reg _ _ _ sp s10.zero (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb11, runBlock_reg _ _ _ (3 : Fin 32) s10.zero (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb11, runBlock_reg _ _ _ (4 : Fin 32) s10.zero (by decide), g10_4]
  have g11_10 : reg n11 a0 = ap := by
    rw [rb11, runBlock_reg _ _ _ a0 s10.zero (by decide), g10_10]
  have g11_11 : reg n11 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb11, runBlock_reg _ _ _ a1 s10.zero (by decide), g10_11]
  have g11_18 : reg n11 (18 : Fin 32) = out := by
    rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by
    rw [rb11, runBlock_reg _ _ _ (19 : Fin 32) s10.zero (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by
    rw [rb11, runBlock_reg _ _ _ (20 : Fin 32) s10.zero (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by
    rw [rb11, runBlock_reg _ _ _ (21 : Fin 32) s10.zero (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by
    rw [rb11, runBlock_reg _ _ _ (22 : Fin 32) s10.zero (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by
    rw [rb11, runBlock_reg _ _ _ (23 : Fin 32) s10.zero (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = al := by
    rw [rb11, runBlock_reg _ _ _ (24 : Fin 32) s10.zero (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by
    rw [rb11, runBlock_reg _ _ _ (25 : Fin 32) s10.zero (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by
    rw [rb11, runBlock_reg _ _ _ (26 : Fin 32) s10.zero (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = x27 := by
    rw [rb11, runBlock_reg _ _ _ (27 : Fin 32) s10.zero (by decide), g10_27]
  have g11_12 : reg n11 a2 = al := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svTr7e94, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_10, g10_11, g10_12, g10_18, g10_19, g10_20, g10_21, g10_22, g10_23, g10_24, g10_25, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := by rw [m11]; exact w10_44
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := by rw [m11]; exact w10_50
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m11]; exact w10_64
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [m11]; exact w10_7c
  have w11_25c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ap := by rw [m11]; exact w10_25c
  have w11_378 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m11]; exact w10_378
  have w11_37c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m11]; exact w10_37c
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := by rw [m11]; exact w10_424
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := by rw [m11]; exact w10_428
  have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := by rw [m11]; exact w10_42c
  have w11_430 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := by rw [m11]; exact w10_430
  clear w10_25c w10_430 w10_42c w10_428 w10_424 w10_37c w10_378 w10_7c w10_64 w10_50 w10_44 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_12 g10_11 g10_10 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
  -- 0xE96: sw
  obtain ⟨n12, d12, s12, fr12, K12, W12, rg12⟩ := sv_sw F E11 s11 sv_at_e96 (off' := 0xE98) (c := 0x260)
    (by decide) (by rw [g11_11]; sv_addr) (by decide) (by decide)
  have t12 : Steps n0 n12 := t11.trans d12
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.keep K12 (by decide)
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [rg12 sp, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg12 (3 : Fin 32), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg12 (4 : Fin 32), g11_4]
  have g12_10 : reg n12 a0 = ap := by rw [rg12 a0, g11_10]
  have g12_11 : reg n12 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by rw [rg12 a1, g11_11]
  have g12_12 : reg n12 a2 = al := by rw [rg12 a2, g11_12]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [rg12 (18 : Fin 32), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [rg12 (19 : Fin 32), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [rg12 (20 : Fin 32), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [rg12 (21 : Fin 32), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [rg12 (22 : Fin 32), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [rg12 (23 : Fin 32), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = al := by rw [rg12 (24 : Fin 32), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [rg12 (25 : Fin 32), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [rg12 (26 : Fin 32), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = x27 := by rw [rg12 (27 : Fin 32), g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4), (0x260, 0x4)] := keep_kk11.trans K12.toL
  clear keep_kk11
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := (K12.w32 (by decide) (by decide)).trans w11_44
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := (K12.w32 (by decide) (by decide)).trans w11_50
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := (K12.w32 (by decide) (by decide)).trans w11_64
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := (K12.w32 (by decide) (by decide)).trans w11_7c
  have w12_25c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ap := (K12.w32 (by decide) (by decide)).trans w11_25c
  have w12_378 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := (K12.w32 (by decide) (by decide)).trans w11_378
  have w12_37c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := (K12.w32 (by decide) (by decide)).trans w11_37c
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := (K12.w32 (by decide) (by decide)).trans w11_424
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := (K12.w32 (by decide) (by decide)).trans w11_428
  have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := (K12.w32 (by decide) (by decide)).trans w11_42c
  have w12_430 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := (K12.w32 (by decide) (by decide)).trans w11_430
  have w12_260 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = al := by rw [W12, g11_12]
  clear w11_430 w11_42c w11_428 w11_424 w11_37c w11_378 w11_25c w11_7c w11_64 w11_50 w11_44 g11_12 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_11 g11_10 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
  -- 0xE98: sw
  obtain ⟨n13, d13, s13, fr13, K13, W13, rg13⟩ := sv_sw F E12 s12 sv_at_e98 (off' := 0xE9A) (c := 0x264)
    (by decide) (by rw [g12_11]; sv_addr) (by decide) (by decide)
  have t13 : Steps n0 n13 := t12.trans d13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keep K13 (by decide)
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rg13 sp, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg13 (3 : Fin 32), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg13 (4 : Fin 32), g12_4]
  have g13_10 : reg n13 a0 = ap := by rw [rg13 a0, g12_10]
  have g13_11 : reg n13 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by rw [rg13 a1, g12_11]
  have g13_12 : reg n13 a2 = al := by rw [rg13 a2, g12_12]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rg13 (18 : Fin 32), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rg13 (19 : Fin 32), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [rg13 (20 : Fin 32), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [rg13 (21 : Fin 32), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [rg13 (22 : Fin 32), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [rg13 (23 : Fin 32), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = al := by rw [rg13 (24 : Fin 32), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [rg13 (25 : Fin 32), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [rg13 (26 : Fin 32), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [rg13 (27 : Fin 32), g12_27]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4)] := keep_kk12.trans K13.toL
  clear keep_kk12
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := (K13.w32 (by decide) (by decide)).trans w12_44
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := (K13.w32 (by decide) (by decide)).trans w12_50
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := (K13.w32 (by decide) (by decide)).trans w12_64
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := (K13.w32 (by decide) (by decide)).trans w12_7c
  have w13_25c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ap := (K13.w32 (by decide) (by decide)).trans w12_25c
  have w13_260 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = al := (K13.w32 (by decide) (by decide)).trans w12_260
  have w13_378 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := (K13.w32 (by decide) (by decide)).trans w12_378
  have w13_37c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := (K13.w32 (by decide) (by decide)).trans w12_37c
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := (K13.w32 (by decide) (by decide)).trans w12_424
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := (K13.w32 (by decide) (by decide)).trans w12_428
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := (K13.w32 (by decide) (by decide)).trans w12_42c
  have w13_430 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := (K13.w32 (by decide) (by decide)).trans w12_430
  have w13_264 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ap := by rw [W13, g12_10]
  clear w12_260 w12_430 w12_42c w12_428 w12_424 w12_37c w12_378 w12_25c w12_7c w12_64 w12_50 w12_44 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_12 g12_11 g12_10 g12_4 g12_3 g12_2 V12 E12 fR12 t12 rg12 W12 K12 fr12 s12 d12
  -- 0xE9A: sw
  obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sw F E13 s13 sv_at_e9a (off' := 0xE9C) (c := 0x268)
    (by decide) (by rw [g13_11]; sv_addr) (by decide) (by decide)
  have t14 : Steps n0 n14 := t13.trans d14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rg14 sp, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg14 (3 : Fin 32), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg14 (4 : Fin 32), g13_4]
  have g14_10 : reg n14 a0 = ap := by rw [rg14 a0, g13_10]
  have g14_11 : reg n14 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by rw [rg14 a1, g13_11]
  have g14_12 : reg n14 a2 = al := by rw [rg14 a2, g13_12]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rg14 (18 : Fin 32), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rg14 (19 : Fin 32), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [rg14 (20 : Fin 32), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [rg14 (21 : Fin 32), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [rg14 (22 : Fin 32), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [rg14 (23 : Fin 32), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = al := by rw [rg14 (24 : Fin 32), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [rg14 (25 : Fin 32), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [rg14 (26 : Fin 32), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = x27 := by rw [rg14 (27 : Fin 32), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := (K14.w32 (by decide) (by decide)).trans w13_44
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := (K14.w32 (by decide) (by decide)).trans w13_50
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := (K14.w32 (by decide) (by decide)).trans w13_64
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := (K14.w32 (by decide) (by decide)).trans w13_7c
  have w14_25c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ap := (K14.w32 (by decide) (by decide)).trans w13_25c
  have w14_260 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = al := (K14.w32 (by decide) (by decide)).trans w13_260
  have w14_264 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ap := (K14.w32 (by decide) (by decide)).trans w13_264
  have w14_378 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := (K14.w32 (by decide) (by decide)).trans w13_378
  have w14_37c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := (K14.w32 (by decide) (by decide)).trans w13_37c
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := (K14.w32 (by decide) (by decide)).trans w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := (K14.w32 (by decide) (by decide)).trans w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := (K14.w32 (by decide) (by decide)).trans w13_42c
  have w14_430 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := (K14.w32 (by decide) (by decide)).trans w13_430
  have w14_268 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = al := by rw [W14, g13_12]
  clear w13_264 w13_430 w13_42c w13_428 w13_424 w13_37c w13_378 w13_260 w13_25c w13_7c w13_64 w13_50 w13_44 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_12 g13_11 g13_10 g13_4 g13_3 g13_2 V13 E13 fR13 t13 rg13 W13 K13 fr13 s13 d13
  by_cases hne : al ≠ 0
  rotate_left
  · have hz : al = 0 := Decidable.of_not_not hne
    -- 0xE9C: branch, taken
    obtain ⟨n15, d15, u15⟩ := s14.taken E14.self 0x1000 sv_at_e9c
      (by decide) (by rw [g14_24, s14.zero]; exact br_beq_t hz)
    have s15 : St n15.mem SV n15 0x1000 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
    have m15 : n15.mem = n14.mem := u15.mem
    have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
    have t15 : Steps n0 n15 := t14.trans (.single d15)
    have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
    have E15 : SvCode n15.mem := E14.fr F fr15
    have V15 : SvSaves B n15.mem v := V14.same m15
    have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
    have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
    have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
    have g15_10 : reg n15 a0 = ap := by rw [u15.regs, g14_10]
    have g15_11 : reg n15 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by rw [u15.regs, g14_11]
    have g15_12 : reg n15 a2 = al := by rw [u15.regs, g14_12]
    have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, g14_18]
    have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, g14_19]
    have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [u15.regs, g14_20]
    have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, g14_21]
    have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, g14_22]
    have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [u15.regs, g14_23]
    have g15_24 : reg n15 (24 : Fin 32) = al := by rw [u15.regs, g14_24]
    have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, g14_25]
    have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, g14_26]
    have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [u15.regs, g14_27]
    have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4)] := by rw [m15]; exact keep_kk14
    clear keep_kk14
    have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := by rw [m15]; exact w14_44
    have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := by rw [m15]; exact w14_50
    have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m15]; exact w14_64
    have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [m15]; exact w14_7c
    have w15_25c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ap := by rw [m15]; exact w14_25c
    have w15_260 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = al := by rw [m15]; exact w14_260
    have w15_264 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ap := by rw [m15]; exact w14_264
    have w15_268 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = al := by rw [m15]; exact w14_268
    have w15_378 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m15]; exact w14_378
    have w15_37c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m15]; exact w14_37c
    have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := by rw [m15]; exact w14_424
    have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := by rw [m15]; exact w14_428
    have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := by rw [m15]; exact w14_42c
    have w15_430 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := by rw [m15]; exact w14_430
    clear w14_268 w14_430 w14_42c w14_428 w14_424 w14_37c w14_378 w14_264 w14_260 w14_25c w14_7c w14_64 w14_50 w14_44 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_12 g14_11 g14_10 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
    -- 0x1000: lw
    obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_1000 (off' := 0x1002) (by decide)
      (by rw [g15_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s16 : St n16.mem SV n16 0x1002 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans (.single d16)
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
    have g16_11 : reg n16 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_11]
    have g16_12 : reg n16 a2 = al := by rw [u16.regs, upd_ne (by decide) (by decide), g15_12]
    have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_20]
    have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = al := by rw [u16.regs, upd_ne (by decide) (by decide), g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = x27 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_27]
    have g16_10 : reg n16 a0 = BitVec.ofNat 32 0x0 := by
      rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g15_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr, w15_64]
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4)] := by rw [m16]; exact keep_kk15
    clear keep_kk15
    have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := by rw [m16]; exact w15_44
    have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := by rw [m16]; exact w15_50
    have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m16]; exact w15_64
    have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [m16]; exact w15_7c
    have w16_25c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ap := by rw [m16]; exact w15_25c
    have w16_260 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = al := by rw [m16]; exact w15_260
    have w16_264 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ap := by rw [m16]; exact w15_264
    have w16_268 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = al := by rw [m16]; exact w15_268
    have w16_378 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m16]; exact w15_378
    have w16_37c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m16]; exact w15_37c
    have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := by rw [m16]; exact w15_424
    have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := by rw [m16]; exact w15_428
    have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := by rw [m16]; exact w15_42c
    have w16_430 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := by rw [m16]; exact w15_430
    clear w15_430 w15_42c w15_428 w15_424 w15_37c w15_378 w15_268 w15_264 w15_260 w15_25c w15_7c w15_64 w15_50 w15_44 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_12 g15_11 g15_10 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15 hz
    -- 0x1002
    obtain ⟨n17, c17, u17⟩ := s16.block svTr71002 E16.self svTr71002_end
      ⟨trivial, trivial⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have s17 : St n17.mem SV n17 0x1006 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have rb17 : ∀ q, reg n17 q = (runBlock svTr71002 (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans c17
    have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by
      rw [rb17, runBlock_reg _ _ _ sp s16.zero (by decide), g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb17, runBlock_reg _ _ _ (3 : Fin 32) s16.zero (by decide), g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb17, runBlock_reg _ _ _ (4 : Fin 32) s16.zero (by decide), g16_4]
    have g17_11 : reg n17 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
      rw [rb17, runBlock_reg _ _ _ a1 s16.zero (by decide), g16_11]
    have g17_12 : reg n17 a2 = al := by
      rw [rb17, runBlock_reg _ _ _ a2 s16.zero (by decide), g16_12]
    have g17_18 : reg n17 (18 : Fin 32) = out := by
      rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by
      rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
    have g17_20 : reg n17 (20 : Fin 32) = x20 := by
      rw [rb17, runBlock_reg _ _ _ (20 : Fin 32) s16.zero (by decide), g16_20]
    have g17_21 : reg n17 (21 : Fin 32) = x21 := by
      rw [rb17, runBlock_reg _ _ _ (21 : Fin 32) s16.zero (by decide), g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = x22 := by
      rw [rb17, runBlock_reg _ _ _ (22 : Fin 32) s16.zero (by decide), g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = x23 := by
      rw [rb17, runBlock_reg _ _ _ (23 : Fin 32) s16.zero (by decide), g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = al := by
      rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = x25 := by
      rw [rb17, runBlock_reg _ _ _ (25 : Fin 32) s16.zero (by decide), g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = x26 := by
      rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = x27 := by
      rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
    have g17_10 : reg n17 a0 = aluEval .sltu (BitVec.ofNat 32 0x0) (BitVec.ofNat 32 0x0) := by
      rw [rb17]; simp +decide only [runBlock, BInstr.run, svTr71002, upd, ↓reduceIte]; rw [g16_10] <;> rfl
    have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4)] := by rw [m17]; exact keep_kk16
    clear keep_kk16
    have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := by rw [m17]; exact w16_44
    have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := by rw [m17]; exact w16_50
    have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m17]; exact w16_64
    have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [m17]; exact w16_7c
    have w17_25c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ap := by rw [m17]; exact w16_25c
    have w17_260 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = al := by rw [m17]; exact w16_260
    have w17_264 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ap := by rw [m17]; exact w16_264
    have w17_268 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = al := by rw [m17]; exact w16_268
    have w17_378 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m17]; exact w16_378
    have w17_37c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m17]; exact w16_37c
    have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := by rw [m17]; exact w16_424
    have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := by rw [m17]; exact w16_428
    have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := by rw [m17]; exact w16_42c
    have w17_430 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := by rw [m17]; exact w16_430
    clear w16_430 w16_42c w16_428 w16_424 w16_37c w16_378 w16_268 w16_264 w16_260 w16_25c w16_7c w16_64 w16_50 w16_44 g16_10 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_12 g16_11 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
    -- 0x1006: lw
    obtain ⟨n18, d18, u18⟩ := s17.lw E17.self sv_at_1006 (off' := 0x1008) (by decide)
      (by rw [g17_2, show B + 0x21A0 + 0x7C = B + 0x21A0 + BitVec.ofNat 32 0x7C by sv_addr]; exact sv_al F (by decide) (by decide))
    have s18 : St n18.mem SV n18 0x1008 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
    have m18 : n18.mem = n17.mem := u18.mem
    have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
    have t18 : Steps n0 n18 := t17.trans (.single d18)
    have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
    have E18 : SvCode n18.mem := E17.fr F fr18
    have V18 : SvSaves B n18.mem v := V17.same m18
    have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
    have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
    have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
    have g18_10 : reg n18 a0 = aluEval .sltu (BitVec.ofNat 32 0x0) (BitVec.ofNat 32 0x0) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_10]
    have g18_12 : reg n18 a2 = al := by rw [u18.regs, upd_ne (by decide) (by decide), g17_12]
    have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
    have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
    have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_20]
    have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_21]
    have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_22]
    have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_23]
    have g18_24 : reg n18 (24 : Fin 32) = al := by rw [u18.regs, upd_ne (by decide) (by decide), g17_24]
    have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_25]
    have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_26]
    have g18_27 : reg n18 (27 : Fin 32) = x27 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_27]
    have g18_11 : reg n18 a1 = BitVec.ofNat 32 0x0 := by
      rw [u18.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g17_2, show B + 0x21A0 + 0x7C = B + 0x21A0 + BitVec.ofNat 32 0x7C by sv_addr, w17_7c]
    have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4)] := by rw [m18]; exact keep_kk17
    clear keep_kk17
    have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := by rw [m18]; exact w17_44
    have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := by rw [m18]; exact w17_50
    have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m18]; exact w17_64
    have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [m18]; exact w17_7c
    have w18_25c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ap := by rw [m18]; exact w17_25c
    have w18_260 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = al := by rw [m18]; exact w17_260
    have w18_264 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ap := by rw [m18]; exact w17_264
    have w18_268 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = al := by rw [m18]; exact w17_268
    have w18_378 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m18]; exact w17_378
    have w18_37c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m18]; exact w17_37c
    have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := by rw [m18]; exact w17_424
    have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := by rw [m18]; exact w17_428
    have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := by rw [m18]; exact w17_42c
    have w18_430 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := by rw [m18]; exact w17_430
    clear w17_430 w17_42c w17_428 w17_424 w17_37c w17_378 w17_268 w17_264 w17_260 w17_25c w17_7c w17_64 w17_50 w17_44 g17_10 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_12 g17_11 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
    -- 0x1008
    obtain ⟨n19, c19, u19⟩ := s18.block svTr71008 E18.self svTr71008_end
      ⟨trivial, trivial⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have s19 : St n19.mem SV n19 0x100A (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have rb19 : ∀ q, reg n19 q = (runBlock svTr71008 (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
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
    have g19_11 : reg n19 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb19, runBlock_reg _ _ _ a1 s18.zero (by decide), g18_11]
    have g19_12 : reg n19 a2 = al := by
      rw [rb19, runBlock_reg _ _ _ a2 s18.zero (by decide), g18_12]
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
    have g19_24 : reg n19 (24 : Fin 32) = al := by
      rw [rb19, runBlock_reg _ _ _ (24 : Fin 32) s18.zero (by decide), g18_24]
    have g19_25 : reg n19 (25 : Fin 32) = x25 := by
      rw [rb19, runBlock_reg _ _ _ (25 : Fin 32) s18.zero (by decide), g18_25]
    have g19_26 : reg n19 (26 : Fin 32) = x26 := by
      rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
    have g19_27 : reg n19 (27 : Fin 32) = x27 := by
      rw [rb19, runBlock_reg _ _ _ (27 : Fin 32) s18.zero (by decide), g18_27]
    have g19_10 : reg n19 a0 = (aluEval .sltu (BitVec.ofNat 32 0x0) (BitVec.ofNat 32 0x0)) &&& (BitVec.ofNat 32 0x0) := by
      rw [rb19]; simp +decide only [runBlock, BInstr.run, svTr71008, upd, ↓reduceIte]; rw [g18_10, g18_11] <;> rfl
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4)] := by rw [m19]; exact keep_kk18
    clear keep_kk18
    have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := by rw [m19]; exact w18_44
    have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := by rw [m19]; exact w18_50
    have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m19]; exact w18_64
    have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [m19]; exact w18_7c
    have w19_25c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ap := by rw [m19]; exact w18_25c
    have w19_260 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = al := by rw [m19]; exact w18_260
    have w19_264 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ap := by rw [m19]; exact w18_264
    have w19_268 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = al := by rw [m19]; exact w18_268
    have w19_378 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m19]; exact w18_378
    have w19_37c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m19]; exact w18_37c
    have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := by rw [m19]; exact w18_424
    have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := by rw [m19]; exact w18_428
    have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := by rw [m19]; exact w18_42c
    have w19_430 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := by rw [m19]; exact w18_430
    clear w18_430 w18_42c w18_428 w18_424 w18_37c w18_378 w18_268 w18_264 w18_260 w18_25c w18_7c w18_64 w18_50 w18_44 g18_11 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_12 g18_10 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
    -- 0x100A: branch, taken
    obtain ⟨n20, d20, u20⟩ := s19.taken E19.self 0x12B8 sv_at_100a
      (by decide) (by rw [g19_10, s19.zero]; decide)
    have s20 : St n20.mem SV n20 0x12B8 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
    have t20 : Steps n0 n20 := t19.trans (.single d20)
    have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
    have E20 : SvCode n20.mem := E19.fr F fr20
    have V20 : SvSaves B n20.mem v := V19.same m20
    have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, g19_2]
    have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, g19_3]
    have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, g19_4]
    have g20_10 : reg n20 a0 = (aluEval .sltu (BitVec.ofNat 32 0x0) (BitVec.ofNat 32 0x0)) &&& (BitVec.ofNat 32 0x0) := by rw [u20.regs, g19_10]
    have g20_11 : reg n20 a1 = BitVec.ofNat 32 0x0 := by rw [u20.regs, g19_11]
    have g20_12 : reg n20 a2 = al := by rw [u20.regs, g19_12]
    have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, g19_19]
    have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [u20.regs, g19_20]
    have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [u20.regs, g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [u20.regs, g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [u20.regs, g19_23]
    have g20_24 : reg n20 (24 : Fin 32) = al := by rw [u20.regs, g19_24]
    have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [u20.regs, g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [u20.regs, g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = x27 := by rw [u20.regs, g19_27]
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4)] := by rw [m20]; exact keep_kk19
    clear keep_kk19
    have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := by rw [m20]; exact w19_44
    have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := by rw [m20]; exact w19_50
    have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m20]; exact w19_64
    have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [m20]; exact w19_7c
    have w20_25c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ap := by rw [m20]; exact w19_25c
    have w20_260 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = al := by rw [m20]; exact w19_260
    have w20_264 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ap := by rw [m20]; exact w19_264
    have w20_268 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = al := by rw [m20]; exact w19_268
    have w20_378 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m20]; exact w19_378
    have w20_37c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m20]; exact w19_37c
    have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := by rw [m20]; exact w19_424
    have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := by rw [m20]; exact w19_428
    have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := by rw [m20]; exact w19_42c
    have w20_430 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := by rw [m20]; exact w19_430
    clear w19_430 w19_42c w19_428 w19_424 w19_37c w19_378 w19_268 w19_264 w19_260 w19_25c w19_7c w19_64 w19_50 w19_44 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_12 g19_11 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
    -- 0x12B8
    obtain ⟨n21, c21, u21⟩ := s20.block svTr712b8 E20.self svTr712b8_end
      ⟨trivial, trivial⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have s21 : St n21.mem SV n21 0x12BA (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have rb21 : ∀ q, reg n21 q = (runBlock svTr712b8 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
    have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
    have t21 : Steps n0 n21 := t20.trans c21
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.same m21
    have g21_2 : reg n21 sp = B + 0x21A0 := by
      rw [rb21, runBlock_reg _ _ _ sp s20.zero (by decide), g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb21, runBlock_reg _ _ _ (3 : Fin 32) s20.zero (by decide), g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb21, runBlock_reg _ _ _ (4 : Fin 32) s20.zero (by decide), g20_4]
    have g21_10 : reg n21 a0 = (aluEval .sltu (BitVec.ofNat 32 0x0) (BitVec.ofNat 32 0x0)) &&& (BitVec.ofNat 32 0x0) := by
      rw [rb21, runBlock_reg _ _ _ a0 s20.zero (by decide), g20_10]
    have g21_11 : reg n21 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb21, runBlock_reg _ _ _ a1 s20.zero (by decide), g20_11]
    have g21_12 : reg n21 a2 = al := by
      rw [rb21, runBlock_reg _ _ _ a2 s20.zero (by decide), g20_12]
    have g21_18 : reg n21 (18 : Fin 32) = out := by
      rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by
      rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
    have g21_20 : reg n21 (20 : Fin 32) = x20 := by
      rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
    have g21_21 : reg n21 (21 : Fin 32) = x21 := by
      rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = x22 := by
      rw [rb21, runBlock_reg _ _ _ (22 : Fin 32) s20.zero (by decide), g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = x23 := by
      rw [rb21, runBlock_reg _ _ _ (23 : Fin 32) s20.zero (by decide), g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = al := by
      rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = x25 := by
      rw [rb21, runBlock_reg _ _ _ (25 : Fin 32) s20.zero (by decide), g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = x26 := by
      rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = x27 := by
      rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
    have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb21]; simp +decide only [runBlock, BInstr.run, svTr712b8, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g20_2, g20_3, g20_4, g20_10, g20_11, g20_12, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := by rw [m21]; exact w20_44
    have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := by rw [m21]; exact w20_50
    have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m21]; exact w20_64
    have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [m21]; exact w20_7c
    have w21_25c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ap := by rw [m21]; exact w20_25c
    have w21_260 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = al := by rw [m21]; exact w20_260
    have w21_264 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ap := by rw [m21]; exact w20_264
    have w21_268 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = al := by rw [m21]; exact w20_268
    have w21_378 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m21]; exact w20_378
    have w21_37c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m21]; exact w20_37c
    have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := by rw [m21]; exact w20_424
    have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := by rw [m21]; exact w20_428
    have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := by rw [m21]; exact w20_42c
    have w21_430 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := by rw [m21]; exact w20_430
    clear w20_430 w20_42c w20_428 w20_424 w20_37c w20_378 w20_268 w20_264 w20_260 w20_25c w20_7c w20_64 w20_50 w20_44 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_12 g20_11 g20_10 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
    -- 0x12BA: j
    obtain ⟨n22, d22, u22⟩ := s21.jump E21.self sv_at_12ba (off' := 0x7A4) (by decide)
      (by rw [s21.pc]; decide)
    have s22 : St n22.mem SV n22 0x7A4 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
    have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u22.regs, g21_8]
    have g22_10 : reg n22 a0 = (aluEval .sltu (BitVec.ofNat 32 0x0) (BitVec.ofNat 32 0x0)) &&& (BitVec.ofNat 32 0x0) := by rw [u22.regs, g21_10]
    have g22_11 : reg n22 a1 = BitVec.ofNat 32 0x0 := by rw [u22.regs, g21_11]
    have g22_12 : reg n22 a2 = al := by rw [u22.regs, g21_12]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [u22.regs, g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = al := by rw [u22.regs, g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [u22.regs, g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = x27 := by rw [u22.regs, g21_27]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := by rw [m22]; exact w21_44
    have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := by rw [m22]; exact w21_50
    have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m22]; exact w21_64
    have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [m22]; exact w21_7c
    have w22_25c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ap := by rw [m22]; exact w21_25c
    have w22_260 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = al := by rw [m22]; exact w21_260
    have w22_264 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ap := by rw [m22]; exact w21_264
    have w22_268 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = al := by rw [m22]; exact w21_268
    have w22_378 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m22]; exact w21_378
    have w22_37c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m22]; exact w21_37c
    have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := by rw [m22]; exact w21_424
    have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := by rw [m22]; exact w21_428
    have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := by rw [m22]; exact w21_42c
    have w22_430 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := by rw [m22]; exact w21_430
    clear w21_430 w21_42c w21_428 w21_424 w21_37c w21_378 w21_268 w21_264 w21_260 w21_25c w21_7c w21_64 w21_50 w21_44 g21_8 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_12 g21_11 g21_10 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hne h0'), sv_fail F E22 s22 t22 (fun x hx => (fR22 x hx).trans (fM x hx).symm) V22 hret g22_2 g22_18 hO g22_3 g22_4⟩
  -- 0xE9C: branch, not taken
  obtain ⟨n15, d15, u15⟩ := s14.notTaken E14.self 0xEA0 sv_at_e9c
    (by decide) (by rw [g14_24, s14.zero]; exact br_beq_f hne)
  have s15 : St n15.mem SV n15 0xEA0 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
  have g15_10 : reg n15 a0 = ap := by rw [u15.regs, g14_10]
  have g15_11 : reg n15 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by rw [u15.regs, g14_11]
  have g15_12 : reg n15 a2 = al := by rw [u15.regs, g14_12]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [u15.regs, g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [u15.regs, g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = al := by rw [u15.regs, g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [u15.regs, g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = aq := by rw [m15]; exact w14_44
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ah := by rw [m15]; exact w14_50
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 := by rw [m15]; exact w14_64
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 := by rw [m15]; exact w14_7c
  have w15_25c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = ap := by rw [m15]; exact w14_25c
  have w15_260 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = al := by rw [m15]; exact w14_260
  have w15_264 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ap := by rw [m15]; exact w14_264
  have w15_268 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = al := by rw [m15]; exact w14_268
  have w15_378 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip := by rw [m15]; exact w14_378
  have w15_37c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil := by rw [m15]; exact w14_37c
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ap := by rw [m15]; exact w14_424
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = al := by rw [m15]; exact w14_428
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = aq := by rw [m15]; exact w14_42c
  have w15_430 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = ah := by rw [m15]; exact w14_430
  clear w14_268 w14_430 w14_42c w14_428 w14_424 w14_37c w14_378 w14_264 w14_260 w14_25c w14_7c w14_64 w14_50 w14_44 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_12 g14_11 g14_10 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
  exact .inr ⟨hne, n15, t15, s15, E15, V15, fR15, g15_2, g15_3, g15_4, g15_18, g15_19, g15_20, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, w15_44, w15_50, w15_64, w15_7c, w15_25c, w15_260, w15_264, w15_268, w15_378, w15_37c, keep_kk15.mono (by decide)⟩

end C3.RV32.Sv
