import C3BootProofs.Proofs.SvRk

/-!
# `sigstore::verify`: the log entry's leaf hash

From 0x189A to 0x1974: SHA-256 of the entry's canonical body, built from its constant parts and the base64 of the image digest, the image signature, and the leaf certificate, goes to offset 0x400.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svRl189e : List BInstr :=
  [.aluImm .add a0 sp 0x460, .lui a1 0x3FCC4000, .aluImm .add a1 a1 0x118, .aluImm .add a2 x0 0x20]
theorem svRl189e_end : blockEnd sigstoreVerifyCode 0x189E svRl189e = some 0x18AE := by
  simp only [svRl189e]
  rw [blockEnd, sv_at_189e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_18a2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_18a6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_18aa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svRl18be : List BInstr :=
  [.lui a1 0x3FCC4000, .aluImm .add a1 a1 0x648, .aluImm .add a0 sp 0x420, .aluImm .add a2 x0 0x1]
theorem svRl18be_end : blockEnd sigstoreVerifyCode 0x18BE svRl18be = some 0x18CC := by
  simp only [svRl18be]
  rw [blockEnd, sv_at_18be]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_18c2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_18c6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_18ca]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svRl18d4 : List BInstr :=
  [.lui a1 0x3FCC4000, .aluImm .add a1 a1 0x560, .aluImm .add a0 sp 0x420, .aluImm .add a2 x0 0x71]
theorem svRl18d4_end : blockEnd sigstoreVerifyCode 0x18D4 svRl18d4 = some 0x18E4 := by
  simp only [svRl18d4]
  rw [blockEnd, sv_at_18d4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_18d8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_18dc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_18e0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svRl18ec : List BInstr :=
  [.aluImm .add a1 x0 0x20, .aluImm .add a2 sp 0x420, .alu .add a0 x0 (20 : Fin 32)]
theorem svRl18ec_end : blockEnd sigstoreVerifyCode 0x18EC svRl18ec = some 0x18F6 := by
  simp only [svRl18ec]
  rw [blockEnd, sv_at_18ec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_18f0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_18f4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svRl18fe : List BInstr :=
  [.lui a1 0x3FCC4000, .aluImm .add a1 a1 0x5D1, .aluImm .add a0 sp 0x420, .aluImm .add a2 x0 0x1B, .aluImm .add (20 : Fin 32) x0 0x1B]
theorem svRl18fe_end : blockEnd sigstoreVerifyCode 0x18FE svRl18fe = some 0x190E := by
  simp only [svRl18fe]
  rw [blockEnd, sv_at_18fe]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1902]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1906]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_190a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_190c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svRl1916 : List BInstr :=
  [.aluImm .add a2 sp 0x420]
theorem svRl1916_end : blockEnd sigstoreVerifyCode 0x1916 svRl1916 = some 0x191A := by
  simp only [svRl1916]
  rw [blockEnd, sv_at_1916]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svRl1926 : List BInstr :=
  [.lui a1 0x3FCC4000, .aluImm .add a1 a1 0x5EC, .aluImm .add a0 sp 0x420, .aluImm .add a2 x0 0x54]
theorem svRl1926_end : blockEnd sigstoreVerifyCode 0x1926 svRl1926 = some 0x1936 := by
  simp only [svRl1926]
  rw [blockEnd, sv_at_1926]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_192a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_192e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1932]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svRl193e : List BInstr :=
  [.aluImm .add a2 sp 0x420]
theorem svRl193e_end : blockEnd sigstoreVerifyCode 0x193E svRl193e = some 0x1942 := by
  simp only [svRl193e]
  rw [blockEnd, sv_at_193e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svRl1944 : List BInstr :=
  [.alu .add a1 x0 (22 : Fin 32)]
theorem svRl1944_end : blockEnd sigstoreVerifyCode 0x1944 svRl1944 = some 0x1946 := by
  simp only [svRl1944]
  rw [blockEnd, sv_at_1944]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svRl194e : List BInstr :=
  [.lui a1 0x3FCC4000, .aluImm .add a1 a1 0x640, .aluImm .add a0 sp 0x420, .aluImm .add a2 x0 0x7]
theorem svRl194e_end : blockEnd sigstoreVerifyCode 0x194E svRl194e = some 0x195C := by
  simp only [svRl194e]
  rw [blockEnd, sv_at_194e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1952]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1956]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_195a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svRl1964 : List BInstr :=
  [.aluImm .add a0 sp 0x400, .aluImm .add a1 sp 0x420]
theorem svRl1964_end : blockEnd sigstoreVerifyCode 0x1964 svRl1964 = some 0x196C := by
  simp only [svRl1964]
  rw [blockEnd, sv_at_1964]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1968]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_rl {B out bp x20 x21 x22 x23 x24 x25 x26 x27 w64 w74 w70 w68 w6c : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x189A (reg n0))
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
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = x27)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64)
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68)
    (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74)
    (S2 : SvSha2Code M0)
    (RS : SvRoSep B)
    (RK0 : SvRkCode M0)
    (dgi_in : SvIn B x20 32)
    (sig_in : SvIn B w70 w68.toNat)
    (crt_in : SvIn B w6c x22.toNat) :
    (¬ (True) ∧ SvErrRet B out v n0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1974 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = BitVec.ofNat 32 0x1B ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
        memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 32 = sha256 ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes M0 (w70) ((w68).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid2Address)) (0x54) ++ base64Encode (memBytes M0 (w6c) ((x22).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPostAddress)) (0x7)) ∧
        SvKeepL B n0.mem n'.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x400, 0x20)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x189A: sb
  obtain ⟨n1, d1, s1, fr1, K1, W1, rg1⟩ := sv_sb F E0 s0 sv_at_189a (off' := 0x189E) (c := 0x45F)
    (by decide) (by rw [g0_2]; sv_addr) (by decide)
  have t1 : Steps n0 n1 := t0.trans d1
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.keep K1 (by decide)
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [rg1 sp, g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg1 (3 : Fin 32), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg1 (4 : Fin 32), g0_4]
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
  have keep_kk1 : SvKeepL B n0.mem n1.mem [(0x45F, 0x1)] := (SvKeepL.refl : SvKeepL B n0.mem n0.mem []).trans K1.toL
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K1.w32 (by decide) (by decide)).trans w0_64
  have w1_68 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K1.w32 (by decide) (by decide)).trans w0_68
  have w1_6c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K1.w32 (by decide) (by decide)).trans w0_6c
  have w1_70 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K1.w32 (by decide) (by decide)).trans w0_70
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K1.w32 (by decide) (by decide)).trans w0_74
  have b1_45f : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x45F) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [W1, s0.zero]; rfl
  -- 0x189E
  obtain ⟨n2, c2, u2⟩ := s1.block svRl189e E1.self svRl189e_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have s2 : St n2.mem SV n2 0x18AE (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have rb2 : ∀ q, reg n2 q = (runBlock svRl189e (n1.mem, reg n1)).2 q := fun q => by rw [u2.regs]
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
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by
    rw [rb2, runBlock_reg _ _ _ (26 : Fin 32) s1.zero (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = x27 := by
    rw [rb2, runBlock_reg _ _ _ (27 : Fin 32) s1.zero (by decide), g1_27]
  have g2_10 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0x460 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, svRl189e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_24, g1_25, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g2_11 : reg n2 a1 = BitVec.ofNat 32 (img% shaIVAddress) := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, svRl189e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_24, g1_25, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g2_12 : reg n2 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, svRl189e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_24, g1_25, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x45F, 0x1)] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m2]; exact w1_64
  have w2_68 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m2]; exact w1_68
  have w2_6c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m2]; exact w1_6c
  have w2_70 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m2]; exact w1_70
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m2]; exact w1_74
  have b2_45f : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x45F) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m2]; exact b1_45f
  clear b1_45f w1_74 w1_70 w1_6c w1_68 w1_64 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 rg1 W1 K1 fr1 s1 d1 g0_4 g0_3 fR0 t0
  -- 0x18AE: memcpy from outside the stack
  obtain ⟨n3, P3, K3, X3⟩ := sv_mcRo2 (c := 0x460) (N := 0x20) F RS E2 s2 sv_at_18ae sv_at_18b2
    (by decide) (by decide) g2_2 g2_10 g2_11 g2_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s3 := P3.st
  have fr3 := P3.fr
  have t3 : Steps n0 n3 := t2.trans P3.steps
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.keep K3 (by decide)
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [P3.regs sp (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P3.regs (3 : Fin 32) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P3.regs (4 : Fin 32) (by decide), g2_4]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [P3.regs (18 : Fin 32) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [P3.regs (19 : Fin 32) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [P3.regs (20 : Fin 32) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [P3.regs (21 : Fin 32) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [P3.regs (22 : Fin 32) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [P3.regs (23 : Fin 32) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = x24 := by rw [P3.regs (24 : Fin 32) (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [P3.regs (25 : Fin 32) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [P3.regs (26 : Fin 32) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = x27 := by rw [P3.regs (27 : Fin 32) (by decide), g2_27]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x45F, 0x1), (0x460, 0x20)] := keep_kk2.trans K3.toL
  clear keep_kk2
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K3.w32 (by decide) (by decide)).trans w2_64
  have w3_68 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K3.w32 (by decide) (by decide)).trans w2_68
  have w3_6c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K3.w32 (by decide) (by decide)).trans w2_6c
  have w3_70 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K3.w32 (by decide) (by decide)).trans w2_70
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K3.w32 (by decide) (by decide)).trans w2_74
  have b3_45f : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x45F) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K3.b8 (by decide) (by decide)).trans b2_45f
  have q3_460 : ∀ j, j < 32 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x460 + j)) = M0 ((BitVec.ofNat 32 (img% shaIVAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X3 j hj).trans (fR2 _ (SvRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear b2_45f w2_74 w2_70 w2_6c w2_68 w2_64 g2_12 g2_11 g2_10 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 rb2 s2 m2 u2 c2
  -- 0x18B6: sw
  obtain ⟨n4, d4, s4, fr4, K4, W4, rg4⟩ := sv_sw F E3 s3 sv_at_18b6 (off' := 0x18BA) (c := 0x480)
    (by decide) (by rw [g3_2]; sv_addr) (by decide) (by decide)
  have t4 : Steps n0 n4 := t3.trans d4
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.keep K4 (by decide)
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [rg4 sp, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg4 (3 : Fin 32), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg4 (4 : Fin 32), g3_4]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [rg4 (18 : Fin 32), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [rg4 (19 : Fin 32), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [rg4 (20 : Fin 32), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [rg4 (21 : Fin 32), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [rg4 (22 : Fin 32), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [rg4 (23 : Fin 32), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = x24 := by rw [rg4 (24 : Fin 32), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [rg4 (25 : Fin 32), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [rg4 (26 : Fin 32), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = x27 := by rw [rg4 (27 : Fin 32), g3_27]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4)] := keep_kk3.trans K4.toL
  clear keep_kk3
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K4.w32 (by decide) (by decide)).trans w3_64
  have w4_68 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K4.w32 (by decide) (by decide)).trans w3_68
  have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K4.w32 (by decide) (by decide)).trans w3_6c
  have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K4.w32 (by decide) (by decide)).trans w3_70
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K4.w32 (by decide) (by decide)).trans w3_74
  have b4_45f : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x45F) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K4.b8 (by decide) (by decide)).trans b3_45f
  have w4_480 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x480) = BitVec.ofNat 32 0x0 := by rw [W4, s3.zero]; rfl
  have q4_460 : ∀ j, j < 32 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x460 + j)) = M0 ((BitVec.ofNat 32 (img% shaIVAddress)) + BitVec.ofNat 32 j) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_460 j hj)
  clear q3_460 b3_45f w3_74 w3_70 w3_6c w3_68 w3_64 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 s3 X3 K3 P3
  -- 0x18BA: sw
  obtain ⟨n5, d5, s5, fr5, K5, W5, rg5⟩ := sv_sw F E4 s4 sv_at_18ba (off' := 0x18BE) (c := 0x484)
    (by decide) (by rw [g4_2]; sv_addr) (by decide) (by decide)
  have t5 : Steps n0 n5 := t4.trans d5
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.keep K5 (by decide)
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [rg5 sp, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg5 (3 : Fin 32), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg5 (4 : Fin 32), g4_4]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [rg5 (18 : Fin 32), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [rg5 (19 : Fin 32), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [rg5 (20 : Fin 32), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [rg5 (21 : Fin 32), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [rg5 (22 : Fin 32), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [rg5 (23 : Fin 32), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by rw [rg5 (24 : Fin 32), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [rg5 (25 : Fin 32), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [rg5 (26 : Fin 32), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = x27 := by rw [rg5 (27 : Fin 32), g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4)] := keep_kk4.trans K5.toL
  clear keep_kk4
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K5.w32 (by decide) (by decide)).trans w4_64
  have w5_68 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K5.w32 (by decide) (by decide)).trans w4_68
  have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K5.w32 (by decide) (by decide)).trans w4_6c
  have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K5.w32 (by decide) (by decide)).trans w4_70
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K5.w32 (by decide) (by decide)).trans w4_74
  have w5_480 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x480) = BitVec.ofNat 32 0x0 := (K5.w32 (by decide) (by decide)).trans w4_480
  have b5_45f : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x45F) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K5.b8 (by decide) (by decide)).trans b4_45f
  have w5_484 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x484) = BitVec.ofNat 32 0x0 := by rw [W5, s4.zero]; rfl
  have q5_460 : ∀ j, j < 32 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x460 + j)) = M0 ((BitVec.ofNat 32 (img% shaIVAddress)) + BitVec.ofNat 32 j) := fun j hj => (K5.range (by decide) (by decide) j hj).trans (q4_460 j hj)
  clear q4_460 w4_480 b4_45f w4_74 w4_70 w4_6c w4_68 w4_64 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_4 g4_3 g4_2 V4 E4 fR4 t4 rg4 W4 K4 fr4 s4 d4
  have H5 := hasher_init_f b5_45f q5_460 S2.iv w5_480 w5_484
  -- 0x18BE
  obtain ⟨n6, c6, u6⟩ := s5.block svRl18be E5.self svRl18be_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0x18CC (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svRl18be (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans c6
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by
    rw [rb6, runBlock_reg _ _ _ sp s5.zero (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb6, runBlock_reg _ _ _ (3 : Fin 32) s5.zero (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb6, runBlock_reg _ _ _ (4 : Fin 32) s5.zero (by decide), g5_4]
  have g6_18 : reg n6 (18 : Fin 32) = out := by
    rw [rb6, runBlock_reg _ _ _ (18 : Fin 32) s5.zero (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by
    rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by
    rw [rb6, runBlock_reg _ _ _ (20 : Fin 32) s5.zero (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by
    rw [rb6, runBlock_reg _ _ _ (21 : Fin 32) s5.zero (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by
    rw [rb6, runBlock_reg _ _ _ (22 : Fin 32) s5.zero (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by
    rw [rb6, runBlock_reg _ _ _ (23 : Fin 32) s5.zero (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = x24 := by
    rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by
    rw [rb6, runBlock_reg _ _ _ (25 : Fin 32) s5.zero (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by
    rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = x27 := by
    rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svRl18be, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_11 : reg n6 a1 = BitVec.ofNat 32 (img% svRekorLeafAddress) := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svRl18be, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_12 : reg n6 a2 = BitVec.ofNat 32 0x1 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svRl18be, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m6]; exact w5_64
  have w6_68 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m6]; exact w5_68
  have w6_6c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m6]; exact w5_6c
  have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m6]; exact w5_70
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m6]; exact w5_74
  have w6_480 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x480) = BitVec.ofNat 32 0x0 := by rw [m6]; exact w5_480
  have w6_484 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x484) = BitVec.ofNat 32 0x0 := by rw [m6]; exact w5_484
  have b6_45f : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x45F) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m6]; exact b5_45f
  have q6_460 : ∀ j, j < 32 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x460 + j)) = M0 ((BitVec.ofNat 32 (img% shaIVAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m6]; exact q5_460 j hj
  clear q5_460 w5_484 b5_45f w5_480 w5_74 w5_70 w5_6c w5_68 w5_64 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 rg5 W5 K5 fr5 s5 d5
  have H6 : HasherAt n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) ([]) := by rw [m6]; exact H5
  -- 0x18CC: sv_updF
  obtain ⟨n7, c7, s7, sp7, rk7, K7, H7, fr7⟩ := sv_updF (hc := 0x420) (nl := 0x1) (msg := [])
    F E6 (S2.sv FW RS fR6) RS s6 sv_at_18cc sv_at_18d0 (by decide) (by decide) g6_2
    g6_10 g6_11 g6_12 (by decide) (by decide) (Or.inr ⟨by decide, by decide⟩) H6 (by decide)
    (by simp only [List.length_append, List.length_nil, memBytes_length]; omega)
  have t7 : Steps n0 n7 := t6.trans c7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.keepL K7 (by decide)
  rw [sv_mbRo2 RS fR6 (Or.inr ⟨by decide, by decide⟩)] at H7
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
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [rk7 (26 : Fin 32) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = x27 := by rw [rk7 (27 : Fin 32) (by decide), g6_27]
  have g7_2 : reg n7 sp = B + 0x21A0 := sp7
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68)] := keep_kk6.trans K7
  clear keep_kk6
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K7.w32 (by decide) (by decide)).trans w6_64
  have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K7.w32 (by decide) (by decide)).trans w6_68
  have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K7.w32 (by decide) (by decide)).trans w6_6c
  have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K7.w32 (by decide) (by decide)).trans w6_70
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K7.w32 (by decide) (by decide)).trans w6_74
  clear q6_460 b6_45f w6_484 w6_480 w6_74 w6_70 w6_6c w6_68 w6_64 g6_12 g6_11 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  -- 0x18D4
  obtain ⟨n8, c8, u8⟩ := s7.block svRl18d4 E7.self svRl18d4_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem SV n8 0x18E4 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock svRl18d4 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by
    rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = x27 := by
    rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svRl18d4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g8_11 : reg n8 a1 = BitVec.ofNat 32 (img% svRekorPreAddress) := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svRl18d4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g8_12 : reg n8 a2 = BitVec.ofNat 32 0x71 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svRl18d4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m8]; exact w7_64
  have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m8]; exact w7_68
  have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m8]; exact w7_6c
  have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m8]; exact w7_70
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m8]; exact w7_74
  clear w7_74 w7_70 w7_6c w7_68 w7_64 g7_2 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_4 g7_3 V7 E7 fR7 t7 fr7 K7 rk7 sp7 s7 c7
  have H8 : HasherAt n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1)) := by rw [m8]; exact H7
  -- 0x18E4: sv_updF
  obtain ⟨n9, c9, s9, sp9, rk9, K9, H9, fr9⟩ := sv_updF (hc := 0x420) (nl := 0x71) (msg := [] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1))
    F E8 (S2.sv FW RS fR8) RS s8 sv_at_18e4 sv_at_18e8 (by decide) (by decide) g8_2
    g8_10 g8_11 g8_12 (by decide) (by decide) (Or.inr ⟨by decide, by decide⟩) H8 (by decide)
    (by simp only [List.length_append, List.length_nil, memBytes_length]; omega)
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keepL K9 (by decide)
  rw [sv_mbRo2 RS fR8 (Or.inr ⟨by decide, by decide⟩)] at H9
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk9 (3 : Fin 32) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk9 (4 : Fin 32) (by decide), g8_4]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rk9 (18 : Fin 32) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rk9 (19 : Fin 32) (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [rk9 (20 : Fin 32) (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [rk9 (21 : Fin 32) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [rk9 (22 : Fin 32) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [rk9 (23 : Fin 32) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = x24 := by rw [rk9 (24 : Fin 32) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [rk9 (25 : Fin 32) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [rk9 (26 : Fin 32) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = x27 := by rw [rk9 (27 : Fin 32) (by decide), g8_27]
  have g9_2 : reg n9 sp = B + 0x21A0 := sp9
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68)] := keep_kk8.trans K9
  clear keep_kk8
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K9.w32 (by decide) (by decide)).trans w8_64
  have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K9.w32 (by decide) (by decide)).trans w8_68
  have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K9.w32 (by decide) (by decide)).trans w8_6c
  have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K9.w32 (by decide) (by decide)).trans w8_70
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K9.w32 (by decide) (by decide)).trans w8_74
  clear w8_74 w8_70 w8_6c w8_68 w8_64 g8_12 g8_11 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  -- 0x18EC
  obtain ⟨n10, c10, u10⟩ := s9.block svRl18ec E9.self svRl18ec_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0x18F6 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svRl18ec (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = x27 := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_10 : reg n10 a0 = x20 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svRl18ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g10_11 : reg n10 a1 = BitVec.ofNat 32 0x20 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svRl18ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g10_12 : reg n10 a2 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svRl18ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
  have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m10]; exact w9_68
  have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m10]; exact w9_6c
  have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m10]; exact w9_70
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m10]; exact w9_74
  clear w9_74 w9_70 w9_6c w9_68 w9_64 g9_2 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_4 g9_3 V9 E9 fR9 t9 fr9 K9 rk9 sp9 s9 c9
  have H10 : HasherAt n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71)) := by rw [m10]; exact H9
  -- 0x18F6: sv_b64eF
  obtain ⟨n11, c11, s11, sp11, rk11, K11, H11, fr11⟩ := sv_b64eF (hc := 0x420) (nl := 32) (msg := [] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71))
    F E10 (S2.sv FW RS fR10) (RK0.sv FW fR10) RS s10 sv_at_18f6 sv_at_18fa (by decide) (by decide) g10_2
    g10_10 g10_11 g10_12 (by decide) (by decide) (.inl dgi_in) H10
    (by simp only [List.length_append, List.length_nil, memBytes_length]; omega)
  have t11 : Steps n0 n11 := t10.trans c11
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.keepL K11 (by decide)
  rw [sv_mbRo2 RS fR10 (.inl dgi_in)] at H11
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk11 (3 : Fin 32) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk11 (4 : Fin 32) (by decide), g10_4]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [rk11 (18 : Fin 32) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [rk11 (19 : Fin 32) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [rk11 (20 : Fin 32) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [rk11 (21 : Fin 32) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [rk11 (22 : Fin 32) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [rk11 (23 : Fin 32) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [rk11 (24 : Fin 32) (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [rk11 (25 : Fin 32) (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [rk11 (26 : Fin 32) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [rk11 (27 : Fin 32) (by decide), g10_27]
  have g11_2 : reg n11 sp = B + 0x21A0 := sp11
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := keep_kk10.trans K11
  clear keep_kk10
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K11.w32 (by decide) (by decide)).trans w10_64
  have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K11.w32 (by decide) (by decide)).trans w10_68
  have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K11.w32 (by decide) (by decide)).trans w10_6c
  have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K11.w32 (by decide) (by decide)).trans w10_70
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K11.w32 (by decide) (by decide)).trans w10_74
  clear w10_74 w10_70 w10_6c w10_68 w10_64 g10_12 g10_11 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0x18FE
  obtain ⟨n12, c12, u12⟩ := s11.block svRl18fe E11.self svRl18fe_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0x190E (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svRl18fe (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans c12
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by
    rw [rb12, runBlock_reg _ _ _ sp s11.zero (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb12, runBlock_reg _ _ _ (3 : Fin 32) s11.zero (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb12, runBlock_reg _ _ _ (4 : Fin 32) s11.zero (by decide), g11_4]
  have g12_18 : reg n12 (18 : Fin 32) = out := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by
    rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by
    rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by
    rw [rb12, runBlock_reg _ _ _ (22 : Fin 32) s11.zero (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by
    rw [rb12, runBlock_reg _ _ _ (23 : Fin 32) s11.zero (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = x24 := by
    rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by
    rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = x27 := by
    rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
  have g12_10 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svRl18fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g12_11 : reg n12 a1 = BitVec.ofNat 32 (img% svRekorMid1Address) := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svRl18fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g12_12 : reg n12 a2 = BitVec.ofNat 32 0x1B := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svRl18fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g12_20 : reg n12 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svRl18fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m12]; exact w11_64
  have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m12]; exact w11_68
  have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m12]; exact w11_6c
  have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m12]; exact w11_70
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m12]; exact w11_74
  clear w11_74 w11_70 w11_6c w11_68 w11_64 g11_2 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_4 g11_3 V11 E11 fR11 t11 fr11 K11 rk11 sp11 s11 c11
  have H12 : HasherAt n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32))) := by rw [m12]; exact H11
  -- 0x190E: sv_updF
  obtain ⟨n13, c13, s13, sp13, rk13, K13, H13, fr13⟩ := sv_updF (hc := 0x420) (nl := 0x1B) (msg := [] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)))
    F E12 (S2.sv FW RS fR12) RS s12 sv_at_190e sv_at_1912 (by decide) (by decide) g12_2
    g12_10 g12_11 g12_12 (by decide) (by decide) (Or.inr ⟨by decide, by decide⟩) H12 (by decide)
    (by have := b64_len_le (memBytes M0 (x20) (32)); rw [memBytes_length] at this; simp only [List.length_append, List.length_nil, memBytes_length]; omega)
  have t13 : Steps n0 n13 := t12.trans c13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keepL K13 (by decide)
  rw [sv_mbRo2 RS fR12 (Or.inr ⟨by decide, by decide⟩)] at H13
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk13 (3 : Fin 32) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk13 (4 : Fin 32) (by decide), g12_4]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rk13 (18 : Fin 32) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rk13 (19 : Fin 32) (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by rw [rk13 (20 : Fin 32) (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [rk13 (21 : Fin 32) (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [rk13 (22 : Fin 32) (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [rk13 (23 : Fin 32) (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [rk13 (24 : Fin 32) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [rk13 (25 : Fin 32) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [rk13 (26 : Fin 32) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = x27 := by rw [rk13 (27 : Fin 32) (by decide), g12_27]
  have g13_2 : reg n13 sp = B + 0x21A0 := sp13
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := keep_kk12.trans K13
  clear keep_kk12
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K13.w32 (by decide) (by decide)).trans w12_64
  have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K13.w32 (by decide) (by decide)).trans w12_68
  have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K13.w32 (by decide) (by decide)).trans w12_6c
  have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K13.w32 (by decide) (by decide)).trans w12_70
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K13.w32 (by decide) (by decide)).trans w12_74
  clear w12_74 w12_70 w12_6c w12_68 w12_64 g12_20 g12_12 g12_11 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_19 g12_18 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0x1916
  obtain ⟨n14, c14, u14⟩ := s13.block svRl1916 E13.self svRl1916_end
    ⟨trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem SV n14 0x191A (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock svRl1916 (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
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
  have g14_18 : reg n14 (18 : Fin 32) = out := by
    rw [rb14, runBlock_reg _ _ _ (18 : Fin 32) s13.zero (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by
    rw [rb14, runBlock_reg _ _ _ (19 : Fin 32) s13.zero (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by
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
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by
    rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = x27 := by
    rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
  have g14_12 : reg n14 a2 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svRl1916, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m14]; exact w13_64
  have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m14]; exact w13_68
  have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m14]; exact w13_6c
  have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m14]; exact w13_70
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m14]; exact w13_74
  clear w13_74 w13_70 w13_6c w13_68 w13_64 g13_2 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_4 g13_3 V13 E13 fR13 t13 fr13 K13 rk13 sp13 s13 c13
  have H14 : HasherAt n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B)) := by rw [m14]; exact H13
  -- 0x191A: lw
  obtain ⟨n15, d15, u15⟩ := s14.lw E14.self sv_at_191a (off' := 0x191C) (by decide)
    (by rw [g14_2, show B + 0x21A0 + 0x70 = B + 0x21A0 + BitVec.ofNat 32 0x70 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s15 : St n15.mem SV n15 0x191C (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
  have g15_12 : reg n15 a2 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_12]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, upd_ne (by decide) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by rw [u15.regs, upd_ne (by decide) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_27]
  have g15_10 : reg n15 a0 = w70 := by
    rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g14_2, show B + 0x21A0 + 0x70 = B + 0x21A0 + BitVec.ofNat 32 0x70 by sv_addr, w14_70]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m15]; exact w14_64
  have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m15]; exact w14_68
  have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m15]; exact w14_6c
  have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m15]; exact w14_70
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m15]; exact w14_74
  clear w14_74 w14_70 w14_6c w14_68 w14_64 g14_12 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  have H15 : HasherAt n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B)) := by rw [m15]; exact H14
  -- 0x191C: lw
  obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_191c (off' := 0x191E) (by decide)
    (by rw [g15_2, show B + 0x21A0 + 0x68 = B + 0x21A0 + BitVec.ofNat 32 0x68 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s16 : St n16.mem SV n16 0x191E (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
  have g16_10 : reg n16 a0 = w70 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_10]
  have g16_12 : reg n16 a2 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_12]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by rw [u16.regs, upd_ne (by decide) (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = x24 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = x27 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_27]
  have g16_11 : reg n16 a1 = w68 := by
    rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g15_2, show B + 0x21A0 + 0x68 = B + 0x21A0 + BitVec.ofNat 32 0x68 by sv_addr, w15_68]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m16]; exact w15_64
  have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m16]; exact w15_68
  have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m16]; exact w15_6c
  have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m16]; exact w15_70
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m16]; exact w15_74
  clear w15_74 w15_70 w15_6c w15_68 w15_64 g15_10 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_12 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
  have H16 : HasherAt n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B)) := by rw [m16]; exact H15
  -- 0x191E: sv_b64eF
  obtain ⟨n17, c17, s17, sp17, rk17, K17, H17, fr17⟩ := sv_b64eF (hc := 0x420) (nl := (w68).toNat) (msg := [] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B))
    F E16 (S2.sv FW RS fR16) (RK0.sv FW fR16) RS s16 sv_at_191e sv_at_1922 (by decide) (by decide) g16_2
    g16_10 (by rw [g16_11, ofNat_toNat_self]) g16_12 (by decide) (by decide) (.inl sig_in) H16
    (by have := b64_len_le (memBytes M0 (x20) (32)); rw [memBytes_length] at this; have := sig_in.lo; simp only [List.length_append, List.length_nil, memBytes_length]; omega)
  have t17 : Steps n0 n17 := t16.trans c17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keepL K17 (by decide)
  rw [sv_mbRo2 RS fR16 (.inl sig_in)] at H17
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk17 (3 : Fin 32) (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk17 (4 : Fin 32) (by decide), g16_4]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [rk17 (18 : Fin 32) (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [rk17 (19 : Fin 32) (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by rw [rk17 (20 : Fin 32) (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [rk17 (21 : Fin 32) (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [rk17 (22 : Fin 32) (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [rk17 (23 : Fin 32) (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = x24 := by rw [rk17 (24 : Fin 32) (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [rk17 (25 : Fin 32) (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [rk17 (26 : Fin 32) (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = x27 := by rw [rk17 (27 : Fin 32) (by decide), g16_27]
  have g17_2 : reg n17 sp = B + 0x21A0 := sp17
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := keep_kk16.trans K17
  clear keep_kk16
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K17.w32 (by decide) (by decide)).trans w16_64
  have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K17.w32 (by decide) (by decide)).trans w16_68
  have w17_6c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K17.w32 (by decide) (by decide)).trans w16_6c
  have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K17.w32 (by decide) (by decide)).trans w16_70
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K17.w32 (by decide) (by decide)).trans w16_74
  clear w16_74 w16_70 w16_6c w16_68 w16_64 g16_11 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_12 g16_10 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  -- 0x1926
  obtain ⟨n18, c18, u18⟩ := s17.block svRl1926 E17.self svRl1926_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have s18 : St n18.mem SV n18 0x1936 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have rb18 : ∀ q, reg n18 q = (runBlock svRl1926 (n17.mem, reg n17)).2 q := fun q => by rw [u18.regs]
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans c18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by
    rw [rb18, runBlock_reg _ _ _ sp s17.zero (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb18, runBlock_reg _ _ _ (3 : Fin 32) s17.zero (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb18, runBlock_reg _ _ _ (4 : Fin 32) s17.zero (by decide), g17_4]
  have g18_18 : reg n18 (18 : Fin 32) = out := by
    rw [rb18, runBlock_reg _ _ _ (18 : Fin 32) s17.zero (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by
    rw [rb18, runBlock_reg _ _ _ (19 : Fin 32) s17.zero (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by
    rw [rb18, runBlock_reg _ _ _ (20 : Fin 32) s17.zero (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by
    rw [rb18, runBlock_reg _ _ _ (21 : Fin 32) s17.zero (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by
    rw [rb18, runBlock_reg _ _ _ (22 : Fin 32) s17.zero (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by
    rw [rb18, runBlock_reg _ _ _ (23 : Fin 32) s17.zero (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = x24 := by
    rw [rb18, runBlock_reg _ _ _ (24 : Fin 32) s17.zero (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by
    rw [rb18, runBlock_reg _ _ _ (25 : Fin 32) s17.zero (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by
    rw [rb18, runBlock_reg _ _ _ (26 : Fin 32) s17.zero (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = x27 := by
    rw [rb18, runBlock_reg _ _ _ (27 : Fin 32) s17.zero (by decide), g17_27]
  have g18_10 : reg n18 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svRl1926, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g18_11 : reg n18 a1 = BitVec.ofNat 32 (img% svRekorMid2Address) := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svRl1926, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g18_12 : reg n18 a2 = BitVec.ofNat 32 0x54 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svRl1926, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m18]; exact w17_64
  have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m18]; exact w17_68
  have w18_6c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m18]; exact w17_6c
  have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m18]; exact w17_70
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m18]; exact w17_74
  clear w17_74 w17_70 w17_6c w17_68 w17_64 g17_2 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_4 g17_3 V17 E17 fR17 t17 fr17 K17 rk17 sp17 s17 c17
  have H18 : HasherAt n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes M0 (w70) ((w68).toNat))) := by rw [m18]; exact H17
  -- 0x1936: sv_updF
  obtain ⟨n19, c19, s19, sp19, rk19, K19, H19, fr19⟩ := sv_updF (hc := 0x420) (nl := 0x54) (msg := [] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes M0 (w70) ((w68).toNat)))
    F E18 (S2.sv FW RS fR18) RS s18 sv_at_1936 sv_at_193a (by decide) (by decide) g18_2
    g18_10 g18_11 g18_12 (by decide) (by decide) (Or.inr ⟨by decide, by decide⟩) H18 (by decide)
    (by have := b64_len_le (memBytes M0 (x20) (32)); rw [memBytes_length] at this; have := b64_len_le (memBytes M0 (w70) ((w68).toNat)); rw [memBytes_length] at this; have := sig_in.lo; simp only [List.length_append, List.length_nil, memBytes_length]; omega)
  have t19 : Steps n0 n19 := t18.trans c19
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.keepL K19 (by decide)
  rw [sv_mbRo2 RS fR18 (Or.inr ⟨by decide, by decide⟩)] at H19
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk19 (3 : Fin 32) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk19 (4 : Fin 32) (by decide), g18_4]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [rk19 (18 : Fin 32) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [rk19 (19 : Fin 32) (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by rw [rk19 (20 : Fin 32) (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [rk19 (21 : Fin 32) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [rk19 (22 : Fin 32) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [rk19 (23 : Fin 32) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = x24 := by rw [rk19 (24 : Fin 32) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [rk19 (25 : Fin 32) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [rk19 (26 : Fin 32) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [rk19 (27 : Fin 32) (by decide), g18_27]
  have g19_2 : reg n19 sp = B + 0x21A0 := sp19
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := keep_kk18.trans K19
  clear keep_kk18
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K19.w32 (by decide) (by decide)).trans w18_64
  have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K19.w32 (by decide) (by decide)).trans w18_68
  have w19_6c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K19.w32 (by decide) (by decide)).trans w18_6c
  have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K19.w32 (by decide) (by decide)).trans w18_70
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K19.w32 (by decide) (by decide)).trans w18_74
  clear w18_74 w18_70 w18_6c w18_68 w18_64 g18_12 g18_11 g18_10 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
  -- 0x193E
  obtain ⟨n20, c20, u20⟩ := s19.block svRl193e E19.self svRl193e_end
    ⟨trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0x1942 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svRl193e (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_18 : reg n20 (18 : Fin 32) = out := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by
    rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by
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
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = x27 := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_12 : reg n20 a2 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svRl193e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m20]; exact w19_64
  have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m20]; exact w19_68
  have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m20]; exact w19_6c
  have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m20]; exact w19_70
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m20]; exact w19_74
  clear w19_74 w19_70 w19_6c w19_68 w19_64 g19_2 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_4 g19_3 V19 E19 fR19 t19 fr19 K19 rk19 sp19 s19 c19
  have H20 : HasherAt n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes M0 (w70) ((w68).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid2Address)) (0x54)) := by rw [m20]; exact H19
  -- 0x1942: lw
  obtain ⟨n21, d21, u21⟩ := s20.lw E20.self sv_at_1942 (off' := 0x1944) (by decide)
    (by rw [g20_2, show B + 0x21A0 + 0x6C = B + 0x21A0 + BitVec.ofNat 32 0x6C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s21 : St n21.mem SV n21 0x1944 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
  have g21_12 : reg n21 a2 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_12]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by rw [u21.regs, upd_ne (by decide) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = x24 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
  have g21_10 : reg n21 a0 = w6c := by
    rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g20_2, show B + 0x21A0 + 0x6C = B + 0x21A0 + BitVec.ofNat 32 0x6C by sv_addr, w20_6c]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m21]; exact w20_64
  have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m21]; exact w20_68
  have w21_6c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m21]; exact w20_6c
  have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m21]; exact w20_70
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m21]; exact w20_74
  clear w20_74 w20_70 w20_6c w20_68 w20_64 g20_12 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  have H21 : HasherAt n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes M0 (w70) ((w68).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid2Address)) (0x54)) := by rw [m21]; exact H20
  -- 0x1944
  obtain ⟨n22, c22, u22⟩ := s21.block svRl1944 E21.self svRl1944_end
    ⟨trivial, trivial⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have s22 : St n22.mem SV n22 0x1946 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have rb22 : ∀ q, reg n22 q = (runBlock svRl1944 (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
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
  have g22_10 : reg n22 a0 = w6c := by
    rw [rb22, runBlock_reg _ _ _ a0 s21.zero (by decide), g21_10]
  have g22_12 : reg n22 a2 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb22, runBlock_reg _ _ _ a2 s21.zero (by decide), g21_12]
  have g22_18 : reg n22 (18 : Fin 32) = out := by
    rw [rb22, runBlock_reg _ _ _ (18 : Fin 32) s21.zero (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by
    rw [rb22, runBlock_reg _ _ _ (19 : Fin 32) s21.zero (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by
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
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by
    rw [rb22, runBlock_reg _ _ _ (26 : Fin 32) s21.zero (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = x27 := by
    rw [rb22, runBlock_reg _ _ _ (27 : Fin 32) s21.zero (by decide), g21_27]
  have g22_11 : reg n22 a1 = x22 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, svRl1944, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_10, g21_12, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m22]; exact w21_64
  have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m22]; exact w21_68
  have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m22]; exact w21_6c
  have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m22]; exact w21_70
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m22]; exact w21_74
  clear w21_74 w21_70 w21_6c w21_68 w21_64 g21_10 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_12 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
  have H22 : HasherAt n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes M0 (w70) ((w68).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid2Address)) (0x54)) := by rw [m22]; exact H21
  -- 0x1946: sv_b64eF
  obtain ⟨n23, c23, s23, sp23, rk23, K23, H23, fr23⟩ := sv_b64eF (hc := 0x420) (nl := (x22).toNat) (msg := [] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes M0 (w70) ((w68).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid2Address)) (0x54))
    F E22 (S2.sv FW RS fR22) (RK0.sv FW fR22) RS s22 sv_at_1946 sv_at_194a (by decide) (by decide) g22_2
    g22_10 (by rw [g22_11, ofNat_toNat_self]) g22_12 (by decide) (by decide) (.inl crt_in) H22
    (by have := b64_len_le (memBytes M0 (x20) (32)); rw [memBytes_length] at this; have := b64_len_le (memBytes M0 (w70) ((w68).toNat)); rw [memBytes_length] at this; have := sig_in.lo; have := crt_in.lo; simp only [List.length_append, List.length_nil, memBytes_length]; omega)
  have t23 : Steps n0 n23 := t22.trans c23
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.keepL K23 (by decide)
  rw [sv_mbRo2 RS fR22 (.inl crt_in)] at H23
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk23 (3 : Fin 32) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk23 (4 : Fin 32) (by decide), g22_4]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [rk23 (18 : Fin 32) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [rk23 (19 : Fin 32) (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by rw [rk23 (20 : Fin 32) (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [rk23 (21 : Fin 32) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [rk23 (22 : Fin 32) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [rk23 (23 : Fin 32) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = x24 := by rw [rk23 (24 : Fin 32) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [rk23 (25 : Fin 32) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [rk23 (26 : Fin 32) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = x27 := by rw [rk23 (27 : Fin 32) (by decide), g22_27]
  have g23_2 : reg n23 sp = B + 0x21A0 := sp23
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := keep_kk22.trans K23
  clear keep_kk22
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K23.w32 (by decide) (by decide)).trans w22_64
  have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K23.w32 (by decide) (by decide)).trans w22_68
  have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K23.w32 (by decide) (by decide)).trans w22_6c
  have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K23.w32 (by decide) (by decide)).trans w22_70
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K23.w32 (by decide) (by decide)).trans w22_74
  clear w22_74 w22_70 w22_6c w22_68 w22_64 g22_11 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_12 g22_10 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22
  -- 0x194E
  obtain ⟨n24, c24, u24⟩ := s23.block svRl194e E23.self svRl194e_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem SV n24 0x195C (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock svRl194e (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
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
  have g24_18 : reg n24 (18 : Fin 32) = out := by
    rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by
    rw [rb24, runBlock_reg _ _ _ (19 : Fin 32) s23.zero (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by
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
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by
    rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = x27 := by
    rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
  have g24_10 : reg n24 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svRl194e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g24_11 : reg n24 a1 = BitVec.ofNat 32 (img% svRekorPostAddress) := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svRl194e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g24_12 : reg n24 a2 = BitVec.ofNat 32 0x7 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svRl194e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m24]; exact w23_64
  have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m24]; exact w23_68
  have w24_6c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m24]; exact w23_6c
  have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m24]; exact w23_70
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m24]; exact w23_74
  clear w23_74 w23_70 w23_6c w23_68 w23_64 g23_2 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_4 g23_3 V23 E23 fR23 t23 fr23 K23 rk23 sp23 s23 c23
  have H24 : HasherAt n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes M0 (w70) ((w68).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid2Address)) (0x54) ++ base64Encode (memBytes M0 (w6c) ((x22).toNat))) := by rw [m24]; exact H23
  -- 0x195C: sv_updF
  obtain ⟨n25, c25, s25, sp25, rk25, K25, H25, fr25⟩ := sv_updF (hc := 0x420) (nl := 0x7) (msg := [] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes M0 (w70) ((w68).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid2Address)) (0x54) ++ base64Encode (memBytes M0 (w6c) ((x22).toNat)))
    F E24 (S2.sv FW RS fR24) RS s24 sv_at_195c sv_at_1960 (by decide) (by decide) g24_2
    g24_10 g24_11 g24_12 (by decide) (by decide) (Or.inr ⟨by decide, by decide⟩) H24 (by decide)
    (by have := b64_len_le (memBytes M0 (x20) (32)); rw [memBytes_length] at this; have := b64_len_le (memBytes M0 (w70) ((w68).toNat)); rw [memBytes_length] at this; have := b64_len_le (memBytes M0 (w6c) ((x22).toNat)); rw [memBytes_length] at this; have := sig_in.lo; have := crt_in.lo; simp only [List.length_append, List.length_nil, memBytes_length]; omega)
  have t25 : Steps n0 n25 := t24.trans c25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keepL K25 (by decide)
  rw [sv_mbRo2 RS fR24 (Or.inr ⟨by decide, by decide⟩)] at H25
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk25 (3 : Fin 32) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk25 (4 : Fin 32) (by decide), g24_4]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rk25 (18 : Fin 32) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rk25 (19 : Fin 32) (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by rw [rk25 (20 : Fin 32) (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by rw [rk25 (21 : Fin 32) (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = x22 := by rw [rk25 (22 : Fin 32) (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = x23 := by rw [rk25 (23 : Fin 32) (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = x24 := by rw [rk25 (24 : Fin 32) (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by rw [rk25 (25 : Fin 32) (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by rw [rk25 (26 : Fin 32) (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = x27 := by rw [rk25 (27 : Fin 32) (by decide), g24_27]
  have g25_2 : reg n25 sp = B + 0x21A0 := sp25
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := keep_kk24.trans K25
  clear keep_kk24
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K25.w32 (by decide) (by decide)).trans w24_64
  have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K25.w32 (by decide) (by decide)).trans w24_68
  have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K25.w32 (by decide) (by decide)).trans w24_6c
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K25.w32 (by decide) (by decide)).trans w24_70
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K25.w32 (by decide) (by decide)).trans w24_74
  clear w24_74 w24_70 w24_6c w24_68 w24_64 g24_12 g24_11 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  -- 0x1964
  obtain ⟨n26, c26, u26⟩ := s25.block svRl1964 E25.self svRl1964_end
    ⟨trivial, trivial, trivial⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have s26 : St n26.mem SV n26 0x196C (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have rb26 : ∀ q, reg n26 q = (runBlock svRl1964 (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans c26
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by
    rw [rb26, runBlock_reg _ _ _ sp s25.zero (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb26, runBlock_reg _ _ _ (3 : Fin 32) s25.zero (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb26, runBlock_reg _ _ _ (4 : Fin 32) s25.zero (by decide), g25_4]
  have g26_18 : reg n26 (18 : Fin 32) = out := by
    rw [rb26, runBlock_reg _ _ _ (18 : Fin 32) s25.zero (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by
    rw [rb26, runBlock_reg _ _ _ (19 : Fin 32) s25.zero (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by
    rw [rb26, runBlock_reg _ _ _ (20 : Fin 32) s25.zero (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by
    rw [rb26, runBlock_reg _ _ _ (21 : Fin 32) s25.zero (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by
    rw [rb26, runBlock_reg _ _ _ (22 : Fin 32) s25.zero (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = x23 := by
    rw [rb26, runBlock_reg _ _ _ (23 : Fin 32) s25.zero (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = x24 := by
    rw [rb26, runBlock_reg _ _ _ (24 : Fin 32) s25.zero (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by
    rw [rb26, runBlock_reg _ _ _ (25 : Fin 32) s25.zero (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by
    rw [rb26, runBlock_reg _ _ _ (26 : Fin 32) s25.zero (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = x27 := by
    rw [rb26, runBlock_reg _ _ _ (27 : Fin 32) s25.zero (by decide), g25_27]
  have g26_10 : reg n26 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, svRl1964, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g26_11 : reg n26 a1 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, svRl1964, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m26]; exact w25_64
  have w26_68 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m26]; exact w25_68
  have w26_6c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m26]; exact w25_6c
  have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m26]; exact w25_70
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m26]; exact w25_74
  clear w25_74 w25_70 w25_6c w25_68 w25_64 g25_2 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_4 g25_3 V25 E25 fR25 t25 fr25 K25 rk25 sp25 s25 c25
  have H26 : HasherAt n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes M0 (w70) ((w68).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid2Address)) (0x54) ++ base64Encode (memBytes M0 (w6c) ((x22).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPostAddress)) (0x7)) := by rw [m26]; exact H25
  -- 0x196C: sv_finF
  obtain ⟨n27, c27, s27, sp27, rk27, K27, D27, fr27⟩ := sv_finF (hc := 0x420) (oc := 0x400) (msg := [] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (x20) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes M0 (w70) ((w68).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid2Address)) (0x54) ++ base64Encode (memBytes M0 (w6c) ((x22).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPostAddress)) (0x7))
    F E26 (S2.sv FW RS fR26) (RK0.sv FW fR26) RS s26 sv_at_196c sv_at_1970 (by decide) (by decide) g26_2
    g26_10 g26_11 (by decide) (by decide) H26
  have t27 : Steps n0 n27 := t26.trans c27
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.keepL K27 (by decide)
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk27 (3 : Fin 32) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk27 (4 : Fin 32) (by decide), g26_4]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [rk27 (18 : Fin 32) (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [rk27 (19 : Fin 32) (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = BitVec.ofNat 32 0x1B := by rw [rk27 (20 : Fin 32) (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [rk27 (21 : Fin 32) (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [rk27 (22 : Fin 32) (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [rk27 (23 : Fin 32) (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = x24 := by rw [rk27 (24 : Fin 32) (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [rk27 (25 : Fin 32) (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [rk27 (26 : Fin 32) (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = x27 := by rw [rk27 (27 : Fin 32) (by decide), g26_27]
  have g27_2 : reg n27 sp = B + 0x21A0 := sp27
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x400, 0x20)] := keep_kk26.trans K27
  clear keep_kk26
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K27.w32 (by decide) (by decide)).trans w26_64
  have w27_68 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K27.w32 (by decide) (by decide)).trans w26_68
  have w27_6c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K27.w32 (by decide) (by decide)).trans w26_6c
  have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K27.w32 (by decide) (by decide)).trans w26_70
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K27.w32 (by decide) (by decide)).trans w26_74
  clear w26_74 w26_70 w26_6c w26_68 w26_64 g26_11 g26_10 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
  exact .inr ⟨n27, t27, s27, E27, V27, fR27, g27_2, g27_3, g27_4, g27_18, g27_19, g27_20, g27_21, g27_22, g27_23, g27_24, g27_25, g27_26, g27_27, w27_64, w27_68, w27_6c, w27_70, w27_74, D27, keep_kk27.mono (by decide)⟩

end C3.RV32.Sv
