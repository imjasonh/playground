import C3BootProofs.Proofs.BootSpec

/-!
# `c3_bootloader::boot`: raising the security level

When the target security level is above the level in the eFuses, `boot`
programs eFuse bits in at most three attempts before it copies the image.
Each attempt reads the eFuse word at 0x6000883C, counts the level from
it, and returns when the level reaches the target. Otherwise it writes
the next bit's timing and data registers, runs `efuse_program_run`, and
checks that the bit reads back.

The model treats the eFuse controller's registers as plain memory, so a
program run never changes the word at 0x6000883C. `rs_raise` proves the
result: from the attempt loop's setup, `boot` reaches the cache setup
with memory unchanged when the eFuse level already reaches the target,
and halts otherwise.
-/

namespace C3.RV32.Cur

open C3.Image

/-- The entry of `efuse_program_run`. -/
abbrev EPR : Word := BitVec.ofNat 32 efuseProgramRunAddress

set_option maxRecDepth 20000

theorem epr_at_0 : fetchRel efuseProgramRunCode 0x0 = some (.lui a2 0x60009000, 4) := by decide
theorem epr_at_4 : fetchRel efuseProgramRunCode 0x4 = some (.store .sw a2 a0 0xFFFFF9CC, 4) := by decide
theorem epr_at_8 : fetchRel efuseProgramRunCode 0x8 = some (.store .sw a2 a1 0xFFFFF9D4, 4) := by decide
theorem epr_at_c : fetchRel efuseProgramRunCode 0xC = some (.aluImm .add a0 x0 0xFFFFFFFF, 2) := by decide
theorem epr_at_e : fetchRel efuseProgramRunCode 0xE = some (.lui a4 0xF4000, 4) := by decide
theorem epr_at_12 : fetchRel efuseProgramRunCode 0x12 = some (.aluImm .add a3 a4 0x240, 4) := by decide
theorem epr_at_16 : fetchRel efuseProgramRunCode 0x16 = some (.aluImm .add a4 a4 0x23F, 4) := by decide
theorem epr_at_1a : fetchRel efuseProgramRunCode 0x1A = some (.branch .beq a0 a4 0x10, 4) := by decide
theorem epr_at_1e : fetchRel efuseProgramRunCode 0x1E = some (.load .lw a5 a2 0xFFFFF9D4, 4) := by decide
theorem epr_at_22 : fetchRel efuseProgramRunCode 0x22 = some (.alu .and a5 a5 a1, 2) := by decide
theorem epr_at_24 : fetchRel efuseProgramRunCode 0x24 = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem epr_at_26 : fetchRel efuseProgramRunCode 0x26 = some (.branch .bne a5 x0 0xFFFFFFF4, 2) := by decide
theorem epr_at_2a : fetchRel efuseProgramRunCode 0x2A = some (.alu .add a0 x0 a3, 2) := by decide
theorem epr_at_2c : fetchRel efuseProgramRunCode 0x2C = some (.lui a1 0xF4000, 4) := by decide
theorem epr_at_30 : fetchRel efuseProgramRunCode 0x30 = some (.aluImm .add a1 a1 0x240, 4) := by decide
theorem epr_at_34 : fetchRel efuseProgramRunCode 0x34 = some (.alu .sltu a0 a0 a1, 4) := by decide
theorem epr_at_38 : fetchRel efuseProgramRunCode 0x38 = some (.jalr x0 ra 0x0, 2) := by decide

def eprBlk : List BInstr :=
  [.lui a2 0x60009000, .sw a2 a0 0xFFFFF9CC, .sw a2 a1 0xFFFFF9D4, .aluImm .add a0 x0 0xFFFFFFFF,
   .lui a4 0xF4000, .aluImm .add a3 a4 0x240, .aluImm .add a4 a4 0x23F]

theorem eprBlk_end : blockEnd efuseProgramRunCode 0x0 eprBlk = some 0x1A :=
  (blockEnd_cons' (off' := 0x4) epr_at_0 rfl (blockEnd_cons' (off' := 0x8) epr_at_4 rfl
    (blockEnd_cons' (off' := 0xC) epr_at_8 rfl (blockEnd_cons' (off' := 0xE) epr_at_c rfl
    (blockEnd_cons' (off' := 0x12) epr_at_e rfl (blockEnd_cons' (off' := 0x16) epr_at_12 rfl
    (blockEnd_cons' (off' := 0x1A) epr_at_16 rfl rfl)))))))

def eprRet : List BInstr := [.lui a1 0xF4000, .aluImm .add a1 a1 0x240, .alu .sltu a0 a0 a1]

theorem eprRet_end : blockEnd efuseProgramRunCode 0x2C eprRet = some 0x38 :=
  (blockEnd_cons' (off' := 0x30) epr_at_2c rfl (blockEnd_cons' (off' := 0x34) epr_at_30 rfl
    (blockEnd_cons' (off' := 0x38) epr_at_34 rfl rfl)))

theorem epr_ne (k : Nat) (hk : k < 0xF4240) :
    (BitVec.ofNat 32 k + 0xFFFFFFFF == (0xF423F : Word)) = false := by
  rw [beq_eq_false_iff_ne]; intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 0xFFFFFFFF from rfl,
    show (0xF423F : Word).toNat = 0xF423F from rfl] at this
  omega

theorem epr_inc (k : Nat) :
    BitVec.ofNat 32 k + 0xFFFFFFFF + 1 = BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (0xFFFFFFFF : Word).toNat = 0xFFFFFFFF from rfl, show (1 : Word).toNat = 1 from rfl]
  omega

/-- `efuse_program_run`'s poll loop runs to its timeout when the status
word it polls keeps a bit of the mask. -/
theorem epr_poll {M : Word → BitVec 8} (hc : CodeIn M EPR efuseProgramRunCode) {v : Word}
    (hv : (memLoad32 M 0x600089D4 &&& v == 0) = false) :
    ∀ d k {n : Machine}, k + d = 0xF4240 → St M EPR n 0x1A (reg n) →
      reg n a0 = BitVec.ofNat 32 k + 0xFFFFFFFF → reg n a4 = 0xF423F → reg n a3 = 0xF4240 →
      reg n a1 = v → reg n a2 = 0x60009000 →
      ∃ n', Steps n n' ∧ St M EPR n' 0x2C (reg n') ∧ reg n' a0 = 0xF4240 ∧
        ∀ r, r ≠ a0 → r ≠ a5 → reg n' r = reg n r
  | 0, k, n, hk, s, h0, h4, h3, _, _ => by
    obtain ⟨n1, d1, u1⟩ := s.taken hc 0x2A epr_at_1a (by decide) (by
      show (reg n a0 == reg n a4) = true; rw [h0, h4, show k = 0xF4240 by omega]; decide)
    obtain ⟨n2, d2, u2⟩ := u1.alu hc epr_at_2a (off' := 0x2C) (by decide)
    refine ⟨n2, .cons d1 (.single d2), ⟨u2.pc, u2.mem, fun _ => rfl⟩, ?_, fun r h1 _ => ?_⟩
    · rw [u2.regs]; simp +decide only [upd, ↓reduceIte]; rw [s.zero, h3]; rfl
    · rw [u2.regs, updz s.zero h1]
  | d + 1, k, n, hk, s, h0, h4, h3, h1, h2 => by
    obtain ⟨n1, d1, u1⟩ := s.notTaken hc 0x1E epr_at_1a (by decide) (by
      show (reg n a0 == reg n a4) = false; rw [h0, h4]; exact epr_ne k (by omega))
    obtain ⟨n2, d2, u2⟩ := u1.lw hc epr_at_1e (off' := 0x22) (by decide) (by rw [h2]; decide)
    obtain ⟨n3, d3, u3⟩ := u2.alu hc epr_at_22 (off' := 0x24) (by decide)
    obtain ⟨n4, d4, u4⟩ := u3.aluImm hc epr_at_24 (off' := 0x26) (by decide)
    obtain ⟨n5, d5, u5⟩ := u4.taken hc 0x1A epr_at_26 (by decide) (by
      show (!(_ == _)) = true
      simp +decide only [upd, ↓reduceIte]
      rw [h1, h2]; show (!(memLoad32 M 0x600089D4 &&& v == 0)) = true; rw [hv]; rfl)
    have q5 : ∀ r, r ≠ a0 → r ≠ a5 → reg n5 r = reg n r := fun r ha hb => by
      rw [u5.regs, updz (by simp [upd]) ha, updz (by simp [upd]) hb, updz s.zero hb]
    obtain ⟨n6, c6, t6, v6, k6⟩ := epr_poll hc hv d (k + 1) (n := n5) (by omega)
      ⟨u5.pc, u5.mem, fun _ => rfl⟩
      (by rw [u5.regs]; simp +decide only [upd, ↓reduceIte]; rw [h0]; exact epr_inc k)
      (by rw [q5 _ (by decide) (by decide), h4]) (by rw [q5 _ (by decide) (by decide), h3])
      (by rw [q5 _ (by decide) (by decide), h1]) (by rw [q5 _ (by decide) (by decide), h2])
    exact ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 c6)))), t6, v6,
      fun r ha hb => by rw [k6 r ha hb, q5 r ha hb]⟩

/-- `efuse_program_run(cmd, mask)` with a nonzero `mask`: it writes `cmd`
to 0x600089CC and `mask` to 0x600089D4, polls until the timeout (the
model's status word keeps the mask), and returns 0. -/
theorem epr_correct {M : Word → BitVec 8} {m : Machine} (hc : CodeIn M EPR efuseProgramRunCode)
    (s : St M EPR m 0 (reg m)) (hmask : (reg m a1 == 0) = false) :
    ∃ m', Steps m m' ∧ m'.pc = reg m ra &&& ~~~1 ∧
      m'.mem = memStore32 (memStore32 M 0x600089CC (reg m a0)) 0x600089D4 (reg m a1) ∧
      reg m' a0 = 0 ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r := by
  have sep : ∀ a : Word, EPR.toNat + 0x3A ≤ a.toNat → a.toNat + 4 ≤ 2 ^ 32 →
      Sep a 4 EPR efuseProgramRunCode.length := fun a h1 h2 =>
    (sep_of_le (by rw [show efuseProgramRunCode.length = 0x3A from rfl]; exact h1) h2).symm
  obtain ⟨n1, c1, u1⟩ := s.block eprBlk hc eprBlk_end
    (by
      simp only [BlockOk, BInstr.ok, BInstr.run, eprBlk]
      simp +decide only [upd, ↓reduceIte, true_and, and_true]
      repeat' constructor
      all_goals first | decide | exact sep _ (by decide) (by decide))
  have hz := s.zero
  have e1 : (runBlock eprBlk (M, reg m)).1 =
      memStore32 (memStore32 M 0x600089CC (reg m a0)) 0x600089D4 (reg m a1) := by
    simp +decide only [runBlock, BInstr.run, eprBlk, upd, ↓reduceIte]; rfl
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 M 0x600089CC (reg m a0)) 0x600089D4 (reg m a1) = M1 :=
    ⟨_, rfl⟩
  rw [e1, hM1] at u1
  have hc1 : CodeIn M1 EPR efuseProgramRunCode := by
    rw [← hM1]; exact (hc.store32 (sep _ (by decide) (by decide))).store32 (sep _ (by decide) (by decide))
  have hld : memLoad32 M1 0x600089D4 = reg m a1 := by rw [← hM1]; exact memLoad32_store32_same _ _ _
  have r1 : ∀ r, reg n1 r = (runBlock eprBlk (M, reg m)).2 r := fun r => by rw [u1.regs]
  have q1 : ∀ r, r ≠ a0 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n1 r = reg m r := fun r h0 h2 h3 h4 => by
    rw [r1, runBlock_reg _ _ _ r hz (by simp only [eprBlk]; revert h0 h2 h3 h4; revert r; decide)]
  obtain ⟨n2, c2, t2, v2, k2⟩ := epr_poll hc1 (v := reg m a1)
    (by rw [hld, BitVec.and_self]; exact hmask) 0xF4240 0 (n := n1) rfl ⟨u1.pc, u1.mem, fun _ => rfl⟩
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, eprBlk, upd, ↓reduceIte])
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, eprBlk, upd, ↓reduceIte])
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, eprBlk, upd, ↓reduceIte])
    (q1 _ (by decide) (by decide) (by decide) (by decide))
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, eprBlk, upd, ↓reduceIte])
  have t2' : St M1 EPR n2 0x2C (reg n2) := t2
  obtain ⟨n3, c3, u3⟩ := t2'.block eprRet hc1 eprRet_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ r, reg n3 r = (runBlock eprRet (M1, reg n2)).2 r := fun r => by rw [u3.regs]
  have hz2 := t2'.zero
  obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hc1 epr_at_38
  have k2' : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n4 r = reg m r :=
    fun r h0 h1 h2 h3 h4 h5 => by
      rw [regs4, runBlock_reg _ _ _ r hz2 (by simp only [eprRet]; revert h0 h1; revert r; decide),
        k2 r h0 h5, q1 r h0 h2 h3 h4]
  refine ⟨n4, c1.trans (c2.trans (c3.trans (.single d4))), ?_, by rw [mem4]; exact hM1.symm, ?_, k2'⟩
  · rw [pc4, runBlock_reg _ _ _ ra hz2 (by decide), add_lit_zero, k2 ra (by decide) (by decide),
      q1 ra (by decide) (by decide) (by decide) (by decide)]
  · rw [regs4]; simp +decide only [runBlock, BInstr.run, eprRet, upd, ↓reduceIte]; rw [v2]; rfl

def rsInit : List BInstr :=
  [.aluImm .add 8 x0 0x0, .lui a0 0x5000, .lui a1 0x3000, .aluImm .add 24 a0 0x555,
   .aluImm .add 25 a1 0x333, .lui 27 0x20000, .aluImm .add 27 27 0xFFFFFE00, .lui 18 0xFF000000,
   .aluImm .add 18 18 0xFF, .aluImm .add 19 9 0xFFFFF800, .lui a0 0x6000, .aluImm .add 23 a0 0xFFFFFA5A,
   .aluImm .add 21 a0 0xFFFFFAA5]

theorem rsInit_end : blockEnd bootFnCode 0x3E rsInit = some 0x6A :=
  (blockEnd_cons' (off' := 0x40) bt_at_3e rfl (blockEnd_cons' (off' := 0x42) bt_at_40 rfl (blockEnd_cons' (off' := 0x44) bt_at_42 rfl (blockEnd_cons' (off' := 0x48) bt_at_44 rfl (blockEnd_cons' (off' := 0x4C) bt_at_48 rfl (blockEnd_cons' (off' := 0x50) bt_at_4c rfl (blockEnd_cons' (off' := 0x54) bt_at_50 rfl (blockEnd_cons' (off' := 0x58) bt_at_54 rfl (blockEnd_cons' (off' := 0x5C) bt_at_58 rfl (blockEnd_cons' (off' := 0x60) bt_at_5c rfl (blockEnd_cons' (off' := 0x62) bt_at_60 rfl (blockEnd_cons' (off' := 0x66) bt_at_62 rfl (blockEnd_cons' (off' := 0x6A) bt_at_66 rfl rfl)))))))))))))

def rsHead : List BInstr :=
  [.lw a0 9 0xFFFFF83C, .aluImm .srl a1 a0 0xF, .aluImm .srl a0 a0 0xE, .alu .and a1 a1 24,
   .alu .sub a1 a0 a1, .aluImm .srl a2 a1 0x2, .alu .and a1 a1 25, .alu .and a2 a2 25, .alu .add a1 a1 a2,
   .aluImm .srl a2 a1 0x4, .alu .add a1 a1 a2, .aluImm .sll a2 a1 0x14, .aluImm .and a1 a1 0xF,
   .aluImm .srl a2 a2 0x1C, .alu .add a1 a1 a2]

theorem rsHead_end : blockEnd bootFnCode 0x6A rsHead = some 0x9A :=
  (blockEnd_cons' (off' := 0x6E) bt_at_6a rfl (blockEnd_cons' (off' := 0x72) bt_at_6e rfl (blockEnd_cons' (off' := 0x74) bt_at_72 rfl (blockEnd_cons' (off' := 0x78) bt_at_74 rfl (blockEnd_cons' (off' := 0x7C) bt_at_78 rfl (blockEnd_cons' (off' := 0x80) bt_at_7c rfl (blockEnd_cons' (off' := 0x84) bt_at_80 rfl (blockEnd_cons' (off' := 0x88) bt_at_84 rfl (blockEnd_cons' (off' := 0x8A) bt_at_88 rfl (blockEnd_cons' (off' := 0x8E) bt_at_8a rfl (blockEnd_cons' (off' := 0x90) bt_at_8e rfl (blockEnd_cons' (off' := 0x94) bt_at_90 rfl (blockEnd_cons' (off' := 0x96) bt_at_94 rfl (blockEnd_cons' (off' := 0x98) bt_at_96 rfl (blockEnd_cons' (off' := 0x9A) bt_at_98 rfl rfl)))))))))))))))

def rsCnt : List BInstr :=
  [.aluImm .and a1 8 0xFF, .aluImm .add a2 x0 0x2]

theorem rsCnt_end : blockEnd bootFnCode 0x9E rsCnt = some 0xA4 :=
  (blockEnd_cons' (off' := 0xA2) bt_at_9e rfl (blockEnd_cons' (off' := 0xA4) bt_at_a2 rfl rfl))

def rsBit : List BInstr :=
  [.aluImm .xor a1 a0 0xFFFFFFFF, .aluImm .add a0 a0 0x1, .alu .and 26 a0 a1, .aluImm .sll a0 26 0x10]

theorem rsBit_end : blockEnd bootFnCode 0xA8 rsBit = some 0xB6 :=
  (blockEnd_cons' (off' := 0xAC) bt_at_a8 rfl (blockEnd_cons' (off' := 0xAE) bt_at_ac rfl (blockEnd_cons' (off' := 0xB2) bt_at_ae rfl (blockEnd_cons' (off' := 0xB6) bt_at_b2 rfl rfl))))

def rsTim : List BInstr :=
  [.aluImm .add a3 9 0xFFFFF980, .lw a1 a3 0x68, .aluImm .and a1 a1 0xFFFFFF00, .aluImm .add a1 a1 0x28,
   .sw a3 a1 0x68, .lw a1 a3 0x68, .alu .or a1 a1 27, .sw a3 a1 0x68, .lw a1 a3 0x70, .alu .and a1 a1 18,
   .lui a2 0x300000, .alu .or a1 a1 a2, .sw a3 a1 0x70, .lw a1 a3 0x74, .lui a2 0xFFFF0000, .alu .and a1 a1 a2,
   .aluImm .add a1 a1 0x190, .sw a3 a1 0x74]

theorem rsTim_end : blockEnd bootFnCode 0xBA rsTim = some 0xEC :=
  (blockEnd_cons' (off' := 0xBE) bt_at_ba rfl (blockEnd_cons' (off' := 0xC0) bt_at_be rfl (blockEnd_cons' (off' := 0xC4) bt_at_c0 rfl (blockEnd_cons' (off' := 0xC8) bt_at_c4 rfl (blockEnd_cons' (off' := 0xCA) bt_at_c8 rfl (blockEnd_cons' (off' := 0xCC) bt_at_ca rfl (blockEnd_cons' (off' := 0xD0) bt_at_cc rfl (blockEnd_cons' (off' := 0xD2) bt_at_d0 rfl (blockEnd_cons' (off' := 0xD4) bt_at_d2 rfl (blockEnd_cons' (off' := 0xD8) bt_at_d4 rfl (blockEnd_cons' (off' := 0xDC) bt_at_d8 rfl (blockEnd_cons' (off' := 0xDE) bt_at_dc rfl (blockEnd_cons' (off' := 0xE0) bt_at_de rfl (blockEnd_cons' (off' := 0xE2) bt_at_e0 rfl (blockEnd_cons' (off' := 0xE4) bt_at_e2 rfl (blockEnd_cons' (off' := 0xE6) bt_at_e4 rfl (blockEnd_cons' (off' := 0xEA) bt_at_e6 rfl (blockEnd_cons' (off' := 0xEC) bt_at_ea rfl rfl))))))))))))))))))

def rsZ1 : List BInstr :=
  [.aluImm .add a1 x0 0x8, .alu .add a2 x0 19]

theorem rsZ1_end : blockEnd bootFnCode 0xEC rsZ1 = some 0xF0 :=
  (blockEnd_cons' (off' := 0xEE) bt_at_ec rfl (blockEnd_cons' (off' := 0xF0) bt_at_ee rfl rfl))

def rsZ2 : List BInstr :=
  [.aluImm .add a1 x0 0x3, .aluImm .add a2 9 0xFFFFF820]

theorem rsZ2_end : blockEnd bootFnCode 0xFC rsZ2 = some 0x102 :=
  (blockEnd_cons' (off' := 0xFE) bt_at_fc rfl (blockEnd_cons' (off' := 0x102) bt_at_fe rfl rfl))

def rsRun : List BInstr :=
  [.aluImm .srl a0 a0 0x2, .sw 9 a0 0xFFFFF810, .aluImm .add a1 x0 0x2, .alu .add a0 x0 23]

theorem rsRun_end : blockEnd bootFnCode 0x10E rsRun = some 0x118 :=
  (blockEnd_cons' (off' := 0x110) bt_at_10e rfl (blockEnd_cons' (off' := 0x114) bt_at_110 rfl (blockEnd_cons' (off' := 0x116) bt_at_114 rfl (blockEnd_cons' (off' := 0x118) bt_at_116 rfl rfl))))

def rsZ3 : List BInstr :=
  [.aluImm .add a1 x0 0x8, .alu .add a2 x0 19]

theorem rsZ3_end : blockEnd bootFnCode 0x120 rsZ3 = some 0x124 :=
  (blockEnd_cons' (off' := 0x122) bt_at_120 rfl (blockEnd_cons' (off' := 0x124) bt_at_122 rfl rfl))

def rsChk : List BInstr :=
  [.lw a0 9 0xFFFFF83C, .aluImm .srl a0 a0 0xE, .alu .and a0 26 a0, .aluImm .sll a0 a0 0x10,
   .alu .sltu a0 x0 a0, .aluImm .add 8 8 0x1, .aluImm .add a0 a0 0xFFFFFFFF, .alu .and 8 8 a0]

theorem rsChk_end : blockEnd bootFnCode 0x13E rsChk = some 0x154 :=
  (blockEnd_cons' (off' := 0x142) bt_at_13e rfl (blockEnd_cons' (off' := 0x144) bt_at_142 rfl (blockEnd_cons' (off' := 0x148) bt_at_144 rfl (blockEnd_cons' (off' := 0x14A) bt_at_148 rfl (blockEnd_cons' (off' := 0x14E) bt_at_14a rfl (blockEnd_cons' (off' := 0x150) bt_at_14e rfl (blockEnd_cons' (off' := 0x152) bt_at_150 rfl (blockEnd_cons' (off' := 0x154) bt_at_152 rfl rfl))))))))

/-- The eFuse word that `boot` counts the security level from. -/
abbrev efuseRd : Word := 0x6000883C

/-- The security level as `boot` counts it from the eFuse word `w`: the
number of set bits among bits 14 to 29, computed the way the compiled code
computes it. -/
def btPop (w : Word) : Word :=
  let a0 := aluEval .srl w 0xE
  let b1 := aluEval .sub a0 (aluEval .and (aluEval .srl w 0xF) 0x5555)
  let b2 := aluEval .add (aluEval .and b1 0x3333) (aluEval .and (aluEval .srl b1 0x2) 0x3333)
  let b3 := aluEval .add b2 (aluEval .srl b2 0x4)
  aluEval .add (aluEval .and b3 0xF) (aluEval .srl (aluEval .sll b3 0x14) 0x1C)

/-- `M` agrees with `Mb` outside the eFuse controller's registers
0x60008800 to 0x600089FF, and on the word at 0x6000883C that holds the
level. -/
def RsI (Mb M : Word → BitVec 8) : Prop :=
  ∀ x : Word, (x.toNat < 0x60008800 ∨ 0x60008A00 ≤ x.toNat ∨
    (0x6000883C ≤ x.toNat ∧ x.toNat < 0x60008840)) → M x = Mb x

theorem RsI.refl (M : Word → BitVec 8) : RsI M M := fun _ _ => rfl

theorem RsI.trans {M0 M1 M2 : Word → BitVec 8} (h1 : RsI M0 M1) (h2 : RsI M1 M2) : RsI M0 M2 :=
  fun x hx => (h2 x hx).trans (h1 x hx)

theorem RsI.store {Mb M : Word → BitVec 8} (h : RsI Mb M) {a : Word} (v : Word)
    (h1 : 0x60008800 ≤ a.toNat) (h2 : a.toNat + 4 ≤ 0x60008A00)
    (h3 : a.toNat + 4 ≤ 0x6000883C ∨ 0x60008840 ≤ a.toNat) : RsI Mb (memStore32 M a v) := fun x hx => by
  have hs : Sep a 4 x 1 := by
    rcases hx with hx | hx | ⟨hx1, hx2⟩
    · exact (sep_of_le (by omega) (by omega)).symm
    · exact sep_of_le (by omega) (by have := x.isLt; omega)
    · rcases h3 with h3 | h3
      · exact sep_of_le (by omega) (by omega)
      · exact (sep_of_le (by omega) (by omega)).symm
  rw [memStore32_get_sep hs]; exact h x hx

theorem RsI.code {Mb M : Word → BitVec 8} {b : Word} {code : List Nat} (hc : CodeIn Mb b code)
    (hl : b.toNat + code.length ≤ 0x60000000) (h : RsI Mb M) : CodeIn M b code := fun i hi => by
  rw [h _ (Or.inl (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]; exact hc i hi

theorem RsI.panic {Mb M : Word → BitVec 8} (hP : PanicCode Mb) (h : RsI Mb M) : PanicCode M := fun p hp => by
  have hm := panicFns_mid p hp
  exact RsI.code (hP p hp) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) h

theorem RsI.field {Mb M : Word → BitVec 8} (h : RsI Mb M) : memLoad32 M efuseRd = memLoad32 Mb efuseRd :=
  memLoad32_congr fun j hj => h _ (Or.inr (Or.inr (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show efuseRd.toNat = 0x6000883C from rfl]
    exact ⟨by omega, by omega⟩)))

theorem rs_sep (a : Word) (h1 : 0x60000000 ≤ a.toNat) (h2 : a.toNat + 4 ≤ 2 ^ 32) :
    Sep a 4 BT bootFnCode.length :=
  (sep_of_le (by rw [show bootFnCode.length = 0x2A8 from rfl, show BT.toNat = 0x403b699e from rfl]; omega)
    h2).symm

theorem rs_bit (a : Word) : ((a + 1) &&& (a ^^^ 0xFFFFFFFF)) &&& a = 0 := by
  rw [BitVec.and_assoc]
  have : (a ^^^ 0xFFFFFFFF) &&& a = 0 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have h1 : (0xFFFFFFFF : Word).getLsbD i = true :=
      (show ∀ i, i < 32 → (0xFFFFFFFF : Word).getLsbD i = true by decide) i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_xor, h1, show BitVec.getLsbD (0 : Word) i = false from BitVec.getLsbD_zero]
    cases a.getLsbD i <;> rfl
  rw [this]; exact BitVec.and_zero

/-- `boot`'s halt with code 0xE1, at 0x29C. -/
theorem rs_halt {n : Machine} (s : St n.mem BT n 0x29C (reg n)) (hc : CodeIn n.mem BT bootFnCode)
    (hP : PanicCode n.mem) (hR : Room (reg n sp) 16) : Panics n := by
  obtain ⟨n1, d1, u1⟩ := s.aluImm hc bt_at_29c (off' := 0x2A0) (by decide)
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1.self.callRa (cb := haltBase) hc bt_at_2a0 bt_at_2a4
    (by decide) (by decide)
  have sp2 : reg n2 sp = reg n sp := by
    rw [regs2, updz u1.self.zero (by decide), u1.regs, updz s.zero (by decide)]
  exact Panics.of_steps (.cons d1 c2) (halt_panics n2 (by rw [mem2]; exact hP) pc2 (by rw [sp2]; exact hR))

theorem rs_p4 (p : Word) (h : p.toNat + 4 < 2 ^ 32) : (p + 4).toNat = p.toNat + 4 := by
  rw [BitVec.toNat_add, show (4 : Word).toNat = 4 from rfl]; omega

/-- One of `boot`'s loops that zero `k` words of eFuse registers from `p`;
its `beq` is at `o`. -/
theorem rs_zero (o : Nat)
    (h2 : fetchRel bootFnCode (o + 2) = some (.store .sw a2 x0 0x0, 4))
    (h6 : fetchRel bootFnCode (o + 6) = some (.aluImm .add a2 a2 0x4, 2))
    (h8 : fetchRel bootFnCode (o + 8) = some (.aluImm .add a1 a1 0xFFFFFFFF, 2))
    (hA : fetchRel bootFnCode (o + 0xA) = some (.branch .bne a1 x0 0xFFFFFFF8, 2))
    (n2 : BitVec.ofNat 32 (o + 2) + 4 = BitVec.ofNat 32 (o + 6))
    (n6 : BitVec.ofNat 32 (o + 6) + 2 = BitVec.ofNat 32 (o + 8))
    (n8 : BitVec.ofNat 32 (o + 8) + 2 = BitVec.ofNat 32 (o + 0xA))
    (nT : BitVec.ofNat 32 (o + 0xA) + 0xFFFFFFF8 = BitVec.ofNat 32 (o + 2))
    (nF : BitVec.ofNat 32 (o + 0xA) + 2 = BitVec.ofNat 32 (o + 0xC)) :
    ∀ k {n : Machine} (p : Word), St n.mem BT n (o + 2) (reg n) → 0 < k → reg n a1 = BitVec.ofNat 32 k →
      reg n a2 = p → p.toNat % 4 = 0 → 0x60008800 ≤ p.toNat → p.toNat + 4 * k ≤ 0x6000883C →
      CodeIn n.mem BT bootFnCode →
      ∃ n', Steps n n' ∧ St n'.mem BT n' (o + 0xC) (reg n') ∧ RsI n.mem n'.mem ∧
        ∀ r, r ≠ a1 → r ≠ a2 → reg n' r = reg n r
  | 0, _, _, _, hk, _, _, _, _, _, _ => absurd hk (by decide)
  | k + 1, n, p, s, _, h1, hp, hal, hlo, hhi, hc => by
    have hz := s.zero
    obtain ⟨n1, d1, u1⟩ := s.sw hc h2 n2 (by rw [hp, add_lit_zero]; exact hal)
    rw [hp, add_lit_zero, show reg n x0 = 0 from hz] at u1
    have hm1 : RsI n.mem n1.mem := by
      rw [u1.mem]; exact (RsI.refl _).store _ hlo (by omega) (Or.inl (by omega))
    have hc1 : CodeIn n1.mem BT bootFnCode := by
      rw [u1.mem]; exact hc.store32 (rs_sep _ (by omega) (by omega))
    have t1 : St n1.mem BT n1 (o + 6) (reg n) := ⟨u1.pc, rfl, u1.regs⟩
    obtain ⟨n3, d3, u3⟩ := t1.aluImm hc1 h6 n6
    obtain ⟨n4, d4, u4⟩ := u3.aluImm hc1 h8 n8
    have v1 : aluEval .add (upd (reg n) a2 (aluEval .add (reg n a2) 0x4) a1) 0xFFFFFFFF = BitVec.ofNat 32 k := by
      rw [updz hz (by decide), h1]
      apply BitVec.eq_of_toNat_eq
      show (BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF).toNat = _
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show (0xFFFFFFFF : Word).toNat = 0xFFFFFFFF from rfl]
      omega
    rw [v1] at u4
    have q4 : ∀ r, r ≠ a1 → r ≠ a2 → upd (upd (reg n) a2 (aluEval .add (reg n a2) 0x4)) a1 (BitVec.ofNat 32 k) r =
        reg n r := fun r ha hb => by rw [updz (by simp [upd]) ha, updz hz hb]
    rcases Nat.eq_zero_or_pos k with hk0 | hkp
    · subst hk0
      obtain ⟨n5, d5, u5⟩ := u4.notTaken hc1 (o + 0xC) hA nF (by
        show ((_ : Word) != _) = false
        simp +decide only [upd, ↓reduceIte])
      refine ⟨n5, .cons d1 (.cons d3 (.cons d4 (.single d5))), ⟨u5.pc, rfl, fun _ => rfl⟩, ?_,
        fun r ha hb => by rw [u5.regs, q4 r ha hb]⟩
      rw [u5.mem]; exact hm1
    · obtain ⟨n5, d5, u5⟩ := u4.taken hc1 (o + 2) hA nT (by
        show ((_ : Word) != _) = true
        simp +decide only [upd, ↓reduceIte]
        exact bne_iff_ne.mpr fun h => by
          have := congrArg BitVec.toNat h
          rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this; omega)
      have a2v : upd (upd (reg n) a2 (aluEval .add (reg n a2) 0x4)) a1 (BitVec.ofNat 32 k) a2 = p + 4 := by
        simp +decide only [upd, ↓reduceIte]; rw [hp]; rfl
      obtain ⟨n6, c6, t6, hm6, k6⟩ := rs_zero o h2 h6 h8 hA n2 n6 n8 nT nF k (n := n5) (p + 4)
        ⟨u5.pc, by rw [u5.mem], fun _ => rfl⟩ hkp
        (by rw [u5.regs]; simp +decide only [upd, ↓reduceIte])
        (by rw [u5.regs, a2v])
        (by rw [rs_p4 p (by omega)]; omega) (by rw [rs_p4 p (by omega)]; omega)
        (by rw [rs_p4 p (by omega)]; omega) (by rw [u5.mem]; exact hc1)
      refine ⟨n6, .cons d1 (.cons d3 (.cons d4 (.cons d5 c6))), t6, ?_,
        fun r ha hb => by rw [k6 r ha hb, u5.regs, q4 r ha hb]⟩
      have : n5.mem = n1.mem := u5.mem
      rw [this] at hm6; exact hm1.trans hm6

/-- The registers that `boot`'s attempt loop keeps, at attempt `k`. -/
structure RsRegs (g : Fin 32 → Word) (k : Nat) (target : Word) : Prop where
  r8 : g 8 = BitVec.ofNat 32 k
  r9 : g 9 = 0x60009000
  r19 : g 19 = 0x60008800
  r22 : g 22 = target
  r23 : g 23 = 0x5A5A
  r24 : g 24 = 0x5555
  r25 : g 25 = 0x3333

/-- What `boot`'s attempt loop needs from memory. -/
structure RsEnv (Mb : Word → BitVec 8) : Prop where
  code : CodeIn Mb BT bootFnCode
  epr : CodeIn Mb EPR efuseProgramRunCode
  panic : PanicCode Mb

theorem rs_keep {g : Fin 32 → Word} (is : List BInstr) (M : Word → BitVec 8) (hz : g 0 = 0) {q : Fin 32}
    (hq : q ∉ is.filterMap BInstr.dst) : (runBlock is (M, g)).2 q = g q :=
  runBlock_reg is M g q hz hq

/-- The registers that `boot`'s attempt loop reads after a call. -/
abbrev rsK (r : Fin 32) : Prop := r ∈ ([2, 8, 9, 19, 22, 23, 24, 25, 26] : List (Fin 32))

/-- The second half of an attempt, from 0xBA: it writes the timing and
data registers, runs `efuse_program_run`, sees that the bit didn't read
back, and returns to 0x6A with the attempt count one higher. -/
theorem rs_tail {Mb : Word → BitVec 8} (E : RsEnv Mb) {target : Word} (k : Nat) (hk : k < 3)
    {n : Machine} (s : St n.mem BT n 0xBA (reg n)) (hI : RsI Mb n.mem) (R : RsRegs (reg n) k target)
    (h26 : reg n 26 = aluEval .and (aluEval .add (aluEval .srl (memLoad32 Mb efuseRd) 0xE) 0x1)
      (aluEval .xor (aluEval .srl (memLoad32 Mb efuseRd) 0xE) 0xFFFFFFFF)) :
    ∃ n', Steps n n' ∧ St n'.mem BT n' 0x6A (reg n') ∧ RsI Mb n'.mem ∧ RsRegs (reg n') (k + 1) target ∧
      reg n' sp = reg n sp := by
  have hc := hI.code E.code (by decide)
  have hz := s.zero
  have h9 := R.r9
  -- the timing registers
  obtain ⟨n1, c1, u1⟩ := s.block rsTim hc rsTim_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, rsTim, upd, ↓reduceIte, h9, true_and, and_true]
    refine ⟨rs_sep _ (by decide) (by decide), rs_sep _ (by decide) (by decide),
      rs_sep _ (by decide) (by decide), rs_sep _ (by decide) (by decide)⟩)
  have hI1 : RsI Mb (runBlock rsTim (n.mem, reg n)).1 := by
    simp only [runBlock, BInstr.run, rsTim]
    refine RsI.store (RsI.store (RsI.store (RsI.store hI _ ?_ ?_ ?_) _ ?_ ?_ ?_) _ ?_ ?_ ?_) _ ?_ ?_ ?_ <;>
      simp +decide only [upd, ↓reduceIte, h9]
  obtain ⟨M1, hM1⟩ : ∃ M1, (runBlock rsTim (n.mem, reg n)).1 = M1 := ⟨_, rfl⟩
  rw [hM1] at hI1 u1
  have hc1 : CodeIn M1 BT bootFnCode := hI1.code E.code (by decide)
  have t1 : St M1 BT n1 0xEC (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have q1 : ∀ r, rsK r → reg n1 r = reg n r := fun r hr => by
    rw [u1.regs, rs_keep _ _ hz (by simp only [rsTim]; revert hr; revert r; decide)]
  -- zero eight words from 0x60008800
  obtain ⟨n2, c2, u2⟩ := t1.block rsZ1 hc1 rsZ1_end ⟨trivial, trivial, trivial⟩
  have hz1 : reg n1 0 = 0 := t1.zero
  have q2 : ∀ r, rsK r → reg n2 r = reg n r := fun r hr => by
    rw [u2.regs, rs_keep _ _ hz1 (by simp only [rsZ1]; revert hr; revert r; decide), q1 r hr]
  have v2a1 : reg n2 a1 = 8 := by
    rw [u2.regs]; simp +decide only [runBlock, BInstr.run, rsZ1, upd, ↓reduceIte]
    rw [show reg n1 x0 = 0 from hz1]; rfl
  have v2a2 : reg n2 a2 = 0x60008800 := by
    rw [u2.regs]; simp +decide only [runBlock, BInstr.run, rsZ1, upd, ↓reduceIte]
    rw [q1 19 (by decide), R.r19]; rfl
  have t2 : St n2.mem BT n2 0xF0 (reg n2) := ⟨u2.pc, by rw [u2.mem], fun _ => rfl⟩
  have m2 : n2.mem = M1 := u2.mem
  have hc2 : CodeIn n2.mem BT bootFnCode := by rw [m2]; exact hc1
  obtain ⟨n3, d3, u3⟩ := t2.notTaken hc2 0xF2 bt_at_f0 (by decide) (by
    show (reg n2 a1 == reg n2 x0) = false; rw [v2a1, t2.zero]; rfl)
  obtain ⟨n4, c4, t4, hm4, k4⟩ := rs_zero 0xF0 bt_at_f2 bt_at_f6 bt_at_f8 bt_at_fa (by decide) (by decide)
    (by decide) (by decide) (by decide) 8 (n := n3) 0x60008800 ⟨u3.pc, by rw [u3.mem], fun _ => rfl⟩
    (by decide) (by rw [u3.regs, v2a1]; rfl) (by rw [u3.regs, v2a2]) (by decide) (by decide) (by decide)
    (by rw [u3.mem]; exact hc2)
  rw [show n3.mem = n2.mem from u3.mem, m2] at hm4
  have hI4 : RsI Mb n4.mem := hI1.trans hm4
  have hc4 : CodeIn n4.mem BT bootFnCode := hI4.code E.code (by decide)
  have q4 : ∀ r, rsK r → reg n4 r = reg n r := fun r hr => by
    rw [k4 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide), u3.regs, q2 r hr]
  -- zero three words from 0x60008820
  obtain ⟨n5, c5, u5⟩ := t4.block rsZ2 hc4 rsZ2_end ⟨trivial, trivial, trivial⟩
  have hz4 : reg n4 0 = 0 := t4.zero
  have q5 : ∀ r, rsK r → reg n5 r = reg n r := fun r hr => by
    rw [u5.regs, rs_keep _ _ hz4 (by simp only [rsZ2]; revert hr; revert r; decide), q4 r hr]
  have v5a1 : reg n5 a1 = 3 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, rsZ2, upd, ↓reduceIte]
    rw [show reg n4 x0 = 0 from hz4]; rfl
  have v5a2 : reg n5 a2 = 0x60008820 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, rsZ2, upd, ↓reduceIte]
    rw [q4 9 (by decide), h9]; rfl
  have t5 : St n5.mem BT n5 0x102 (reg n5) := ⟨u5.pc, by rw [u5.mem], fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have hc5 : CodeIn n5.mem BT bootFnCode := by rw [m5]; exact hc4
  obtain ⟨n6, d6, u6⟩ := t5.notTaken hc5 0x104 bt_at_102 (by decide) (by
    show (reg n5 a1 == reg n5 x0) = false; rw [v5a1, t5.zero]; rfl)
  obtain ⟨n7, c7, t7, hm7, k7⟩ := rs_zero 0x102 bt_at_104 bt_at_108 bt_at_10a bt_at_10c (by decide)
    (by decide) (by decide) (by decide) (by decide) 3 (n := n6) 0x60008820
    ⟨u6.pc, by rw [u6.mem], fun _ => rfl⟩ (by decide) (by rw [u6.regs, v5a1]; rfl) (by rw [u6.regs, v5a2])
    (by decide) (by decide) (by decide) (by rw [u6.mem]; exact hc5)
  rw [show n6.mem = n5.mem from u6.mem, m5] at hm7
  have hI7 : RsI Mb n7.mem := hI4.trans hm7
  have hc7 : CodeIn n7.mem BT bootFnCode := hI7.code E.code (by decide)
  have q7 : ∀ r, rsK r → reg n7 r = reg n r := fun r hr => by
    rw [k7 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide), u6.regs, q5 r hr]
  -- the data word, then `efuse_program_run(0x5A5A, 2)`
  have h9' : reg n7 9 = 0x60009000 := by rw [q7 9 (by decide), h9]
  obtain ⟨n8, c8, u8⟩ := t7.block rsRun hc7 rsRun_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, rsRun, upd, ↓reduceIte, h9', true_and, and_true]
    exact rs_sep _ (by decide) (by decide))
  have hI8 : RsI Mb (runBlock rsRun (n7.mem, reg n7)).1 := by
    simp only [runBlock, BInstr.run, rsRun]
    refine RsI.store hI7 _ ?_ ?_ ?_ <;> simp +decide only [upd, ↓reduceIte, h9']
  obtain ⟨M8, hM8⟩ : ∃ M8, (runBlock rsRun (n7.mem, reg n7)).1 = M8 := ⟨_, rfl⟩
  rw [hM8] at hI8 u8
  have hc8 : CodeIn M8 BT bootFnCode := hI8.code E.code (by decide)
  have hz7 : reg n7 0 = 0 := t7.zero
  have q8 : ∀ r, rsK r → reg n8 r = reg n r := fun r hr => by
    rw [u8.regs, rs_keep _ _ hz7 (by simp only [rsRun]; revert hr; revert r; decide), q7 r hr]
  have v8a1 : reg n8 a1 = 2 := by
    rw [u8.regs]; simp +decide only [runBlock, BInstr.run, rsRun, upd, ↓reduceIte]
  obtain ⟨n9, c9, pc9, mem9, regs9⟩ := u8.self.callRa (cb := EPR) hc8 bt_at_118 bt_at_11c (by decide) (by decide)
  have ce : CodeIn M8 EPR efuseProgramRunCode := hI8.code E.epr (by decide)
  obtain ⟨n10, c10, pc10, mem10, a010, k10⟩ := epr_correct (m := n9) ce
    ⟨by rw [pc9]; exact (add_ofNat_zero _).symm, mem9, fun _ => rfl⟩
    (by rw [regs9, updz u8.self.zero (by decide), v8a1]; rfl)
  have hI10 : RsI Mb n10.mem := by
    rw [mem10]; exact (hI8.store _ (by decide) (by decide) (by decide)).store _ (by decide) (by decide)
      (by decide)
  have hc10 : CodeIn n10.mem BT bootFnCode := hI10.code E.code (by decide)
  have q10 : ∀ r, rsK r → reg n10 r = reg n r := fun r hr => by
    have h : ∀ q : Fin 32, q ∈ ([10, 11, 12, 13, 14, 15, 1] : List (Fin 32)) → ¬ rsK q := by decide
    rw [k10 r (fun e => h r (by rw [e]; decide) hr) (fun e => h r (by rw [e]; decide) hr)
      (fun e => h r (by rw [e]; decide) hr) (fun e => h r (by rw [e]; decide) hr)
      (fun e => h r (by rw [e]; decide) hr) (fun e => h r (by rw [e]; decide) hr),
      regs9, updz u8.self.zero (fun e => h r (by rw [e]; decide) hr), q8 r hr]
  have t10 : St n10.mem BT n10 0x120 (reg n10) := ⟨by
    rw [pc10, regs9]; simp +decide only [upd, ↓reduceIte], rfl, fun _ => rfl⟩
  -- zero eight words from 0x60008800 again
  obtain ⟨n11, c11, u11⟩ := t10.block rsZ3 hc10 rsZ3_end ⟨trivial, trivial, trivial⟩
  have hz10 : reg n10 0 = 0 := t10.zero
  have q11 : ∀ r, rsK r → reg n11 r = reg n r := fun r hr => by
    rw [u11.regs, rs_keep _ _ hz10 (by simp only [rsZ3]; revert hr; revert r; decide), q10 r hr]
  have v11a0 : reg n11 a0 = 0 := by
    rw [u11.regs, rs_keep _ _ hz10 (by decide), a010]
  have v11a1 : reg n11 a1 = 8 := by
    rw [u11.regs]; simp +decide only [runBlock, BInstr.run, rsZ3, upd, ↓reduceIte]
    rw [show reg n10 x0 = 0 from hz10]; rfl
  have v11a2 : reg n11 a2 = 0x60008800 := by
    rw [u11.regs]; simp +decide only [runBlock, BInstr.run, rsZ3, upd, ↓reduceIte]
    rw [q10 19 (by decide), R.r19]; rfl
  have t11 : St n11.mem BT n11 0x124 (reg n11) := ⟨u11.pc, by rw [u11.mem], fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have hc11 : CodeIn n11.mem BT bootFnCode := by rw [m11]; exact hc10
  obtain ⟨n12, d12, u12⟩ := t11.notTaken hc11 0x126 bt_at_124 (by decide) (by
    show (reg n11 a1 == reg n11 x0) = false; rw [v11a1, t11.zero]; rfl)
  obtain ⟨n13, c13, t13, hm13, k13⟩ := rs_zero 0x124 bt_at_126 bt_at_12a bt_at_12c bt_at_12e (by decide)
    (by decide) (by decide) (by decide) (by decide) 8 (n := n12) 0x60008800
    ⟨u12.pc, by rw [u12.mem], fun _ => rfl⟩ (by decide) (by rw [u12.regs, v11a1]; rfl) (by rw [u12.regs, v11a2])
    (by decide) (by decide) (by decide) (by rw [u12.mem]; exact hc11)
  rw [show n12.mem = n11.mem from u12.mem, m11] at hm13
  have hI13 : RsI Mb n13.mem := hI10.trans hm13
  have hc13 : CodeIn n13.mem BT bootFnCode := hI13.code E.code (by decide)
  have q13 : ∀ r, rsK r → reg n13 r = reg n r := fun r hr => by
    rw [k13 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide), u12.regs, q11 r hr]
  have v13a0 : reg n13 a0 = 0 := by rw [k13 a0 (by decide) (by decide), u12.regs, v11a0]
  -- the bit didn't read back
  obtain ⟨n14, d14, u14⟩ := t13.taken hc13 0x13E bt_at_130 (by decide) (by
    show (reg n13 a0 == reg n13 x0) = true; rw [v13a0, t13.zero]; rfl)
  have t14 : St n13.mem BT n14 0x13E (reg n14) := ⟨u14.pc, u14.mem, fun _ => rfl⟩
  have h9'' : reg n14 9 = 0x60009000 := by rw [u14.regs, q13 9 (by decide), h9]
  obtain ⟨n15, c15, u15⟩ := t14.block rsChk hc13 rsChk_end
    ⟨by show (reg n14 9 + 0xFFFFF83C).toNat % 4 = 0; rw [h9'']; decide, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have hz14 : reg n14 0 = 0 := t14.zero
  have q15 : ∀ r, rsK r → r ≠ 8 → reg n15 r = reg n r := fun r hr h8 => by
    rw [u15.regs, rs_keep _ _ hz14 (by simp only [rsChk]; revert h8 hr; revert r; decide), u14.regs, q13 r hr]
  have v15 : reg n15 8 = BitVec.ofNat 32 (k + 1) := by
    have hw : memLoad32 n13.mem (reg n14 9 + 0xFFFFF83C) = memLoad32 Mb efuseRd := by
      rw [h9'']; exact hI13.field
    rw [u15.regs]; simp +decide only [runBlock, BInstr.run, rsChk, upd, ↓reduceIte]
    rw [hw, u14.regs 26, u14.regs 8, q13 26 (by decide), q13 8 (by decide), h26, R.r8]
    rw [show ∀ w : Word, aluEval .and (aluEval .and (aluEval .add w 0x1) (aluEval .xor w 0xFFFFFFFF)) w = 0
      from rs_bit]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;> decide
  have t15 : St n13.mem BT n15 0x154 (reg n15) := ⟨u15.pc, u15.mem, fun _ => rfl⟩
  obtain ⟨n16, d16, u16⟩ := t15.jump hc13 bt_at_154 (off' := 0x6A) (by decide) (by rw [t15.pc]; decide)
  have q16 : ∀ r, rsK r → r ≠ 8 → reg n16 r = reg n r := fun r hr h8 => by rw [u16.regs, q15 r hr h8]
  refine ⟨n16, c1.trans (c2.trans (.cons d3 (c4.trans (c5.trans (.cons d6 (c7.trans (c8.trans (c9.trans
    (c10.trans (c11.trans (.cons d12 (c13.trans (.cons d14 (c15.trans (.single d16))))))))))))))),
    ⟨u16.pc, rfl, fun _ => rfl⟩, by rw [u16.mem]; exact hI13, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    q16 sp (by decide) (by decide)⟩
  · rw [u16.regs, v15]
  · rw [q16 9 (by decide) (by decide), h9]
  · rw [q16 19 (by decide) (by decide), R.r19]
  · rw [q16 22 (by decide) (by decide), R.r22]
  · rw [q16 23 (by decide) (by decide), R.r23]
  · rw [q16 24 (by decide) (by decide), R.r24]
  · rw [q16 25 (by decide) (by decide), R.r25]

/-- An attempt from 0x6A while the eFuse level is below the target: the
fourth attempt halts, and an earlier one halts or returns to 0x6A with
the attempt count one higher. -/
theorem rs_iter {Mb : Word → BitVec 8} (E : RsEnv Mb) {target : Word}
    (hlt : (btPop (memLoad32 Mb efuseRd)).ult target = true) (k : Nat) (hk : k ≤ 3)
    {n : Machine} (s : St n.mem BT n 0x6A (reg n)) (hI : RsI Mb n.mem) (R : RsRegs (reg n) k target)
    (hR : Room (reg n sp) 16) :
    (k < 3 ∧ ∃ n', Steps n n' ∧ St n'.mem BT n' 0x6A (reg n') ∧ RsI Mb n'.mem ∧
      RsRegs (reg n') (k + 1) target ∧ reg n' sp = reg n sp) ∨ Panics n := by
  have hc := hI.code E.code (by decide)
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block rsHead hc rsHead_end
    ⟨by show (reg n 9 + 0xFFFFF83C).toNat % 4 = 0; rw [R.r9]; decide, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial, trivial, trivial, trivial, trivial⟩
  have hw : memLoad32 n.mem (reg n 9 + 0xFFFFF83C) = memLoad32 Mb efuseRd := by rw [R.r9]; exact hI.field
  have v1a1 : reg n1 a1 = btPop (memLoad32 Mb efuseRd) := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, rsHead, upd, ↓reduceIte]
    rw [hw, R.r24, R.r25]; rfl
  have v1a0 : reg n1 a0 = aluEval .srl (memLoad32 Mb efuseRd) 0xE := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, rsHead, upd, ↓reduceIte]; rw [hw]
  have q1 : ∀ r, rsK r → reg n1 r = reg n r := fun r hr => by
    rw [u1.regs, rs_keep _ _ hz (by simp only [rsHead]; revert hr; revert r; decide)]
  have t1 : St n.mem BT n1 0x9A (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  obtain ⟨n2, d2, u2⟩ := t1.notTaken hc 0x9E bt_at_9a (by decide) (by
    show (!(reg n1 a1).ult (reg n1 22)) = false; rw [v1a1, q1 22 (by decide), R.r22, hlt]; rfl)
  have t2 : St n.mem BT n2 0x9E (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  obtain ⟨n3, c3, u3⟩ := t2.block rsCnt hc rsCnt_end ⟨trivial, trivial, trivial⟩
  have hz2 : reg n2 0 = 0 := t2.zero
  have t3 : St n.mem BT n3 0xA4 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  have q3 : ∀ r, rsK r → reg n3 r = reg n r := fun r hr => by
    rw [u3.regs, rs_keep _ _ hz2 (by simp only [rsCnt]; revert hr; revert r; decide), u2.regs, q1 r hr]
  have v3a1 : reg n3 a1 = BitVec.ofNat 32 k &&& 0xFF := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, rsCnt, upd, ↓reduceIte]
    rw [u2.regs, q1 8 (by decide), R.r8]; rfl
  have v3a2 : reg n3 a2 = 2 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, rsCnt, upd, ↓reduceIte]
  have v3a0 : reg n3 a0 = aluEval .srl (memLoad32 Mb efuseRd) 0xE := by
    rw [u3.regs, rs_keep _ _ hz2 (by decide), u2.regs, v1a0]
  have halt : ∀ n' : Machine, Steps n n' → St n.mem BT n' 0x29C (reg n') → reg n' sp = reg n sp → Panics n :=
    fun n' c t hsp => Panics.of_steps c (rs_halt ⟨t.pc, rfl, fun _ => rfl⟩ (by rw [t.mem]; exact hc)
      (by rw [t.mem]; exact hI.panic E.panic) (by rw [hsp]; exact hR))
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · obtain ⟨n4, d4, u4⟩ := t3.notTaken hc 0xA8 bt_at_a4 (by decide) (by
      show (reg n3 a2).ult (reg n3 a1) = false; rw [v3a2, v3a1]
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;> decide)
    have t4 : St n.mem BT n4 0xA8 (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
    obtain ⟨n5, c5, u5⟩ := t4.block rsBit hc rsBit_end ⟨trivial, trivial, trivial, trivial, trivial⟩
    have hz4 : reg n4 0 = 0 := t4.zero
    have t5 : St n.mem BT n5 0xB6 (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
    have q5 : ∀ r, rsK r → r ≠ 26 → reg n5 r = reg n r := fun r hr h26 => by
      rw [u5.regs, rs_keep _ _ hz4 (by simp only [rsBit]; revert h26 hr; revert r; decide), u4.regs, q3 r hr]
    have v5 : reg n5 26 = aluEval .and (aluEval .add (aluEval .srl (memLoad32 Mb efuseRd) 0xE) 0x1)
        (aluEval .xor (aluEval .srl (memLoad32 Mb efuseRd) 0xE) 0xFFFFFFFF) := by
      rw [u5.regs]; simp +decide only [runBlock, BInstr.run, rsBit, upd, ↓reduceIte]; rw [u4.regs, v3a0]
    have c4 : Steps n n4 := c1.trans (.cons d2 (c3.trans (.single d4)))
    by_cases h0 : (reg n5 a0 == reg n5 x0) = true
    · obtain ⟨n6, d6, u6⟩ := t5.taken hc 0x29C bt_at_b6 (by decide) h0
      exact Or.inr (halt n6 (c4.trans (c5.trans (.single d6))) ⟨u6.pc, u6.mem, fun _ => rfl⟩
        (by rw [u6.regs, q5 sp (by decide) (by decide)]))
    · obtain ⟨n6, d6, u6⟩ := t5.notTaken hc 0xBA bt_at_b6 (by decide) (by simp only [Bool.not_eq_true] at h0; exact h0)
      have q6 : ∀ r, rsK r → r ≠ 26 → reg n6 r = reg n r := fun r hr h26 => by rw [u6.regs, q5 r hr h26]
      obtain ⟨n7, c7, t7, hI7, R7, sp7⟩ := rs_tail E k hk3 (n := n6) ⟨u6.pc, by rw [u6.mem], fun _ => rfl⟩
        (by rw [u6.mem]; exact hI)
        ⟨by rw [q6 8 (by decide) (by decide), R.r8], by rw [q6 9 (by decide) (by decide), R.r9],
          by rw [q6 19 (by decide) (by decide), R.r19], by rw [q6 22 (by decide) (by decide), R.r22],
          by rw [q6 23 (by decide) (by decide), R.r23], by rw [q6 24 (by decide) (by decide), R.r24],
          by rw [q6 25 (by decide) (by decide), R.r25]⟩
        (by rw [u6.regs, v5])
      exact Or.inl ⟨hk3, n7, c4.trans (c5.trans (.cons d6 c7)), t7, hI7, R7,
        by rw [sp7, u6.regs, q5 sp (by decide) (by decide)]⟩
  · obtain ⟨n4, d4, u4⟩ := t3.taken hc 0x29C bt_at_a4 (by decide) (by
      show (reg n3 a2).ult (reg n3 a1) = true; rw [v3a2, v3a1, show k = 3 by omega]; decide)
    exact Or.inr (halt n4 (c1.trans (.cons d2 (c3.trans (.single d4)))) ⟨u4.pc, u4.mem, fun _ => rfl⟩
      (by rw [u4.regs, q3 sp (by decide)]))

theorem rs_loop {Mb : Word → BitVec 8} (E : RsEnv Mb) {target : Word}
    (hlt : (btPop (memLoad32 Mb efuseRd)).ult target = true) :
    ∀ d k {n : Machine}, k + d = 3 → St n.mem BT n 0x6A (reg n) → RsI Mb n.mem → RsRegs (reg n) k target →
      Room (reg n sp) 16 → Panics n
  | d, k, n, hd, s, hI, R, hR => by
    rcases rs_iter E hlt k (by omega) s hI R hR with ⟨hk, n', c, s', hI', R', sp'⟩ | hp
    · match d, hd with
      | 0, hd => exact absurd hd (by omega)
      | d + 1, hd => exact Panics.of_steps c (rs_loop E hlt d (k + 1) (by omega) s' hI' R' (by rw [sp']; exact hR))
    · exact hp

/-- `boot`'s raise of the security level, from 0x3E: when the eFuse level
`btPop` reads reaches `target`, `boot` reaches the cache setup at 0x156
with memory unchanged; otherwise it halts. -/
theorem rs_raise {n : Machine} (E : RsEnv n.mem) {target : Word} (s : St n.mem BT n 0x3E (reg n))
    (h9 : reg n 9 = 0x60009000) (h22 : reg n 22 = target) (hR : Room (reg n sp) 16) :
    (∃ n', Steps n n' ∧ St n.mem BT n' 0x156 (reg n') ∧
      (btPop (memLoad32 n.mem efuseRd)).ult target = false ∧
      ∀ r, r ∈ ([2, 20, 22, 26] : List (Fin 32)) → reg n' r = reg n r) ∨ Panics n := by
  have hc := E.code
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block rsInit hc rsInit_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial, trivial⟩
  have t1 : St n.mem BT n1 0x6A (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have rv : ∀ r : Fin 32, reg n1 r = (runBlock rsInit (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  have q1 : ∀ r, r ∈ ([2, 9, 20, 22, 26] : List (Fin 32)) → reg n1 r = reg n r := fun r hr => by
    rw [rv, rs_keep _ _ hz (by simp only [rsInit]; revert hr; revert r; decide)]
  have R1 : RsRegs (reg n1) 0 target := by
    refine ⟨?_, by rw [q1 9 (by decide), h9], ?_, by rw [q1 22 (by decide), h22], ?_, ?_, ?_⟩ <;>
      rw [rv] <;> simp +decide only [runBlock, BInstr.run, rsInit, upd, ↓reduceIte] <;>
      (try rw [show reg n x0 = 0 from hz]) <;> (try rw [h9]) <;> rfl
  by_cases hlt : (btPop (memLoad32 n.mem efuseRd)).ult target = true
  · exact Or.inr (Panics.of_steps c1 (rs_loop E hlt 3 0 rfl (⟨u1.pc, rfl, fun _ => rfl⟩ : St n1.mem BT n1 0x6A (reg n1)) (by rw [u1.mem]; exact RsI.refl _) R1
      (by rw [q1 sp (by decide)]; exact hR)))
  · obtain ⟨n2, c2, u2⟩ := t1.block rsHead hc rsHead_end
      ⟨by show (reg n1 9 + 0xFFFFF83C).toNat % 4 = 0; rw [R1.r9]; decide, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
        trivial, trivial, trivial, trivial, trivial, trivial⟩
    have v2 : reg n2 a1 = btPop (memLoad32 n.mem efuseRd) := by
      rw [u2.regs]; simp +decide only [runBlock, BInstr.run, rsHead, upd, ↓reduceIte]
      rw [R1.r9, R1.r24, R1.r25]; rfl
    have hz1 : reg n1 0 = 0 := t1.zero
    have q2 : ∀ r, r ∈ ([2, 20, 22, 26] : List (Fin 32)) → reg n2 r = reg n r := fun r hr => by
      rw [u2.regs, rs_keep _ _ hz1 (by simp only [rsHead]; revert hr; revert r; decide),
        q1 r (by revert hr; revert r; decide)]
    have t2 : St n.mem BT n2 0x9A (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
    have hge : (btPop (memLoad32 n.mem efuseRd)).ult target = false := by simpa using hlt
    obtain ⟨n3, d3, u3⟩ := t2.taken hc 0x156 bt_at_9a (by decide) (by
      show (!(reg n2 a1).ult (reg n2 22)) = true; rw [v2, q2 22 (by decide), h22, hge]; rfl)
    exact Or.inl ⟨n3, c1.trans (c2.trans (.single d3)), ⟨u3.pc, u3.mem, fun _ => rfl⟩, hge,
      fun r hr => by rw [u3.regs, q2 r hr]⟩

end C3.RV32.Cur
