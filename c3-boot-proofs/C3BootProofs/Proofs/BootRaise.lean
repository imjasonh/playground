import C3BootProofs.Proofs.BootSpec

/-!
# `c3_bootloader::boot`: raising the security level

When the target security level is above the level in the eFuses, `boot`
programs eFuse bits in at most three attempts before it copies the image.
Each attempt reads the eFuse word at 0x6000883C, counts the level from
it, and returns when the level reaches the target. Otherwise it writes
the next bit's timing and data registers, runs `efuse_program_run`, and
checks that the bit reads back.

The eFuse controller comes in through its contract `EfuseCtl`: a call of
`efuse_program_run` leaves memory outside the controller's registers
unchanged and may set bits of the level word at 0x6000883C. `rs_raise`
proves the result: from the attempt loop's setup, `boot` reaches the cache
setup when the level it reads reaches the target, with memory outside the
controller's registers unchanged and the level word its old value with
some bits set, and halts otherwise.
-/

namespace C3.RV32.Cur

open C3.Image

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

/-- `M` agrees with `Mb` outside the eFuse controller's registers
0x60008800 to 0x600089FF, and on the word at 0x6000883C that holds the
level. -/
def RsJ (Mb M : Word → BitVec 8) : Prop :=
  ∀ x : Word, (x.toNat < 0x60008800 ∨ 0x60008A00 ≤ x.toNat ∨
    (0x6000883C ≤ x.toNat ∧ x.toNat < 0x60008840)) → M x = Mb x

theorem RsJ.refl (M : Word → BitVec 8) : RsJ M M := fun _ _ => rfl

theorem RsJ.trans {M0 M1 M2 : Word → BitVec 8} (h1 : RsJ M0 M1) (h2 : RsJ M1 M2) : RsJ M0 M2 :=
  fun x hx => (h2 x hx).trans (h1 x hx)

theorem RsJ.store {Mb M : Word → BitVec 8} (h : RsJ Mb M) {a : Word} (v : Word)
    (h1 : 0x60008800 ≤ a.toNat) (h2 : a.toNat + 4 ≤ 0x60008A00)
    (h3 : a.toNat + 4 ≤ 0x6000883C ∨ 0x60008840 ≤ a.toNat) : RsJ Mb (memStore32 M a v) := fun x hx => by
  have hs : Sep a 4 x 1 := by
    rcases hx with hx | hx | ⟨hx1, hx2⟩
    · exact (sep_of_le (by omega) (by omega)).symm
    · exact sep_of_le (by omega) (by have := x.isLt; omega)
    · rcases h3 with h3 | h3
      · exact sep_of_le (by omega) (by omega)
      · exact (sep_of_le (by omega) (by omega)).symm
  rw [memStore32_get_sep hs]; exact h x hx

theorem RsJ.code {Mb M : Word → BitVec 8} {b : Word} {code : List Nat} (hc : CodeIn Mb b code)
    (hl : b.toNat + code.length ≤ 0x60000000) (h : RsJ Mb M) : CodeIn M b code := fun i hi => by
  rw [h _ (Or.inl (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]; exact hc i hi

theorem RsJ.field {Mb M : Word → BitVec 8} (h : RsJ Mb M) : memLoad32 M efuseRd = memLoad32 Mb efuseRd :=
  memLoad32_congr fun j hj => h _ (Or.inr (Or.inr (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show efuseRd.toNat = 0x6000883C from rfl]
    exact ⟨by omega, by omega⟩)))

theorem RsJ.out {Mb M : Word → BitVec 8} (h : RsJ Mb M) : EfOut Mb M := fun x hx =>
  h x (hx.elim Or.inl fun h => Or.inr (Or.inl h))

theorem EfOut.refl (M : Word → BitVec 8) : EfOut M M := fun _ _ => rfl

theorem EfOut.trans {M0 M1 M2 : Word → BitVec 8} (h1 : EfOut M0 M1) (h2 : EfOut M1 M2) : EfOut M0 M2 :=
  fun x hx => (h2 x hx).trans (h1 x hx)

theorem EfOut.code {Mb M : Word → BitVec 8} {b : Word} {code : List Nat} (h : EfOut Mb M)
    (hc : CodeIn Mb b code) (hl : b.toNat + code.length ≤ 0x60000000) : CodeIn M b code := fun i hi => by
  rw [h _ (Or.inl (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]; exact hc i hi

theorem EfOut.panic {Mb M : Word → BitVec 8} (h : EfOut Mb M) (hP : PanicCode Mb) : PanicCode M := fun p hp => by
  have hm := panicFns_mid p hp
  exact h.code (hP p hp) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)

theorem EprAt.out {Mb M : Word → BitVec 8} (h : EprAt Mb) (hO : EfOut Mb M) : EprAt M :=
  let ⟨code, hc, hl, hF⟩ := h
  ⟨code, hO.code hc hl, hl, hF⟩

/-- **A plain-memory eFuse controller meets `EfuseCtl`.** When the
controller's registers are plain memory, `efuse_program_run` writes the
command and the mask, polls to its timeout, and leaves the level word as it
was, so the contract holds with no new bits. The contract is consistent. -/
theorem efuseCtl_plain : EfuseCtl efuseProgramRunCode := ⟨fun m hcm hpc ha1 => by
  obtain ⟨m', c, pc, mem, _, k⟩ := epr_correct hcm
    ⟨by rw [hpc]; exact (add_ofNat_zero _).symm, rfl, fun _ => rfl⟩
    (by rcases ha1 with h | h <;> rw [h] <;> decide)
  have hJ : RsJ m.mem m'.mem := by
    rw [mem]
    exact ((RsJ.refl _).store _ (by decide) (by decide) (by decide)).store _ (by decide) (by decide)
      (by decide)
  exact ⟨m', c, pc, k, hJ.out, 0, by rw [hJ.field]; exact BitVec.or_zero.symm⟩⟩

theorem eprAt_of_code {M : Word → BitVec 8} (hc : CodeIn M EPR efuseProgramRunCode) : EprAt M :=
  ⟨efuseProgramRunCode, hc, by decide, efuseCtl_plain⟩

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

/-- The security level as `boot` counts it from the eFuse word `w`: the
number of set bits among bits 14 to 29, computed the way the compiled code
computes it. -/
def btPop (w : Word) : Word :=
  let a0 := aluEval .srl w 0xE
  let b1 := aluEval .sub a0 (aluEval .and (aluEval .srl w 0xF) 0x5555)
  let b2 := aluEval .add (aluEval .and b1 0x3333) (aluEval .and (aluEval .srl b1 0x2) 0x3333)
  let b3 := aluEval .add b2 (aluEval .srl b2 0x4)
  aluEval .add (aluEval .and b3 0xF) (aluEval .srl (aluEval .sll b3 0x14) 0x1C)

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
    (hP : PanicCode n.mem) (hR : Room (reg n sp) 16) : HaltsWith n 0xE1 := by
  obtain ⟨n1, d1, u1⟩ := s.aluImm hc bt_at_29c (off' := 0x2A0) (by decide)
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1.self.callRa (cb := haltBase) hc bt_at_2a0 bt_at_2a4
    (by decide) (by decide)
  have sp2 : reg n2 sp = reg n sp := by
    rw [regs2, updz u1.self.zero (by decide), u1.regs, updz s.zero (by decide)]
  have a02 : reg n2 a0 = 0xE1 := by
    rw [regs2, updz u1.self.zero (by decide), u1.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [s.zero]; rfl
  have hh := halt_haltCode n2 (by rw [mem2]; exact hP) pc2 (by rw [sp2]; exact hR)
  rw [a02] at hh
  exact hh.of_steps (.cons d1 c2)

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
      ∃ n', Steps n n' ∧ St n'.mem BT n' (o + 0xC) (reg n') ∧ RsJ n.mem n'.mem ∧
        ∀ r, r ≠ a1 → r ≠ a2 → reg n' r = reg n r
  | 0, _, _, _, hk, _, _, _, _, _, _ => absurd hk (by decide)
  | k + 1, n, p, s, _, h1, hp, hal, hlo, hhi, hc => by
    have hz := s.zero
    obtain ⟨n1, d1, u1⟩ := s.sw hc h2 n2 (by rw [hp, add_lit_zero]; exact hal)
    rw [hp, add_lit_zero, show reg n x0 = 0 from hz] at u1
    have hm1 : RsJ n.mem n1.mem := by
      rw [u1.mem]; exact (RsJ.refl _).store _ hlo (by omega) (Or.inl (by omega))
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

/-- What `boot`'s attempt loop needs from memory: its code, the panic
handlers, and an `efuse_program_run` that meets the eFuse controller's
contract. -/
structure RsEnv (Mb : Word → BitVec 8) : Prop where
  code : CodeIn Mb BT bootFnCode
  epr : EprAt Mb
  panic : PanicCode Mb

theorem rs_keep {g : Fin 32 → Word} (is : List BInstr) (M : Word → BitVec 8) (hz : g 0 = 0) {q : Fin 32}
    (hq : q ∉ is.filterMap BInstr.dst) : (runBlock is (M, g)).2 q = g q :=
  runBlock_reg is M g q hz hq

/-- The registers that `boot`'s attempt loop reads after a call. -/
abbrev rsK (r : Fin 32) : Prop := r ∈ ([2, 8, 9, 19, 20, 22, 23, 24, 25, 26] : List (Fin 32))

/-- The attempt count after the read-back check: one more when the bit
didn't read back, and 0 when it did. -/
theorem rs_chkv (k : Nat) (hk : k < 3) (y : Word) :
    aluEval .and (aluEval .add (BitVec.ofNat 32 k) 0x1) (aluEval .add (aluEval .sltu 0 y) 0xFFFFFFFF) =
      if y = 0 then BitVec.ofNat 32 (k + 1) else 0 := by
  by_cases hy : y = 0
  · subst hy; rw [if_pos rfl]; rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;> decide
  · rw [if_neg hy]
    have hn : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq h)
    have h1 : aluEval .sltu 0 y = 1 := by
      show (if (0 : Word).ult y then 1 else 0) = 1
      rw [if_pos (by simp only [BitVec.ult, decide_eq_true_eq]; exact Nat.pos_of_ne_zero hn)]
    rw [h1]
    show (BitVec.ofNat 32 k + 1) &&& ((1 : Word) + 0xFFFFFFFF) = 0
    rw [show (1 : Word) + 0xFFFFFFFF = 0 from rfl]; exact BitVec.and_zero

/-- The read-back check from 0x13E: the attempt count goes up by one, or
to 0 when the eFuse word now has the bit `boot` programmed, so it differs
from the word `w` the attempt started from. `boot` then returns to 0x6A. -/
theorem rs_chk {k : Nat} (hk : k < 3) {M : Word → BitVec 8} {n : Machine} (s : St M BT n 0x13E (reg n))
    (hc : CodeIn M BT bootFnCode) (h9 : reg n 9 = 0x60009000) (h8 : reg n 8 = BitVec.ofNat 32 k) {w : Word}
    (h26 : reg n 26 = aluEval .and (aluEval .add (aluEval .srl w 0xE) 0x1)
      (aluEval .xor (aluEval .srl w 0xE) 0xFFFFFFFF)) :
    ∃ n', Steps n n' ∧ St M BT n' 0x6A (reg n') ∧ (∀ r, rsK r → r ≠ 8 → reg n' r = reg n r) ∧
      (reg n' 8 = BitVec.ofNat 32 (k + 1) ∨ (reg n' 8 = 0 ∧ memLoad32 M efuseRd ≠ w)) := by
  obtain ⟨n1, c1, u1⟩ := s.block rsChk hc rsChk_end
    ⟨by show (reg n 9 + 0xFFFFF83C).toNat % 4 = 0; rw [h9]; decide, trivial, trivial, trivial, trivial,
      trivial, trivial, trivial, trivial⟩
  have hz := s.zero
  have q1 : ∀ r, rsK r → r ≠ 8 → reg n1 r = reg n r := fun r hr h8' => by
    rw [u1.regs, rs_keep _ _ hz (by simp only [rsChk]; revert h8' hr; revert r; decide)]
  have hw : memLoad32 M (reg n 9 + 0xFFFFF83C) = memLoad32 M efuseRd := by rw [h9]; rfl
  have v1 : reg n1 8 = aluEval .and (aluEval .add (BitVec.ofNat 32 k) 0x1)
      (aluEval .add (aluEval .sltu 0 (aluEval .sll (aluEval .and (reg n 26)
        (aluEval .srl (memLoad32 M efuseRd) 0xE)) 0x10)) 0xFFFFFFFF) := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, rsChk, upd, ↓reduceIte]
    rw [hw, h8]
  have t1 : St M BT n1 0x154 (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  obtain ⟨n2, d2, u2⟩ := t1.jump hc bt_at_154 (off' := 0x6A) (by decide) (by rw [t1.pc]; decide)
  refine ⟨n2, c1.trans (.single d2), ⟨u2.pc, u2.mem, fun _ => rfl⟩,
    fun r hr h8' => by rw [u2.regs, q1 r hr h8'], ?_⟩
  rw [u2.regs, v1, rs_chkv k hk]
  split
  · exact Or.inl rfl
  · rename_i hy
    refine Or.inr ⟨rfl, fun he => hy ?_⟩
    rw [h26, he, show ∀ w : Word, aluEval .and (aluEval .and (aluEval .add w 0x1) (aluEval .xor w 0xFFFFFFFF)) w = 0
      from rs_bit]
    rfl

/-- The second half of an attempt, from 0xBA: it writes the timing and
data registers, runs `efuse_program_run` with the program command, zeroes
the data registers, reloads the read registers when the run reported
success, checks whether the bit reads back, and returns to 0x6A. Memory
outside the eFuse controller's registers is unchanged and the level word
only gains bits. The attempt count goes up by one, or back to 0 when the
level word changed. -/
theorem rs_tail {Mb : Word → BitVec 8} (E : RsEnv Mb) {target : Word} (k : Nat) (hk : k < 3)
    {n : Machine} (s : St n.mem BT n 0xBA (reg n)) (hO : EfOut Mb n.mem) (R : RsRegs (reg n) k target)
    (h26 : reg n 26 = aluEval .and (aluEval .add (aluEval .srl (memLoad32 n.mem efuseRd) 0xE) 0x1)
      (aluEval .xor (aluEval .srl (memLoad32 n.mem efuseRd) 0xE) 0xFFFFFFFF)) :
    ∃ n', Steps n n' ∧ St n'.mem BT n' 0x6A (reg n') ∧ EfOut Mb n'.mem ∧
      (∃ X, memLoad32 n'.mem efuseRd = memLoad32 n.mem efuseRd ||| X) ∧
      (RsRegs (reg n') (k + 1) target ∨
        (memLoad32 n'.mem efuseRd ≠ memLoad32 n.mem efuseRd ∧ RsRegs (reg n') 0 target)) ∧
      ∀ r, r ∈ ([2, 20] : List (Fin 32)) → reg n' r = reg n r := by
  have hcn : CodeIn n.mem BT bootFnCode := hO.code E.code (by decide)
  have hI : RsJ n.mem n.mem := RsJ.refl _
  have hc := hI.code hcn (by decide)
  have hz := s.zero
  have h9 := R.r9
  -- the timing registers
  obtain ⟨n1, c1, u1⟩ := s.block rsTim hc rsTim_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, rsTim, upd, ↓reduceIte, h9, true_and, and_true]
    refine ⟨rs_sep _ (by decide) (by decide), rs_sep _ (by decide) (by decide),
      rs_sep _ (by decide) (by decide), rs_sep _ (by decide) (by decide)⟩)
  have hI1 : RsJ n.mem (runBlock rsTim (n.mem, reg n)).1 := by
    simp only [runBlock, BInstr.run, rsTim]
    refine RsJ.store (RsJ.store (RsJ.store (RsJ.store hI _ ?_ ?_ ?_) _ ?_ ?_ ?_) _ ?_ ?_ ?_) _ ?_ ?_ ?_ <;>
      simp +decide only [upd, ↓reduceIte, h9]
  obtain ⟨M1, hM1⟩ : ∃ M1, (runBlock rsTim (n.mem, reg n)).1 = M1 := ⟨_, rfl⟩
  rw [hM1] at hI1 u1
  have hc1 : CodeIn M1 BT bootFnCode := hI1.code hcn (by decide)
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
  have hI4 : RsJ n.mem n4.mem := hI1.trans hm4
  have hc4 : CodeIn n4.mem BT bootFnCode := hI4.code hcn (by decide)
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
  have hI7 : RsJ n.mem n7.mem := hI4.trans hm7
  have hc7 : CodeIn n7.mem BT bootFnCode := hI7.code hcn (by decide)
  have q7 : ∀ r, rsK r → reg n7 r = reg n r := fun r hr => by
    rw [k7 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide), u6.regs, q5 r hr]
  -- the data word, then `efuse_program_run(0x5A5A, 2)`
  have h9' : reg n7 9 = 0x60009000 := by rw [q7 9 (by decide), h9]
  obtain ⟨n8, c8, u8⟩ := t7.block rsRun hc7 rsRun_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, rsRun, upd, ↓reduceIte, h9', true_and, and_true]
    exact rs_sep _ (by decide) (by decide))
  have hI8 : RsJ n.mem (runBlock rsRun (n7.mem, reg n7)).1 := by
    simp only [runBlock, BInstr.run, rsRun]
    refine RsJ.store hI7 _ ?_ ?_ ?_ <;> simp +decide only [upd, ↓reduceIte, h9']
  obtain ⟨M8, hM8⟩ : ∃ M8, (runBlock rsRun (n7.mem, reg n7)).1 = M8 := ⟨_, rfl⟩
  rw [hM8] at hI8 u8
  have hc8 : CodeIn M8 BT bootFnCode := hI8.code hcn (by decide)
  have hz7 : reg n7 0 = 0 := t7.zero
  have q8 : ∀ r, rsK r → reg n8 r = reg n r := fun r hr => by
    rw [u8.regs, rs_keep _ _ hz7 (by simp only [rsRun]; revert hr; revert r; decide), q7 r hr]
  have v8a1 : reg n8 a1 = 2 := by
    rw [u8.regs]; simp +decide only [runBlock, BInstr.run, rsRun, upd, ↓reduceIte]
  obtain ⟨n9, c9, pc9, mem9, regs9⟩ := u8.self.callRa (cb := EPR) hc8 bt_at_118 bt_at_11c (by decide) (by decide)
  obtain ⟨ec, hce, -, hF⟩ := E.epr.out (hO.trans hI8.out)
  obtain ⟨n10, c10, pc10, k10, hO10, X1, hX1⟩ := hF.run n9 (by rw [mem9]; exact hce) pc9
    (Or.inr (by rw [regs9, updz u8.self.zero (by decide), v8a1]))
  rw [mem9] at hO10 hX1
  have hc10 : CodeIn n10.mem BT bootFnCode := hO10.code hc8 (by decide)
  have nk : ∀ r, rsK r → r ∉ ([10, 11, 12, 13, 14, 15, 1] : List (Fin 32)) := by decide
  have q10 : ∀ r, rsK r → reg n10 r = reg n r := fun r hr => by
    have h := nk r hr
    rw [k10 r (fun e => h (by rw [e]; decide)) (fun e => h (by rw [e]; decide))
      (fun e => h (by rw [e]; decide)) (fun e => h (by rw [e]; decide))
      (fun e => h (by rw [e]; decide)) (fun e => h (by rw [e]; decide)),
      regs9, updz u8.self.zero (fun e => h (by rw [e]; decide)), q8 r hr]
  have t10 : St n10.mem BT n10 0x120 (reg n10) := ⟨by
    rw [pc10, regs9]; simp +decide only [upd, ↓reduceIte], rfl, fun _ => rfl⟩
  -- zero eight words from 0x60008800 again
  obtain ⟨n11, c11, u11⟩ := t10.block rsZ3 hc10 rsZ3_end ⟨trivial, trivial, trivial⟩
  have hz10 : reg n10 0 = 0 := t10.zero
  have q11 : ∀ r, rsK r → reg n11 r = reg n r := fun r hr => by
    rw [u11.regs, rs_keep _ _ hz10 (by simp only [rsZ3]; revert hr; revert r; decide), q10 r hr]
  have v11a0 : reg n11 a0 = reg n10 a0 := by
    rw [u11.regs, rs_keep _ _ hz10 (by decide)]
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
  have hc13 : CodeIn n13.mem BT bootFnCode := hm13.code hc10 (by decide)
  have q13 : ∀ r, rsK r → reg n13 r = reg n r := fun r hr => by
    rw [k13 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide), u12.regs, q11 r hr]
  have v13a0 : reg n13 a0 = reg n10 a0 := by rw [k13 a0 (by decide) (by decide), u12.regs, v11a0]
  have w13 : memLoad32 n13.mem efuseRd = memLoad32 n.mem efuseRd ||| X1 := by
    rw [hm13.field, hX1, hI8.field]
  have O13 : EfOut Mb n13.mem := hO.trans (hI8.out.trans (hO10.trans hm13.out))
  -- `efuse_program_run(0x5AA5, 1)` reloads the read registers when the program run returned nonzero
  have mid : ∃ n14, Steps n13 n14 ∧ St n14.mem BT n14 0x13E (reg n14) ∧ EfOut n13.mem n14.mem ∧
      (∃ X, memLoad32 n14.mem efuseRd = memLoad32 n13.mem efuseRd ||| X) ∧
      ∀ r, rsK r → reg n14 r = reg n13 r := by
    by_cases h0 : reg n10 a0 = 0
    · obtain ⟨n14, d14, u14⟩ := t13.taken hc13 0x13E bt_at_130 (by decide) (by
        show (reg n13 a0 == reg n13 x0) = true; rw [v13a0, h0, t13.zero]; rfl)
      exact ⟨n14, .single d14, ⟨u14.pc, rfl, fun _ => rfl⟩, by rw [u14.mem]; exact EfOut.refl _,
        ⟨0, by rw [u14.mem]; exact BitVec.or_zero.symm⟩, fun r _ => by rw [u14.regs]⟩
    · obtain ⟨n14, d14, u14⟩ := t13.notTaken hc13 0x132 bt_at_130 (by decide) (by
        show (reg n13 a0 == reg n13 x0) = false; rw [v13a0, t13.zero]; exact beq_false_of_ne h0)
      obtain ⟨n15, d15, u15⟩ := u14.aluImm hc13 bt_at_132 (off' := 0x134) (by decide)
      obtain ⟨n16, d16, u16⟩ := u15.alu hc13 bt_at_134 (off' := 0x136) (by decide)
      obtain ⟨n17, c17, pc17, mem17, regs17⟩ := u16.self.callRa (cb := EPR) hc13 bt_at_136 bt_at_13a
        (by decide) (by decide)
      obtain ⟨ec2, hce2, -, hF2⟩ := E.epr.out O13
      obtain ⟨n18, c18, pc18, k18, hO18, X2, hX2⟩ := hF2.run n17 (by rw [mem17]; exact hce2) pc17
        (Or.inl (by
          rw [regs17, updz u16.self.zero (by decide), u16.regs]
          simp +decide only [upd, ↓reduceIte]
          rw [show reg n13 x0 = 0 from t13.zero]; rfl))
      rw [mem17] at hO18 hX2
      refine ⟨n18, .cons d14 (.cons d15 (.cons d16 (c17.trans c18))), ⟨by
        rw [pc18, regs17]; simp +decide only [upd, ↓reduceIte], rfl, fun _ => rfl⟩, hO18, ⟨X2, hX2⟩,
        fun r hr => ?_⟩
      have h := nk r hr
      rw [k18 r (fun e => h (by rw [e]; decide)) (fun e => h (by rw [e]; decide))
        (fun e => h (by rw [e]; decide)) (fun e => h (by rw [e]; decide))
        (fun e => h (by rw [e]; decide)) (fun e => h (by rw [e]; decide)),
        regs17, updz u16.self.zero (fun e => h (by rw [e]; decide)), u16.regs,
        updz (by simp [upd]) (fun e => h (by rw [e]; decide)), updz t13.zero (fun e => h (by rw [e]; decide))]
  obtain ⟨n14, c14, t14, O14, ⟨X2, hX2⟩, q14⟩ := mid
  have hc14 : CodeIn n14.mem BT bootFnCode := O14.code hc13 (by decide)
  have Q : ∀ r, rsK r → reg n14 r = reg n r := fun r hr => by rw [q14 r hr, q13 r hr]
  -- the read-back check
  obtain ⟨n15, c15, t15, q15, h8'⟩ := rs_chk hk t14 hc14 (by rw [Q 9 (by decide), h9])
    (by rw [Q 8 (by decide), R.r8]) (by rw [Q 26 (by decide), h26])
  have m15 : n15.mem = n14.mem := t15.mem
  have K : ∀ r, rsK r → r ≠ 8 → reg n15 r = reg n r := fun r hr h8 => by rw [q15 r hr h8, Q r hr]
  have RR : ∀ k', reg n15 8 = BitVec.ofNat 32 k' → RsRegs (reg n15) k' target := fun k' e =>
    ⟨e, by rw [K 9 (by decide) (by decide), h9], by rw [K 19 (by decide) (by decide), R.r19],
      by rw [K 22 (by decide) (by decide), R.r22], by rw [K 23 (by decide) (by decide), R.r23],
      by rw [K 24 (by decide) (by decide), R.r24], by rw [K 25 (by decide) (by decide), R.r25]⟩
  refine ⟨n15, c1.trans (c2.trans (.cons d3 (c4.trans (c5.trans (.cons d6 (c7.trans (c8.trans (c9.trans
    (c10.trans (c11.trans (.cons d12 (c13.trans (c14.trans c15))))))))))))),
    ⟨t15.pc, rfl, fun _ => rfl⟩, by rw [m15]; exact O13.trans O14,
    ⟨X1 ||| X2, by rw [m15, hX2, w13, BitVec.or_assoc]⟩, ?_,
    fun r hr => K r (by revert hr; revert r; decide) (by revert hr; revert r; decide)⟩
  rcases h8' with e | ⟨e, hne⟩
  · exact Or.inl (RR _ e)
  · exact Or.inr ⟨by rw [m15]; exact hne, RR 0 e⟩

/-- An attempt from 0x6A: when the eFuse level that `btPop` counts reaches
the target, `boot` leaves for the cache setup at 0x156 with memory
unchanged. Otherwise the fourth attempt halts, and an earlier one halts or
returns to 0x6A, with memory outside the eFuse controller's registers
unchanged, the level word only gaining bits, and the attempt count one
higher or, when the level word changed, 0. -/
theorem rs_iter {Mb : Word → BitVec 8} (E : RsEnv Mb) {target : Word} (k : Nat) (hk : k ≤ 3)
    {n : Machine} (s : St n.mem BT n 0x6A (reg n)) (hO : EfOut Mb n.mem) (R : RsRegs (reg n) k target)
    (hR : Room (reg n sp) 16) :
    (∃ n', Steps n n' ∧ St n.mem BT n' 0x156 (reg n') ∧
      (btPop (memLoad32 n.mem efuseRd)).ult target = false ∧
      ∀ r, r ∈ ([2, 20, 22] : List (Fin 32)) → reg n' r = reg n r) ∨
    (∃ n', Steps n n' ∧ St n'.mem BT n' 0x6A (reg n') ∧ EfOut Mb n'.mem ∧
      (∃ X, memLoad32 n'.mem efuseRd = memLoad32 n.mem efuseRd ||| X) ∧
      ((k + 1 ≤ 3 ∧ RsRegs (reg n') (k + 1) target) ∨
        (memLoad32 n'.mem efuseRd ≠ memLoad32 n.mem efuseRd ∧ RsRegs (reg n') 0 target)) ∧
      ∀ r, r ∈ ([2, 20] : List (Fin 32)) → reg n' r = reg n r) ∨
    HaltsWith n 0xE1 := by
  have hc := hO.code E.code (by decide)
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block rsHead hc rsHead_end
    ⟨by show (reg n 9 + 0xFFFFF83C).toNat % 4 = 0; rw [R.r9]; decide, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have v1a1 : reg n1 a1 = btPop (memLoad32 n.mem efuseRd) := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, rsHead, upd, ↓reduceIte]
    rw [R.r9, R.r24, R.r25]; rfl
  have v1a0 : reg n1 a0 = aluEval .srl (memLoad32 n.mem efuseRd) 0xE := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, rsHead, upd, ↓reduceIte]; rw [R.r9]; rfl
  have q1 : ∀ r, rsK r → reg n1 r = reg n r := fun r hr => by
    rw [u1.regs, rs_keep _ _ hz (by simp only [rsHead]; revert hr; revert r; decide)]
  have t1 : St n.mem BT n1 0x9A (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  by_cases hlt : (btPop (memLoad32 n.mem efuseRd)).ult target = true
  · obtain ⟨n2, d2, u2⟩ := t1.notTaken hc 0x9E bt_at_9a (by decide) (by
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
    have v3a0 : reg n3 a0 = aluEval .srl (memLoad32 n.mem efuseRd) 0xE := by
      rw [u3.regs, rs_keep _ _ hz2 (by decide), u2.regs, v1a0]
    have halt : ∀ n' : Machine, Steps n n' → St n.mem BT n' 0x29C (reg n') → reg n' sp = reg n sp →
        HaltsWith n 0xE1 :=
      fun n' c t hsp => HaltsWith.of_steps c (rs_halt ⟨t.pc, rfl, fun _ => rfl⟩ (by rw [t.mem]; exact hc)
        (by rw [t.mem]; exact hO.panic E.panic) (by rw [hsp]; exact hR))
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
      have v5 : reg n5 26 = aluEval .and (aluEval .add (aluEval .srl (memLoad32 n.mem efuseRd) 0xE) 0x1)
          (aluEval .xor (aluEval .srl (memLoad32 n.mem efuseRd) 0xE) 0xFFFFFFFF) := by
        rw [u5.regs]; simp +decide only [runBlock, BInstr.run, rsBit, upd, ↓reduceIte]; rw [u4.regs, v3a0]
      have c4 : Steps n n4 := c1.trans (.cons d2 (c3.trans (.single d4)))
      by_cases h0 : (reg n5 a0 == reg n5 x0) = true
      · obtain ⟨n6, d6, u6⟩ := t5.taken hc 0x29C bt_at_b6 (by decide) h0
        exact Or.inr (Or.inr (halt n6 (c4.trans (c5.trans (.single d6))) ⟨u6.pc, u6.mem, fun _ => rfl⟩
          (by rw [u6.regs, q5 sp (by decide) (by decide)])))
      · obtain ⟨n6, d6, u6⟩ := t5.notTaken hc 0xBA bt_at_b6 (by decide) (by
          simp only [Bool.not_eq_true] at h0; exact h0)
        have m6 : n6.mem = n.mem := u6.mem
        have q6 : ∀ r, rsK r → r ≠ 26 → reg n6 r = reg n r := fun r hr h26 => by rw [u6.regs, q5 r hr h26]
        obtain ⟨n7, c7, t7, O7, W7, RR7, K7⟩ := rs_tail E k hk3 (n := n6) ⟨u6.pc, rfl, fun _ => rfl⟩
          (by rw [m6]; exact hO)
          ⟨by rw [q6 8 (by decide) (by decide), R.r8], by rw [q6 9 (by decide) (by decide), R.r9],
            by rw [q6 19 (by decide) (by decide), R.r19], by rw [q6 22 (by decide) (by decide), R.r22],
            by rw [q6 23 (by decide) (by decide), R.r23], by rw [q6 24 (by decide) (by decide), R.r24],
            by rw [q6 25 (by decide) (by decide), R.r25]⟩
          (by rw [u6.regs, v5, m6])
        rw [m6] at W7 RR7
        exact Or.inr (Or.inl ⟨n7, c4.trans (c5.trans (.cons d6 c7)), t7, O7, W7,
          RR7.imp (fun h => ⟨by omega, h⟩) id,
          fun r hr => by rw [K7 r hr, q6 r (by revert hr; revert r; decide) (by revert hr; revert r; decide)]⟩)
    · obtain ⟨n4, d4, u4⟩ := t3.taken hc 0x29C bt_at_a4 (by decide) (by
        show (reg n3 a2).ult (reg n3 a1) = true; rw [v3a2, v3a1, show k = 3 by omega]; decide)
      exact Or.inr (Or.inr (halt n4 (c1.trans (.cons d2 (c3.trans (.single d4)))) ⟨u4.pc, u4.mem, fun _ => rfl⟩
        (by rw [u4.regs, q3 sp (by decide)])))
  · have hge : (btPop (memLoad32 n.mem efuseRd)).ult target = false := by simpa using hlt
    obtain ⟨n2, d2, u2⟩ := t1.taken hc 0x156 bt_at_9a (by decide) (by
      show (!(reg n1 a1).ult (reg n1 22)) = true; rw [v1a1, q1 22 (by decide), R.r22, hge]; rfl)
    exact Or.inl ⟨n2, c1.trans (.single d2), ⟨u2.pc, u2.mem, fun _ => rfl⟩, hge,
      fun r hr => by rw [u2.regs, q1 r (by revert hr; revert r; decide)]⟩

/-- `boot`'s attempt loop from 0x6A, by induction on a bound `N` on the
measure `4 * (2^32 - w) + (3 - k)` for the level word `w` and the attempt
count `k`: every pass that returns to 0x6A raises `k` or raises `w`, which
only gains bits. The loop reaches 0x156 with the level at least the target,
or halts. -/
theorem rs_loop {Mb : Word → BitVec 8} (E : RsEnv Mb) {target : Word} :
    ∀ N k {n : Machine}, k ≤ 3 → 4 * (0x100000000 - (memLoad32 n.mem efuseRd).toNat) + (3 - k) < N →
      St n.mem BT n 0x6A (reg n) → EfOut Mb n.mem → RsRegs (reg n) k target → Room (reg n sp) 16 →
      (∃ n', Steps n n' ∧ St n'.mem BT n' 0x156 (reg n') ∧ EfOut Mb n'.mem ∧
        (btPop (memLoad32 n'.mem efuseRd)).ult target = false ∧
        (∃ X, memLoad32 n'.mem efuseRd = memLoad32 n.mem efuseRd ||| X) ∧
        ∀ r, r ∈ ([2, 20, 22] : List (Fin 32)) → reg n' r = reg n r) ∨ HaltsWith n 0xE1
  | 0, _, _, _, hN, _, _, _, _ => absurd hN (Nat.not_lt_zero _)
  | N + 1, k, n, hk, hN, s, hO, R, hR => by
    rcases rs_iter E k hk s hO R hR with ⟨n', c, s', hge, K⟩ | ⟨n', c, s', hO', ⟨X, hX⟩, RR, K⟩ | hp
    · have m' : n'.mem = n.mem := s'.mem
      exact Or.inl ⟨n', c, ⟨s'.pc, rfl, fun _ => rfl⟩, by rw [m']; exact hO, by rw [m']; exact hge,
        ⟨0, by rw [m']; exact BitVec.or_zero.symm⟩, K⟩
    · have hle : (memLoad32 n.mem efuseRd).toNat ≤ (memLoad32 n'.mem efuseRd).toNat := by
        rw [hX, BitVec.toNat_or]; exact Nat.left_le_or
      have hw' := (memLoad32 n'.mem efuseRd).isLt
      obtain ⟨k', hk', R', hN'⟩ : ∃ k', k' ≤ 3 ∧ RsRegs (reg n') k' target ∧
          4 * (0x100000000 - (memLoad32 n'.mem efuseRd).toNat) + (3 - k') < N := by
        rcases RR with ⟨h3, R'⟩ | ⟨hne, R'⟩
        · exact ⟨k + 1, h3, R', by omega⟩
        · have hlt : (memLoad32 n.mem efuseRd).toNat < (memLoad32 n'.mem efuseRd).toNat :=
            Nat.lt_of_le_of_ne hle fun h => hne (BitVec.eq_of_toNat_eq h).symm
          exact ⟨0, by omega, R', by omega⟩
      have sp' : reg n' sp = reg n sp := K 2 (by decide)
      rcases rs_loop E N k' hk' hN' s' hO' R' (by rw [sp']; exact hR) with
        ⟨n'', c', s'', hO'', hge, ⟨Y, hY⟩, K'⟩ | hp
      · refine Or.inl ⟨n'', c.trans c', s'', hO'', hge, ⟨X ||| Y, by rw [hY, hX, BitVec.or_assoc]⟩,
          fun r hr => ?_⟩
        rw [K' r hr]
        rcases (show r = 2 ∨ r = 20 ∨ r = 22 by revert hr; revert r; decide) with rfl | rfl | rfl
        · exact K 2 (by decide)
        · exact K 20 (by decide)
        · rw [R'.r22, R.r22]
      · exact Or.inr (HaltsWith.of_steps c hp)
    · exact Or.inr hp

/-- `boot`'s raise of the security level, from 0x3E: `boot` reaches the
cache setup at 0x156 when the eFuse level that `btPop` reads reaches
`target`, with memory outside the eFuse controller's registers unchanged
and the level word its old value with some bits set; otherwise it halts. -/
theorem rs_raise {n : Machine} (E : RsEnv n.mem) {target : Word} (s : St n.mem BT n 0x3E (reg n))
    (h9 : reg n 9 = 0x60009000) (h22 : reg n 22 = target) (hR : Room (reg n sp) 16) :
    (∃ n', Steps n n' ∧ St n'.mem BT n' 0x156 (reg n') ∧ EfOut n.mem n'.mem ∧
      (btPop (memLoad32 n'.mem efuseRd)).ult target = false ∧
      (∃ X, memLoad32 n'.mem efuseRd = memLoad32 n.mem efuseRd ||| X) ∧
      ∀ r, r ∈ ([2, 20, 22] : List (Fin 32)) → reg n' r = reg n r) ∨ HaltsWith n 0xE1 := by
  have hc := E.code
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block rsInit hc rsInit_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial, trivial⟩
  have t1 : St n1.mem BT n1 0x6A (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n.mem := u1.mem
  have rv : ∀ r : Fin 32, reg n1 r = (runBlock rsInit (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  have q1 : ∀ r, r ∈ ([2, 9, 20, 22] : List (Fin 32)) → reg n1 r = reg n r := fun r hr => by
    rw [rv, rs_keep _ _ hz (by simp only [rsInit]; revert hr; revert r; decide)]
  have R1 : RsRegs (reg n1) 0 target := by
    refine ⟨?_, by rw [q1 9 (by decide), h9], ?_, by rw [q1 22 (by decide), h22], ?_, ?_, ?_⟩ <;>
      rw [rv] <;> simp +decide only [runBlock, BInstr.run, rsInit, upd, ↓reduceIte] <;>
      (try rw [show reg n x0 = 0 from hz]) <;> (try rw [h9]) <;> rfl
  have hw := (memLoad32 n1.mem efuseRd).isLt
  rcases rs_loop E (4 * 0x100000000 + 4) 0 (by decide) (by omega) t1 (by rw [m1]; exact EfOut.refl _) R1
      (by rw [q1 sp (by decide)]; exact hR) with ⟨n', c', s', hO', hge, ⟨X, hX⟩, K'⟩ | hp
  · rw [m1] at hX
    exact Or.inl ⟨n', c1.trans c', s', hO', hge, ⟨X, hX⟩,
      fun r hr => by rw [K' r hr, q1 r (by revert hr; revert r; decide)]⟩
  · exact Or.inr (HaltsWith.of_steps c1 hp)

end C3.RV32.Cur
