import C3BootProofs.Proofs.BootRaise

/-!
# `c3_bootloader::boot`

`boot_correct` covers the compiled `boot` from entry to the jump into the
application, given the ROM contracts `RomRead` (flash reads) and `RomFn`
(the log and the three cache routines it calls). `bt_body` covers the part
from the segment count at 0x18C, after `boot` raises the security level
and locks the eFuse and flash registers.
-/

namespace C3.RV32.Cur

open C3.Image

def btPs : List (Fin 32 × Word) :=
  [(ra, 0x3C), (8, 0x38), (9, 0x34), (18, 0x30), (19, 0x2C), (20, 0x28), (21, 0x24), (22, 0x20), (23, 0x1C),
   (24, 0x18), (25, 0x14), (26, 0x10), (27, 0xC)]

def btPro : List BInstr :=
  [.sw sp ra 0x3C, .sw sp 8 0x38, .sw sp 9 0x34, .sw sp 18 0x30, .sw sp 19 0x2C, .sw sp 20 0x28,
   .sw sp 21 0x24, .sw sp 22 0x20, .sw sp 23 0x1C, .sw sp 24 0x18, .sw sp 25 0x14, .sw sp 26 0x10,
   .sw sp 27 0xC]

theorem btPro_eq : btPro = saveBlock btPs := rfl

theorem btPro_end : blockEnd bootFnCode 0x2 btPro = some 0x1C :=
  (blockEnd_cons' (off' := 0x4) bt_at_2 rfl (blockEnd_cons' (off' := 0x6) bt_at_4 rfl (blockEnd_cons' (off' := 0x8) bt_at_6 rfl (blockEnd_cons' (off' := 0xA) bt_at_8 rfl (blockEnd_cons' (off' := 0xC) bt_at_a rfl (blockEnd_cons' (off' := 0xE) bt_at_c rfl (blockEnd_cons' (off' := 0x10) bt_at_e rfl (blockEnd_cons' (off' := 0x12) bt_at_10 rfl (blockEnd_cons' (off' := 0x14) bt_at_12 rfl (blockEnd_cons' (off' := 0x16) bt_at_14 rfl (blockEnd_cons' (off' := 0x18) bt_at_16 rfl (blockEnd_cons' (off' := 0x1A) bt_at_18 rfl (blockEnd_cons' (off' := 0x1C) bt_at_1a rfl rfl)))))))))))))

def btFr : List BInstr :=
  [.alu .add 20 x0 a2, .sw sp a1 0x8, .sw sp a0 0x4]

theorem btFr_end : blockEnd bootFnCode 0x1C btFr = some 0x22 :=
  (blockEnd_cons' (off' := 0x1E) bt_at_1c rfl (blockEnd_cons' (off' := 0x20) bt_at_1e rfl (blockEnd_cons' (off' := 0x22) bt_at_20 rfl rfl)))

def btRaise : List BInstr :=
  [.alu .add 22 x0 a3, .lui 9 0x60009000, .lui a0 0x3FCC6000, .aluImm .add a0 a0 0x6DF,
   .alu .add a1 x0 a3]

theorem btRaise_end : blockEnd bootFnCode 0x26 btRaise = some 0x36 :=
  (blockEnd_cons' (off' := 0x28) bt_at_26 rfl (blockEnd_cons' (off' := 0x2C) bt_at_28 rfl (blockEnd_cons' (off' := 0x30) bt_at_2c rfl (blockEnd_cons' (off' := 0x34) bt_at_30 rfl (blockEnd_cons' (off' := 0x36) bt_at_34 rfl rfl)))))

def btLk1 : List BInstr :=
  [.lui a1 0x18002000, .lui a0 0x600C1000, .aluImm .add a3 a1 0x200, .aluImm .add a1 x0 0x7,
   .sw a0 a3 0x110, .aluImm .add a2 a0 0x114, .aluImm .add a3 a3 0x200, .lw 23 sp 0x8]

theorem btLk1_end : blockEnd bootFnCode 0x156 btLk1 = some 0x172 :=
  (blockEnd_cons' (off' := 0x15A) bt_at_156 rfl (blockEnd_cons' (off' := 0x15E) bt_at_15a rfl (blockEnd_cons' (off' := 0x162) bt_at_15e rfl (blockEnd_cons' (off' := 0x164) bt_at_162 rfl (blockEnd_cons' (off' := 0x168) bt_at_164 rfl (blockEnd_cons' (off' := 0x16C) bt_at_168 rfl (blockEnd_cons' (off' := 0x170) bt_at_16c rfl (blockEnd_cons' (off' := 0x172) bt_at_170 rfl rfl))))))))

def btLk2 : List BInstr :=
  [.aluImm .add a3 a0 0x100, .lw a1 a3 0x8, .aluImm .and a1 a1 0xFFFFFFFC, .aluImm .add a1 a1 0x2,
   .aluImm .add a2 x0 0x1, .sw a3 a1 0x8, .sw a3 a2 0x4]

theorem btLk2_end : blockEnd bootFnCode 0x17C btLk2 = some 0x18C :=
  (blockEnd_cons' (off' := 0x180) bt_at_17c rfl (blockEnd_cons' (off' := 0x182) bt_at_180 rfl (blockEnd_cons' (off' := 0x184) bt_at_182 rfl (blockEnd_cons' (off' := 0x186) bt_at_184 rfl (blockEnd_cons' (off' := 0x188) bt_at_186 rfl (blockEnd_cons' (off' := 0x18A) bt_at_188 rfl (blockEnd_cons' (off' := 0x18C) bt_at_18a rfl rfl)))))))

def btCnt : List BInstr :=
  [.aluImm .add a2 x0 0x10, .aluImm .sltu a1 a0 0x11, .alu .add 22 x0 23]

theorem btCnt_end : blockEnd bootFnCode 0x190 btCnt = some 0x198 :=
  (blockEnd_cons' (off' := 0x192) bt_at_190 rfl (blockEnd_cons' (off' := 0x196) bt_at_192 rfl (blockEnd_cons' (off' := 0x198) bt_at_196 rfl rfl)))

def btSet : List BInstr :=
  [.alu .sub a1 x0 a1, .alu .and a0 a0 a1, .aluImm .sll 8 a0 0x4, .aluImm .add 19 x0 0x2,
   .alu .add 18 22 8, .lui 21 0xFF900000, .alu .add 9 x0 22]

theorem btSet_end : blockEnd bootFnCode 0x19E btSet = some 0x1B4 :=
  (blockEnd_cons' (off' := 0x1A2) bt_at_19e rfl (blockEnd_cons' (off' := 0x1A4) bt_at_1a2 rfl (blockEnd_cons' (off' := 0x1A8) bt_at_1a4 rfl (blockEnd_cons' (off' := 0x1AA) bt_at_1a8 rfl (blockEnd_cons' (off' := 0x1AE) bt_at_1aa rfl (blockEnd_cons' (off' := 0x1B2) bt_at_1ae rfl (blockEnd_cons' (off' := 0x1B4) bt_at_1b2 rfl rfl)))))))

def btSusp : List BInstr :=
  [.lui 8 0x600C5000, .aluImm .add 9 x0 0x80]

theorem btSusp_end : blockEnd bootFnCode 0x1E2 btSusp = some 0x1EA :=
  (blockEnd_cons' (off' := 0x1E6) bt_at_1e2 rfl (blockEnd_cons' (off' := 0x1EA) bt_at_1e6 rfl rfl))

def btInv0 : List BInstr :=
  [.alu .add 21 x0 a0, .aluImm .add a0 x0 0x100]

theorem btInv0_end : blockEnd bootFnCode 0x1F2 btInv0 = some 0x1F8 :=
  (blockEnd_cons' (off' := 0x1F4) bt_at_1f2 rfl (blockEnd_cons' (off' := 0x1F8) bt_at_1f4 rfl rfl))

def btMap0 : List BInstr :=
  [.aluImm .add a0 x0 0x2, .lui 9 0x600C5000, .aluImm .add a2 x0 0x7F]

theorem btMap0_end : blockEnd bootFnCode 0x202 btMap0 = some 0x20C :=
  (blockEnd_cons' (off' := 0x204) bt_at_202 rfl (blockEnd_cons' (off' := 0x208) bt_at_204 rfl (blockEnd_cons' (off' := 0x20C) bt_at_208 rfl rfl)))

def btBus : List BInstr :=
  [.lui a0 0x600C4000, .lw a1 a0 0x4, .aluImm .and a1 a1 0xFFFFFFFC, .sw a0 a1 0x4]

theorem btBus_end : blockEnd bootFnCode 0x25A btBus = some 0x264 :=
  (blockEnd_cons' (off' := 0x25E) bt_at_25a rfl (blockEnd_cons' (off' := 0x260) bt_at_25e rfl (blockEnd_cons' (off' := 0x262) bt_at_260 rfl (blockEnd_cons' (off' := 0x264) bt_at_262 rfl rfl))))

def btJmp : List BInstr :=
  [.lw 8 23 0x100, .lui a0 0x3FCC6000, .aluImm .add a0 a0 0x696, .alu .add a1 x0 8]

theorem btJmp_end : blockEnd bootFnCode 0x276 btJmp = some 0x284 :=
  (blockEnd_cons' (off' := 0x27A) bt_at_276 rfl (blockEnd_cons' (off' := 0x27E) bt_at_27a rfl (blockEnd_cons' (off' := 0x282) bt_at_27e rfl (blockEnd_cons' (off' := 0x284) bt_at_282 rfl rfl))))

/-- A call from `boot` to a ROM routine, with the stack pointer at `S`. -/
theorem bt_romcall {romBase : Word} {romCode : List Nat} {romStack : Nat} (F : Word) {n : Machine}
    {g : Fin 32 → Word} {off : Nat} {imm o S : Word}
    (hF : RomFn romBase romCode F romStack fun _ => True) (s : St n.mem BT n off g) (hgs : g sp = S)
    (hc : CodeIn n.mem BT bootFnCode) (hr : CodeIn n.mem romBase romCode) (hS : romStack ≤ S.toNat)
    (h1 : fetchRel bootFnCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootFnCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : BT + BitVec.ofNat 32 off + imm + o = F) (he : F.toNat % 2 = 0)
    (he8 : (BT + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem BT n' (off + 8) (reg n') ∧
      (∀ x, Sep (S - BitVec.ofNat 32 romStack) romStack x 1 → n'.mem x = n.mem x) ∧
      ∀ q, romKeep q = true → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb he
  have sp1 : reg n1 sp = S := by rw [regs1, updz s.zero (by decide)]; exact hgs
  obtain ⟨n2, c2, pc2, keep2, mem2⟩ := hF n1 (by rw [mem1]; exact hr) pc1 trivial (by rw [sp1]; exact hS)
  refine ⟨n2, c1.trans c2, ⟨?_, rfl, fun _ => rfl⟩, fun x hx => by rw [mem2 x (by rw [sp1]; exact hx), mem1],
    fun q hq => ?_⟩
  · rw [pc2, regs1]; simp +decide only [upd, ite_true, ite_false]; exact even_clear _ he8
  · rw [keep2 q hq, regs1]; exact updz s.zero (by rintro rfl; exact absurd hq (by decide))

/-- `M'` agrees with `M` outside the peripheral registers from 0x60008A00
to 0x600C3FFF. -/
def BtW (M M' : Word → BitVec 8) : Prop :=
  ∀ x : Word, (x.toNat < 0x60008A00 ∨ 0x600C4000 ≤ x.toNat) → M' x = M x

theorem BtW.refl (M : Word → BitVec 8) : BtW M M := fun _ _ => rfl

theorem BtW.trans {M0 M1 M2 : Word → BitVec 8} (h1 : BtW M0 M1) (h2 : BtW M1 M2) : BtW M0 M2 :=
  fun x hx => (h2 x hx).trans (h1 x hx)

theorem BtW.store {M M' : Word → BitVec 8} (h : BtW M M') {a : Word} (v : Word) (h1 : 0x60008A00 ≤ a.toNat)
    (h2 : a.toNat + 4 ≤ 0x600C4000) : BtW M (memStore32 M' a v) := fun x hx => by
  have hs : Sep a 4 x 1 := by
    rcases hx with hx | hx
    · exact (sep_of_le (by omega) (by omega)).symm
    · exact sep_of_le (by omega) (by have := x.isLt; omega)
  rw [memStore32_get_sep hs]; exact h x hx

/-- `boot`'s loop at 0x174 that writes `v` to `k` words of the flash
controller's registers from `p`. -/
theorem bt_lock (v : Word) :
    ∀ k {n : Machine} (p : Word), St n.mem BT n 0x174 (reg n) → 0 < k → reg n a1 = BitVec.ofNat 32 k →
      reg n a2 = p → reg n a3 = v → p.toNat % 4 = 0 → 0x60008A00 ≤ p.toNat → p.toNat + 4 * k ≤ 0x600C4000 →
      CodeIn n.mem BT bootFnCode →
      ∃ n', Steps n n' ∧ St n'.mem BT n' 0x17C (reg n') ∧ BtW n.mem n'.mem ∧
        ∀ r, r ≠ a1 → r ≠ a2 → reg n' r = reg n r
  | 0, _, _, _, hk, _, _, _, _, _, _, _ => absurd hk (by decide)
  | k + 1, n, p, s, _, h1, hp, h3, hal, hlo, hhi, hc => by
    have hz := s.zero
    obtain ⟨n1, d1, u1⟩ := s.sw hc bt_at_174 (off' := 0x176) (by decide) (by rw [hp, add_lit_zero]; exact hal)
    rw [hp, add_lit_zero, h3] at u1
    have hm1 : BtW n.mem n1.mem := by rw [u1.mem]; exact (BtW.refl _).store _ hlo (by omega)
    have hc1 : CodeIn n1.mem BT bootFnCode := by rw [u1.mem]; exact hc.store32 (rs_sep _ (by omega) (by omega))
    have t1 : St n1.mem BT n1 0x176 (reg n) := ⟨u1.pc, rfl, u1.regs⟩
    obtain ⟨n3, d3, u3⟩ := t1.aluImm hc1 bt_at_176 (off' := 0x178) (by decide)
    obtain ⟨n4, d4, u4⟩ := u3.aluImm hc1 bt_at_178 (off' := 0x17A) (by decide)
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
      obtain ⟨n5, d5, u5⟩ := u4.notTaken hc1 0x17C bt_at_17a (by decide) (by
        show ((_ : Word) != _) = false
        simp +decide only [upd, ↓reduceIte])
      refine ⟨n5, .cons d1 (.cons d3 (.cons d4 (.single d5))), ⟨u5.pc, rfl, fun _ => rfl⟩, ?_,
        fun r ha hb => by rw [u5.regs, q4 r ha hb]⟩
      rw [u5.mem]; exact hm1
    · obtain ⟨n5, d5, u5⟩ := u4.taken hc1 0x174 bt_at_17a (by decide) (by
        show ((_ : Word) != _) = true
        simp +decide only [upd, ↓reduceIte]
        exact bne_iff_ne.mpr fun h => by
          have := congrArg BitVec.toNat h
          rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this; omega)
      have a2v : upd (upd (reg n) a2 (aluEval .add (reg n a2) 0x4)) a1 (BitVec.ofNat 32 k) a2 = p + 4 := by
        simp +decide only [upd, ↓reduceIte]; rw [hp]; rfl
      obtain ⟨n6, c6, t6, hm6, k6⟩ := bt_lock v k (n := n5) (p + 4)
        ⟨u5.pc, by rw [u5.mem], fun _ => rfl⟩ hkp
        (by rw [u5.regs]; simp +decide only [upd, ↓reduceIte])
        (by rw [u5.regs, a2v]) (by rw [u5.regs, q4 a3 (by decide) (by decide), h3])
        (by rw [rs_p4 p (by omega)]; omega) (by rw [rs_p4 p (by omega)]; omega)
        (by rw [rs_p4 p (by omega)]; omega) (by rw [u5.mem]; exact hc1)
      refine ⟨n6, .cons d1 (.cons d3 (.cons d4 (.cons d5 c6))), t6, ?_,
        fun r ha hb => by rw [k6 r ha hb, u5.regs, q4 r ha hb]⟩
      have : n5.mem = n1.mem := u5.mem
      rw [this] at hm6; exact hm1.trans hm6

/-- `bootMem` keeps memory from the ROM at 0x40000000 to the cache
controller at 0x600C4000: `boot` copies RAM segments below 0x40000000 and
writes only the cache controller's registers above. -/
theorem bt_bootMem_hi {flash : Nat → BitVec 8} {M : Word → BitVec 8} {top acc imgf romBase : Word}
    {R romStack : Nat} {romCode : List Nat} (C : BtCtx M top acc imgf R romStack romBase romCode) (x : Word)
    (h1 : 0x40000000 ≤ x.toNat) (h2 : x.toNat < 0x600C4000) : bootMem flash M acc imgf x = M x := by
  unfold bootMem busOn
  rw [st32_low (a := icacheCtrl1) _ _ (by decide) (by decide) h2, mmuMap_low _ x h2]
  unfold mmuInv
  rw [if_neg (by rw [BitVec.toNat_sub, show mmuBase.toNat = 0x600C5000 from rfl]; omega)]
  exact ramLoad_out x _ fun i hi hk => sep_hi (C.ram i hi hk).2.1 h1

/-- The segment table pointer `P0` is the header `acc` when the segment count
`cw` is at most 16. A definition, so that `omega` doesn't case-split on it. -/
def BtClamp (cw P0 acc : Word) : Prop := cw.toNat ≤ 16 → P0 = acc

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 20000 in
/-- `boot` from the segment count at 0x18C to the jump into the
application, with memory `M0` there, the header at `acc` in register 23,
the image's flash offset in register 20, and the slot in the frame at
`top - 0x3C`: it jumps to the entry point with the slot in `a0`, with the
memory outside its stack as `bootMem` says, or halts with code 0xE2 when a
flash read fails. -/
theorem bt_body {flash : Nat → BitVec 8} {R romStack : Nat} {romBase : Word} {romCode : List Nat}
    {M0 : Word → BitVec 8} {top acc imgf slot : Word}
    (C : BtCtx M0 top acc imgf R romStack romBase romCode) (hROM : RomRead flash R romBase romCode)
    (log : RomFn romBase romCode 0x40000040 romStack fun _ => True)
    (suspend : RomFn romBase romCode 0x40000524 romStack fun _ => True)
    (invalidate : RomFn romBase romCode 0x400004D8 romStack fun _ => True)
    (resume : RomFn romBase romCode 0x40000528 romStack fun _ => True)
    {n5 : Machine} (t5 : St M0 BT n5 0x18C (reg n5)) (sp5 : reg n5 sp = top + 0xFFFFFFC0)
    (w23 : reg n5 23 = acc) (w20 : reg n5 20 = imgf) (hslot : memLoad32 M0 (top + 0xFFFFFFC0 + 4) = slot) :
    (∃ m', Steps n5 m' ∧ m'.pc = memLoad32 M0 (acc + 0x100) &&& ~~~1 ∧ reg m' a0 = slot ∧
      ∀ x, Sep (top - BitVec.ofNat 32 (btK R romStack)) (btK R romStack) x 1 →
        m'.mem x = bootMem flash M0 acc imgf x) ∨ HaltsWith n5 0xE2 := by
  have hKv : btK R romStack = 0x40 + 16 + R + romStack := rfl
  have hspl := C.hspl; have hsph := C.hsph; have h16 := C.hsp; have hR4 := C.hR
  rw [hKv] at hspl; unfold dramEnd at hsph
  obtain ⟨Ss, hSs⟩ : ∃ Ss, top - BitVec.ofNat 32 (btK R romStack) = Ss := ⟨_, rfl⟩
  rw [hSs]
  have sAS := C.sAS; rw [hSs] at sAS
  have hSn : Ss.toNat = top.toNat - btK R romStack := by
    rw [← hSs, BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]; omega
  have hsp1 : (top + 0xFFFFFFC0).toNat = top.toNat - 0x40 := by
    rw [BitVec.toNat_add, show (0xFFFFFFC0 : Word).toNat = 2 ^ 32 - 0x40 from rfl]; omega
  have hRS : (top + 0xFFFFFFC0 - BitVec.ofNat 32 romStack).toNat = top.toNat - 0x40 - romStack := by
    rw [BitVec.toNat_sub, hsp1, BitVec.toNat_ofNat]; omega
  have romS : ∀ x, Sep Ss (btK R romStack) x 1 → Sep (top + 0xFFFFFFC0 - BitVec.ofNat 32 romStack) romStack x 1 :=
    fun x hx => by
      have e : top + 0xFFFFFFC0 - BitVec.ofNat 32 romStack = Ss + BitVec.ofNat 32 (16 + R) :=
        BitVec.eq_of_toNat_eq (by
          rw [hRS, BitVec.toNat_add Ss, BitVec.toNat_ofNat, hSn, hKv]; omega)
      rw [e]; exact hx.sub (by rw [hKv]; omega)
  have stkHi : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep Ss (btK R romStack) x 1 := fun x hx =>
    sep_of_le (by rw [hSn, hKv]; omega) (by have := x.isLt; omega)
  have tbl : ∀ i, i < 0x10C → Sep Ss (btK R romStack) (acc + BitVec.ofNat 32 i) 1 := fun i hi =>
    (sAS.sub (c := i) (l := 1) (by omega)).symm
  -- the frame word that holds the slot
  have hF4 : ∀ j, j < 4 → (top + 0xFFFFFFC0 + 4 + BitVec.ofNat 32 j).toNat = top.toNat - 0x3C + j := fun j hj => by
    rw [BitVec.toNat_add, BitVec.toNat_add, hsp1, BitVec.toNat_ofNat, show (4 : Word).toNat = 4 from rfl]; omega
  have frS : ∀ j, j < 4 →
      Sep (top + 0xFFFFFFC0 - BitVec.ofNat 32 romStack) romStack (top + 0xFFFFFFC0 + 4 + BitVec.ofNat 32 j) 1 :=
    fun j hj => sep_of_le (by rw [hRS, hF4 j hj]; omega) (by rw [hF4 j hj]; omega)
  have frLo : ∀ j, j < 4 → (top + 0xFFFFFFC0 + 4 + BitVec.ofNat 32 j).toNat < 0x40000000 := fun j hj => by
    rw [hF4 j hj]; omega
  -- a call to a ROM routine that keeps memory outside its stack
  have romcall : ∀ (F : Word) (n : Machine) (g : Fin 32 → Word) (off : Nat) (imm o : Word),
      RomFn romBase romCode F romStack (fun _ => True) → St n.mem BT n off g → g sp = top + 0xFFFFFFC0 →
      BtHi M0 n.mem →
      fetchRel bootFnCode off = some (.auipc ra imm, 4) → fetchRel bootFnCode (off + 4) = some (.jalr ra ra o, 4) →
      BT + BitVec.ofNat 32 off + imm + o = F → F.toNat % 2 = 0 → (BT + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0 →
      ∃ n', Steps n n' ∧ St n'.mem BT n' (off + 8) (reg n') ∧
        (∀ x, Sep Ss (btK R romStack) x 1 → n'.mem x = n.mem x) ∧ BtHi M0 n'.mem ∧
        memLoad32 n'.mem (top + 0xFFFFFFC0 + 4) = memLoad32 n.mem (top + 0xFFFFFFC0 + 4) ∧
        ∀ q, romKeep q = true → reg n' q = g q := by
    intro F n g off imm o hF s hgs hH h1 h2 hb he he8
    obtain ⟨n', c', t', o', k'⟩ := bt_romcall F hF s hgs (hiKeep C.code hH (by decide) (by decide))
      (hiKeep C.rom hH C.hrb C.hrl) (by rw [hsp1]; omega) h1 h2 hb he he8
    exact ⟨n', c', t', fun x hx => o' x (romS x hx),
      fun x h1 h2 => by rw [o' x (romS x (stkHi x h1))]; exact hH x h1 h2,
      memLoad32_congr fun j hj => o' _ (frS j hj), k'⟩
  have hacc := C.hacc; have haccl := C.haccl
  have hc5 := C.code
  -- the segment count
  obtain ⟨cw, hcw⟩ : ∃ cw, memLoad32 M0 (acc + 0x108) = cw := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, sgCount M0 acc = N := ⟨_, rfl⟩
  have hNv : N = if cw.toNat ≤ 16 then cw.toNat else 0 := by rw [← hN, ← hcw]; rfl
  have hN16 : N ≤ 16 := by rw [← hN]; exact sgCount_le M0 acc
  obtain ⟨n6, d6, u6⟩ := t5.lw hc5 bt_at_18c (off' := 0x190) (by decide)
    (by rw [w23, BitVec.toNat_add]; simp; omega)
  have t6 := u6.self
  have v0 : reg n6 a0 = cw := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]; rw [w23]; exact hcw
  have k6 : ∀ r, r ≠ a0 → reg n6 r = reg n5 r := fun r h => by rw [u6.regs]; exact updz t5.zero h
  obtain ⟨n7, c7, u7⟩ := t6.block btCnt hc5 btCnt_end ⟨trivial, trivial, trivial, trivial⟩
  have t7 : St M0 BT n7 0x198 (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
  have r7 : ∀ r, reg n7 r = (runBlock btCnt (M0, reg n6)).2 r := fun r => by rw [u7.regs]
  have e2 : reg n7 a2 = 16 := by rw [r7]; simp +decide only [runBlock, BInstr.run, btCnt, upd, ↓reduceIte]; rw [t6.zero]; rfl
  have e0 : reg n7 a0 = cw := by rw [r7, runBlock_reg _ _ _ a0 t6.zero (by decide)]; exact v0
  have e1 : reg n7 a1 = aluEval .sltu cw 0x11 := by
    rw [r7]; simp +decide only [runBlock, BInstr.run, btCnt, upd, ↓reduceIte]; rw [v0]
  have e22 : reg n7 22 = acc := by
    rw [r7]; simp +decide only [runBlock, BInstr.run, btCnt, upd, ↓reduceIte]
    rw [k6 23 (by decide), w23]; exact BitVec.zero_add _
  have k7 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ 22 → reg n7 r = reg n5 r := fun r h0 h1 h2 h22 => by
    rw [r7, runBlock_reg _ _ _ r t6.zero (by simp only [btCnt]; revert h1 h2 h22; revert r; decide), k6 r h0]
  -- the clamp: `P0` is the header when the count is at most 16
  obtain ⟨n8, c8, t8, P0, y22, hP0, k8⟩ : ∃ n8, Steps n7 n8 ∧ St M0 BT n8 0x19E (reg n8) ∧ ∃ P0,
      reg n8 22 = P0 ∧ BtClamp cw P0 acc ∧ ∀ r, r ≠ 22 → reg n8 r = reg n7 r := by
    by_cases hc : cw.toNat ≤ 16
    · obtain ⟨n8, d8, u8⟩ := t7.taken hc5 0x19E bt_at_198 (by decide) (by
        show (!(reg n7 a2).ult (reg n7 a0)) = true
        rw [e2, e0]; simp only [BitVec.ult]; rw [show (16 : Word).toNat = 16 from rfl]
        rw [decide_eq_false (show ¬ 16 < cw.toNat by omega)]; rfl)
      exact ⟨n8, .single d8, ⟨u8.pc, u8.mem, fun _ => rfl⟩, acc, by rw [u8.regs]; exact e22, fun _ => rfl,
        fun r _ => by rw [u8.regs]⟩
    · obtain ⟨n8, d8, u8⟩ := t7.notTaken hc5 0x19C bt_at_198 (by decide) (by
        show (!(reg n7 a2).ult (reg n7 a0)) = false
        rw [e2, e0]; simp only [BitVec.ult]; rw [show (16 : Word).toNat = 16 from rfl]
        rw [decide_eq_true (show 16 < cw.toNat by omega)]; rfl)
      have t8 : St M0 BT n8 0x19C (reg n8) := ⟨u8.pc, u8.mem, fun _ => rfl⟩
      obtain ⟨n9, d9, u9⟩ := t8.aluImm hc5 bt_at_19c (off' := 0x19E) (by decide)
      exact ⟨n9, .cons d8 (.single d9), ⟨u9.pc, u9.mem, fun _ => rfl⟩, _, rfl, fun h => absurd h hc,
        fun r h => by rw [u9.regs, updz t8.zero h, u8.regs]⟩
  obtain ⟨n9, c9, u9⟩ := t8.block btSet hc5 btSet_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have t9 : St M0 BT n9 0x1B4 (reg n9) := ⟨u9.pc, u9.mem, fun _ => rfl⟩
  have r9 : ∀ r, reg n9 r = (runBlock btSet (M0, reg n8)).2 r := fun r => by rw [u9.regs]
  have hmask : aluEval .and cw (aluEval .sub 0 (aluEval .sltu cw 0x11)) = BitVec.ofNat 32 N := by
    by_cases hc : cw.toNat ≤ 16
    · rw [hNv, ite_eq_left hc]
      show cw &&& (0 - (if cw.ult 0x11 then 1 else 0)) = _
      rw [show cw.ult 0x11 = true from decide_eq_true (show cw.toNat < 17 by omega)]
      rw [show (0 : Word) - (if true = true then 1 else 0) = 0xFFFFFFFF from rfl, and_ff32, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
    · rw [hNv, ite_eq_right hc]
      show cw &&& (0 - (if cw.ult 0x11 then 1 else 0)) = _
      rw [show cw.ult 0x11 = false from decide_eq_false (show ¬ cw.toNat < 17 by omega)]
      exact BitVec.and_zero
  have g0 : reg n8 a0 = cw := by rw [k8 a0 (by decide)]; exact e0
  have g1 : reg n8 a1 = aluEval .sltu cw 0x11 := by rw [k8 a1 (by decide)]; exact e1
  have shl4 : aluEval .sll (BitVec.ofNat 32 N) 0x4 = BitVec.ofNat 32 (16 * N) := by
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 32 N <<< ((4 : Word).toNat % 32)).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [show (4 : Word).toNat % 32 = 4 from rfl]; omega
  have z8 : reg n9 8 = BitVec.ofNat 32 (16 * N) := by
    rw [r9]; simp +decide only [runBlock, BInstr.run, btSet, upd, ↓reduceIte]; rw [g0, g1, t8.zero, hmask, shl4]
  have z9 : reg n9 9 = P0 := by
    rw [r9]; simp +decide only [runBlock, BInstr.run, btSet, upd, ↓reduceIte]; rw [y22]; exact BitVec.zero_add _
  have z22 : reg n9 22 = P0 := by rw [r9, runBlock_reg _ _ _ 22 t8.zero (by decide)]; exact y22
  have z18 : reg n9 18 = P0 + BitVec.ofNat 32 (16 * N) := by
    rw [r9]; simp +decide only [runBlock, BInstr.run, btSet, upd, ↓reduceIte]; rw [g0, g1, t8.zero, hmask, shl4, y22]; rfl
  have z19 : reg n9 19 = 2 := by
    rw [r9]; simp +decide only [runBlock, BInstr.run, btSet, upd, ↓reduceIte]; (try rw [t8.zero]); try rfl
  have z21 : reg n9 21 = 0xFF900000 := by rw [r9]; simp +decide only [runBlock, BInstr.run, btSet, upd, ↓reduceIte]
  have k9 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 21 → r ≠ 22 →
      reg n9 r = reg n5 r :=
    fun r h0 h1 h2 h8 h9 h18 h19 h21 h22 => by
      rw [r9, runBlock_reg _ _ _ r t8.zero (by simp only [btSet]; revert h0 h1 h8 h9 h18 h19 h21; revert r; decide),
        k8 r h22, k7 r h0 h1 h2 h22]
  have kk9 : ∀ r, r = sp ∨ r = 20 ∨ r = 23 → reg n9 r = reg n5 r := fun r hr => by
    rcases hr with rfl | rfl | rfl <;>
      exact k9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
  -- the RAM copies, to 0x1E2
  have stageE2 : (∃ n10, Steps n9 n10 ∧ St n10.mem BT n10 0x1E2 (reg n10) ∧ BtHi M0 n10.mem ∧
      (∀ x, Sep Ss (btK R romStack) x 1 → n10.mem x = ramLoad flash M0 acc imgf N x) ∧
      memLoad32 n10.mem (top + 0xFFFFFFC0 + 4) = slot ∧
      ∀ r, romKeep r = true → r ≠ 8 → r ≠ 9 → reg n10 r = reg n9 r) ∨ HaltsWith n9 0xE2 := by
    by_cases hN0 : N = 0
    · obtain ⟨n10, d10, u10⟩ := t9.taken hc5 0x1E2 bt_at_1b4 (by decide) (by
        show (reg n9 8 == reg n9 x0) = true; rw [z8, t9.zero, hN0]; rfl)
      exact Or.inl ⟨n10, .single d10, ⟨u10.pc, rfl, fun _ => rfl⟩, fun x _ _ => by rw [u10.mem],
        fun x _ => by rw [u10.mem, hN0]; rfl, by rw [u10.mem]; exact hslot, fun r _ _ _ => by rw [u10.regs]⟩
    · obtain ⟨n10, d10, u10⟩ := t9.notTaken hc5 0x1B6 bt_at_1b4 (by decide) (by
        show (reg n9 8 == reg n9 x0) = false; rw [z8, t9.zero]
        exact decide_eq_false fun e => hN0 (by
          have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          simp at this; omega))
      have hcw : cw.toNat ≤ 16 := by
        by_cases h : cw.toNat ≤ 16
        · exact h
        · rw [hNv, ite_eq_right h] at hN0; exact absurd rfl hN0
      rcases bt_copy C hROM N 0 (by rw [hN]; omega) (by rw [hN]; omega)
          (⟨u10.pc, rfl, fun _ => rfl⟩ : St n10.mem BT n10 0x1B6 (reg n10)) (fun x _ _ => by rw [u10.mem])
          (fun x _ => by rw [u10.mem]; rfl)
          (by rw [u10.regs, kk9 sp (by simp)]; exact sp5)
          (by unfold sgPtr; rw [u10.regs, z9, hP0 hcw, Nat.mul_zero, add_ofNat_zero])
          (by rw [u10.regs, z8, hN, Nat.sub_zero])
          (by rw [u10.regs]; exact z19) (by rw [u10.regs]; exact z21)
          (by rw [u10.regs, kk9 20 (by simp)]; exact w20) with ⟨n', c', s', hH', fr', o', k'⟩ | hp
      · rw [hN, hSs] at o'
        refine Or.inl ⟨n', .cons d10 c', s', hH', o', ?_, fun r hr h8 h9 => by rw [k' r hr h8 h9, u10.regs]⟩
        rw [← hslot]
        exact memLoad32_congr fun j hj => by
          rw [show top + 0xFFFFFFC0 + 4 + BitVec.ofNat 32 j = top + 0xFFFFFFC0 + BitVec.ofNat 32 (4 + j) from
            add_ofNat_assoc _ 4 j, fr' _ (by omega), u10.mem]
      · exact Or.inr (HaltsWith.of_steps (.single d10) hp)
  have pre9 : Steps n5 n9 := .cons d6 (c7.trans (c8.trans c9))
  refine stageE2.elim (fun h => ?_) fun hp => Or.inr (HaltsWith.of_steps pre9 hp)
  obtain ⟨n10, c10, t10, hH10, o10, fr10, k10⟩ := h
  have q10 : ∀ r, r = sp ∨ r = 18 ∨ r = 20 ∨ r = 22 ∨ r = 23 → reg n10 r = reg n9 r := fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact k10 _ (by decide) (by decide) (by decide)
  have sp10 : reg n10 sp = top + 0xFFFFFFC0 := by rw [q10 sp (by simp), kk9 sp (by simp)]; exact sp5
  have s23 : reg n10 23 = acc := by rw [q10 23 (by simp), kk9 23 (by simp)]; exact w23
  have s20 : reg n10 20 = imgf := by rw [q10 20 (by simp), kk9 20 (by simp)]; exact w20
  have s18 : reg n10 18 = P0 + BitVec.ofNat 32 (16 * N) := by rw [q10 18 (by simp)]; exact z18
  have s22 : reg n10 22 = P0 := by rw [q10 22 (by simp)]; exact z22
  -- the registers `boot` still needs, through a step that keeps them
  have keepS : ∀ {n n' : Machine}, (∀ r, r = sp ∨ r = 18 ∨ r = 20 ∨ r = 22 ∨ r = 23 → reg n' r = reg n r) →
      reg n sp = top + 0xFFFFFFC0 ∧ reg n 18 = P0 + BitVec.ofNat 32 (16 * N) ∧ reg n 20 = imgf ∧
        reg n 22 = P0 ∧ reg n 23 = acc →
      reg n' sp = top + 0xFFFFFFC0 ∧ reg n' 18 = P0 + BitVec.ofNat 32 (16 * N) ∧ reg n' 20 = imgf ∧
        reg n' 22 = P0 ∧ reg n' 23 = acc := fun h ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨by rw [h sp (by simp)]; exact h1, by rw [h 18 (by simp)]; exact h2, by rw [h 20 (by simp)]; exact h3,
      by rw [h 22 (by simp)]; exact h4, by rw [h 23 (by simp)]; exact h5⟩
  have romK : ∀ r, r = sp ∨ r = 18 ∨ r = 20 ∨ r = 22 ∨ r = 23 → romKeep r = true := fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  have R10 := (⟨sp10, s18, s20, s22, s23⟩ : reg n10 sp = top + 0xFFFFFFC0 ∧
    reg n10 18 = P0 + BitVec.ofNat 32 (16 * N) ∧ reg n10 20 = imgf ∧ reg n10 22 = P0 ∧ reg n10 23 = acc)
  have hc10 := hiKeep C.code hH10 (by decide) (by decide)
  -- cache_suspend, then the 128 invalid entries
  obtain ⟨n11, c11, u11⟩ := t10.block btSusp hc10 btSusp_end ⟨trivial, trivial, trivial⟩
  have t11 : St n11.mem BT n11 0x1EA (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have r11 : ∀ r, reg n11 r = (runBlock btSusp (n10.mem, reg n10)).2 r := fun r => by rw [u11.regs]
  have R11 := keepS (n := n10) (n' := n11) (fun r hr => by
    rw [r11, runBlock_reg _ _ _ r t10.zero (by simp only [btSusp]; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]) R10
  have v11 : reg n11 9 = 0x80 := by
    rw [r11]; simp +decide only [runBlock, BInstr.run, btSusp, upd, ↓reduceIte]; (try rw [t10.zero]); try rfl
  obtain ⟨n12, c12, t12, o12, hH12, fr12, k12⟩ := romcall 0x40000524 n11 (reg n11) 0x1EA _ _ suspend t11 R11.1
    (by rw [m11]; exact hH10) bt_at_1ea bt_at_1ee (by decide) (by decide) (by decide)
  rw [m11, fr10] at fr12
  have R12 := keepS (n := n11) (n' := n12) (fun r hr => k12 r (romK r hr)) R11
  have hc12 := hiKeep C.code hH12 (by decide) (by decide)
  obtain ⟨n13, c13, u13⟩ := t12.block btInv0 hc12 btInv0_end ⟨trivial, trivial, trivial⟩
  have t13 : St n12.mem BT n13 0x1F8 (reg n13) := ⟨u13.pc, u13.mem, fun _ => rfl⟩
  have r13 : ∀ r, reg n13 r = (runBlock btInv0 (n12.mem, reg n12)).2 r := fun r => by rw [u13.regs]
  have R13 := keepS (n := n12) (n' := n13) (fun r hr => by
    rw [r13, runBlock_reg _ _ _ r t12.zero (by simp only [btInv0]; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]) R12
  have v13 : reg n13 9 = 0x80 := by
    rw [r13, runBlock_reg _ _ _ 9 t12.zero (by decide), k12 9 (by decide)]; exact v11
  have a13 : reg n13 a0 = 0x100 := by
    rw [r13]; simp +decide only [runBlock, BInstr.run, btInv0, upd, ↓reduceIte]; (try rw [t12.zero]); try rfl
  have e13 : reg n13 8 = 0x600C5000 := by
    rw [r13, runBlock_reg _ _ _ 8 t12.zero (by decide), k12 8 (by decide), r11]
    simp +decide only [runBlock, BInstr.run, btSusp, upd, ↓reduceIte]
  obtain ⟨n14, d14, u14⟩ := t13.notTaken hc12 0x1FA bt_at_1f8 (by decide) (by
    show (reg n13 9 == reg n13 x0) = false; rw [v13, t13.zero]; rfl)
  have mi0 : mmuInv n12.mem 0 = n12.mem := funext fun x => by unfold mmuInv; rw [ite_eq_right (by omega)]
  obtain ⟨n15, c15, t15, k15⟩ := bt_inv hc12 128 0 (n := n14) rfl (by decide)
    (by rw [mi0]; exact ⟨u14.pc, u14.mem, fun _ => rfl⟩) (by rw [u14.regs, e13]; rfl) (by rw [u14.regs, v13]; rfl)
    (by rw [u14.regs]; exact a13)
  have R15 := keepS (n := n13) (n' := n15) (fun r hr => by
    rw [k15 r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), u14.regs]) R13
  -- the agreement of the memory so far with the specification
  have hMx : ∀ x, Sep Ss (btK R romStack) x 1 → n12.mem x = ramLoad flash M0 acc imgf N x := fun x hx => by
    rw [o12 x hx, m11, o10 x hx]
  have mmuLo : ∀ x : Word, x.toNat < 0x600C5000 → mmuInv n12.mem 128 x = n12.mem x := fun x hx => by
    unfold mmuInv; rw [ite_eq_right (by rw [BitVec.toNat_sub, show (mmuBase).toNat = 0x600C5000 from rfl]; omega)]
  have hH15 : BtHi M0 (mmuInv n12.mem 128) := fun x h1 h2 => by rw [mmuLo x (by omega)]; exact hH12 x h1 h2
  have hc15 := hiKeep C.code hH15 (by decide) (by decide)
  obtain ⟨n16, c16, u16⟩ := t15.block btMap0 hc15 btMap0_end ⟨trivial, trivial, trivial, trivial⟩
  have t16 : St (mmuInv n12.mem 128) BT n16 0x20C (reg n16) := ⟨u16.pc, u16.mem, fun _ => rfl⟩
  have r16 : ∀ r, reg n16 r = (runBlock btMap0 (mmuInv n12.mem 128, reg n15)).2 r := fun r => by rw [u16.regs]
  have R16 := keepS (n := n15) (n' := n16) (fun r hr => by
    rw [r16, runBlock_reg _ _ _ r t15.zero (by simp only [btMap0]; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]) R15
  -- the MMU entries, to 0x25A
  have hT : ∀ i, i < 0x10C → mmuInv n12.mem 128 (acc + BitVec.ofNat 32 i) = M0 (acc + BitVec.ofNat 32 i) :=
    fun i hi => by
      have hlo : (acc + BitVec.ofNat 32 i).toNat < 0x40000000 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      rw [mmuLo _ (by omega), hMx _ (tbl i hi)]
      exact ramLoad_out _ N fun j hj hk => ((C.ram j (by rw [hN]; omega) hk).2.2.1.symm.sub (c := i) (l := 1) (by omega)).symm
  obtain ⟨n17, c17, t17, k17⟩ : ∃ n17, Steps n16 n17 ∧
      St (mmuMap M0 acc imgf (mmuInv n12.mem 128) N) BT n17 0x25A (reg n17) ∧
      ∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → r ≠ 22 → reg n17 r = reg n16 r := by
    by_cases hN0 : N = 0
    · subst hN0
      obtain ⟨n17, d17, u17⟩ := t16.taken hc15 0x25A bt_at_20c (by decide) (by
        show (reg n16 22 == reg n16 18) = true
        rw [R16.2.2.2.1, R16.2.1, Nat.mul_zero, add_ofNat_zero]; exact decide_eq_true rfl)
      exact ⟨n17, .single d17, ⟨u17.pc, u17.mem, fun _ => rfl⟩, fun r _ _ _ _ _ _ => by rw [u17.regs]⟩
    · have hcw : cw.toNat ≤ 16 := by
        by_cases h : cw.toNat ≤ 16
        · exact h
        · rw [hNv, ite_eq_right h] at hN0; exact absurd rfl hN0
      have hbt : BT.toNat + bootFnCode.length ≤ 0x600C4000 := by decide
      obtain ⟨n17, c17, t17, k17⟩ := bt_map hbt hN16 hacc haccl (fun j hj => C.kind j (by rw [hN]; exact hj)) hT
        hc15 N 0 (by omega) (by omega) t16
        (by rw [R16.2.2.2.1, hP0 hcw]; unfold sgPtr; rw [Nat.mul_zero, add_ofNat_zero])
        (by rw [R16.2.1, hP0 hcw]; rfl)
        (by rw [r16]; simp +decide only [runBlock, BInstr.run, btMap0, upd, ↓reduceIte]; (try rw [t15.zero]); try rfl)
        (by rw [r16]; simp +decide only [runBlock, BInstr.run, btMap0, upd, ↓reduceIte]; (try rw [t15.zero]); try rfl)
        (by rw [r16]; simp +decide only [runBlock, BInstr.run, btMap0, upd, ↓reduceIte])
        R16.2.2.1
      exact ⟨n17, c17, t17, k17⟩
  have k17' : ∀ r, r = sp ∨ r = 23 → reg n17 r = reg n16 r := fun r hr => by
    rcases hr with rfl | rfl <;> exact k17 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have sp17 : reg n17 sp = top + 0xFFFFFFC0 := by rw [k17' sp (by simp)]; exact R16.1
  have s23' : reg n17 23 = acc := by rw [k17' 23 (by simp)]; exact R16.2.2.2.2
  -- both cache buses on
  obtain ⟨Mm, hMm⟩ : ∃ Mm, mmuMap M0 acc imgf (mmuInv n12.mem 128) N = Mm := ⟨_, rfl⟩
  rw [hMm] at t17
  have hHm : BtHi M0 Mm := fun x h1 h2 => by rw [← hMm, mmuMap_low N x (by omega)]; exact hH15 x h1 h2
  have frm : memLoad32 Mm (top + 0xFFFFFFC0 + 4) = slot := by
    rw [← fr12]; exact memLoad32_congr fun j hj => by
      have := frLo j hj
      rw [← hMm, mmuMap_low N _ (by omega), mmuLo _ (by omega)]
  have hcm := hiKeep C.code hHm (by decide) (by decide)
  obtain ⟨n18, c18, u18⟩ := t17.block btBus hcm btBus_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, btBus]
    simp +decide only [upd, ↓reduceIte, true_and, and_true]
    exact (sep_of_le (by decide) (by decide)).symm)
  have m18 : n18.mem = busOn Mm := by
    rw [u18.mem]; simp +decide only [runBlock, BInstr.run, btBus, upd, ↓reduceIte]; rfl
  have r18 : ∀ r, reg n18 r = (runBlock btBus (Mm, reg n17)).2 r := fun r => by rw [u18.regs]
  have q18 : ∀ r, r ≠ a0 → r ≠ a1 → reg n18 r = reg n17 r := fun r h0 h1 => by
    rw [r18, runBlock_reg _ _ _ r t17.zero (by simp only [btBus]; revert h0 h1; revert r; decide)]
  have t18 : St n18.mem BT n18 0x264 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have hHb : BtHi M0 n18.mem := fun x h1 h2 => by
    rw [m18]; unfold busOn; rw [st32_low Mm _ (by decide) (by decide) (by omega)]; exact hHm x h1 h2
  have fr18 : memLoad32 n18.mem (top + 0xFFFFFFC0 + 4) = slot := by
    rw [← frm]; exact memLoad32_congr fun j hj => by
      have := frLo j hj
      rw [m18]; unfold busOn; rw [st32_low Mm _ (by decide) (by decide) (by omega)]
  obtain ⟨n19, c19, t19, o19, hH19, fr19, k19⟩ := romcall 0x400004D8 n18 (reg n18) 0x264 _ _ invalidate t18
    (by rw [q18 sp (by decide) (by decide)]; exact sp17) hHb bt_at_264 bt_at_268 (by decide) (by decide) (by decide)
  have hc19 := hiKeep C.code hH19 (by decide) (by decide)
  obtain ⟨n20, d20, u20⟩ := t19.alu hc19 bt_at_26c (off' := 0x26E) (by decide)
  have t20 := u20.self
  have q20 : ∀ r, r ≠ a0 → reg n20 r = reg n19 r := fun r h => by rw [u20.regs]; exact updz t19.zero h
  obtain ⟨n21, c21, t21, o21, hH21, fr21, k21⟩ := romcall 0x40000528 n20 (reg n20) 0x26E _ _ resume
    (⟨t20.pc, rfl, fun _ => rfl⟩ : St n20.mem BT n20 0x26E (reg n20))
    (by rw [q20 sp (by decide), k19 sp (by decide), q18 sp (by decide) (by decide)]; exact sp17)
    (by rw [u20.mem]; exact hH19) bt_at_26e bt_at_272 (by decide) (by decide) (by decide)
  have keep21 : ∀ r, r = sp ∨ r = 23 → reg n21 r = reg n17 r := fun r hr => by
    have hk : romKeep r = true := by rcases hr with rfl | rfl <;> decide
    have h0 : r ≠ a0 := by rcases hr with rfl | rfl <;> decide
    have h1 : r ≠ a1 := by rcases hr with rfl | rfl <;> decide
    rw [k21 r hk, q20 r h0, k19 r hk, q18 r h0 h1]
  rw [u20.mem, fr19, fr18] at fr21
  -- the entry point, the log, and the jump
  have o21' : ∀ x, Sep Ss (btK R romStack) x 1 → n21.mem x = busOn Mm x := fun x hx => by
    rw [o21 x hx, u20.mem, o19 x hx, m18]
  have hent : memLoad32 n21.mem (acc + 0x100) = memLoad32 M0 (acc + 0x100) :=
    memLoad32_congr fun i hi => by
      rw [show acc + 0x100 + BitVec.ofNat 32 i = acc + BitVec.ofNat 32 (0x100 + i) from add_ofNat_assoc acc 0x100 i]
      have hlo : (acc + BitVec.ofNat 32 (0x100 + i)).toNat < 0x40000000 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      rw [o21' _ (tbl _ (by omega))]
      unfold busOn; rw [st32_low Mm _ (by decide) (by decide) (by omega), ← hMm, mmuMap_low N _ (by omega)]
      exact hT _ (by omega)
  have hc21 := hiKeep C.code hH21 (by decide) (by decide)
  obtain ⟨n22, c22, u22⟩ := t21.block btJmp hc21 btJmp_end (by
    simp only [BlockOk, BInstr.ok, btJmp]
    simp +decide only [and_true]
    rw [keep21 23 (by simp), s23', BitVec.toNat_add]; simp; omega)
  have t22 : St n22.mem BT n22 0x284 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have r22 : ∀ r, reg n22 r = (runBlock btJmp (n21.mem, reg n21)).2 r := fun r => by rw [u22.regs]
  have e22 : reg n22 8 = memLoad32 M0 (acc + 0x100) := by
    rw [r22]; simp +decide only [runBlock, BInstr.run, btJmp, upd, ↓reduceIte]; rw [keep21 23 (by simp), s23', hent]
  have q22 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ 8 → reg n22 r = reg n21 r := fun r h0 h1 h8 => by
    rw [r22, runBlock_reg _ _ _ r t21.zero (by simp only [btJmp]; revert h0 h1 h8; revert r; decide)]
  obtain ⟨n23, c23, t23, o23, hH23, fr23, k23⟩ := romcall 0x40000040 n22 (reg n22) 0x284 _ _ log t22
    (by rw [q22 sp (by decide) (by decide) (by decide), keep21 sp (by simp)]; exact sp17) (by rw [m22]; exact hH21)
    bt_at_284 bt_at_288 (by decide) (by decide) (by decide)
  rw [m22, fr21] at fr23
  have hc23 := hiKeep C.code hH23 (by decide) (by decide)
  have sp23 : reg n23 sp = top + 0xFFFFFFC0 := by
    rw [k23 sp (by decide), q22 sp (by decide) (by decide) (by decide), keep21 sp (by simp)]; exact sp17
  obtain ⟨n24, d24, u24⟩ := t23.lw hc23 bt_at_28c (off' := 0x28E) (by decide)
    (by rw [sp23, BitVec.toNat_add, hsp1, show (4 : Word).toNat = 4 from rfl]; omega)
  obtain ⟨n25, d25, pc25, mem25, regs25⟩ := u24.call hc23 bt_at_28e
  refine Or.inl ⟨n25, pre9.trans (c10.trans (c11.trans (c12.trans (c13.trans (.cons d14 (c15.trans (c16.trans
    (c17.trans (c18.trans (c19.trans (.cons d20 (c21.trans (c22.trans (c23.trans (.cons d24 (.single d25)))))))))))))))),
    ?_, ?_, fun x hx => ?_⟩
  · rw [pc25]; simp +decide only [upd, ↓reduceIte]
    rw [k23 8 (by decide), e22, add_lit_zero]
  · rw [regs25]; simp +decide only [upd, ↓reduceIte]
    rw [sp23]; exact fr23
  · rw [mem25, o23 x hx, m22, o21' x hx]
    unfold bootMem; rw [hN, ← hMm]
    refine busOn_agree (O := fun x => Sep Ss (btK R romStack) x 1)
      (mmuMap_agree (mmuInv_agree hMx 128) N) (fun i hi => stkHi _ ?_) x hx
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (icacheCtrl1).toNat = 0x600C4004 from rfl]; omega

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 20000 in
/-- `boot` from its entry, called with the slot, the accepted header, the
image's flash offset, the target security level, and the level the caller
read: it raises the level when the target is above it, locks the eFuse and
flash registers, and jumps to the header's entry point with the slot in
`a0` and the memory outside its stack and those registers as `bootMem`
says. At the jump the eFuse level word is its value at entry with some
bits set, and the level `btPop` counts from it is at least `target`, or
the caller's `level` is at least `target` and the word is unchanged. The
eFuse controller is assumed to meet `EfuseCtl` (`BtCtx.epr`). Or it
halts deliberately: with code 0xE1 when the level read back stays below
`target` after the raise loop's tries, or 0xE2 when a flash read of the
image fails. -/
theorem boot_correct_halt {flash : Nat → BitVec 8} {R romStack : Nat} {romBase : Word} {romCode : List Nat}
    (m : Machine) {slot acc imgf target level : Word}
    (C : BtCtx m.mem (reg m sp) acc imgf R romStack romBase romCode) (hROM : RomRead flash R romBase romCode)
    (hpc : m.pc = BT) (ha0 : reg m a0 = slot) (ha1 : reg m a1 = acc) (ha2 : reg m a2 = imgf)
    (ha3 : reg m a3 = target) (ha4 : reg m a4 = level)
    (log : RomFn romBase romCode 0x40000040 romStack fun _ => True)
    (suspend : RomFn romBase romCode 0x40000524 romStack fun _ => True)
    (invalidate : RomFn romBase romCode 0x400004D8 romStack fun _ => True)
    (resume : RomFn romBase romCode 0x40000528 romStack fun _ => True) :
    (∃ m', Steps m m' ∧ m'.pc = memLoad32 m.mem (acc + 0x100) &&& ~~~1 ∧ reg m' a0 = slot ∧
      ((btPop (memLoad32 m'.mem efuseRd)).ult target = false ∨
        (level.ult target = false ∧ memLoad32 m'.mem efuseRd = memLoad32 m.mem efuseRd)) ∧
      (∃ X, memLoad32 m'.mem efuseRd = memLoad32 m.mem efuseRd ||| X) ∧
      ∀ x, Sep (reg m sp - BitVec.ofNat 32 (btK R romStack)) (btK R romStack) x 1 →
        (x.toNat < 0x60000000 ∨ 0x600C4000 ≤ x.toNat) → m'.mem x = bootMem flash m.mem acc imgf x) ∨
      HaltsDeliberately m := by
  obtain ⟨top, htop⟩ : ∃ top, reg m sp = top := ⟨_, rfl⟩
  rw [htop] at C ⊢
  obtain ⟨M0, hM0⟩ : ∃ M0, m.mem = M0 := ⟨_, rfl⟩
  rw [hM0] at C ⊢
  have hKv : btK R romStack = 0x40 + 16 + R + romStack := rfl
  have hspl := C.hspl; have hsph := C.hsph; have h16 := C.hsp; have hR4 := C.hR
  rw [hKv] at hspl; unfold dramEnd at hsph
  obtain ⟨Ss, hSs⟩ : ∃ Ss, top - BitVec.ofNat 32 (btK R romStack) = Ss := ⟨_, rfl⟩
  rw [hSs]
  have sAS := C.sAS; rw [hSs] at sAS
  have hSn : Ss.toNat = top.toNat - btK R romStack := by
    rw [← hSs, BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]; omega
  have hsp1 : (top + 0xFFFFFFC0).toNat = top.toNat - 0x40 := by
    rw [BitVec.toNat_add, show (0xFFFFFFC0 : Word).toNat = 2 ^ 32 - 0x40 from rfl]; omega
  have hRS : (top + 0xFFFFFFC0 - BitVec.ofNat 32 romStack).toNat = top.toNat - 0x40 - romStack := by
    rw [BitVec.toNat_sub, hsp1, BitVec.toNat_ofNat]; omega
  -- the stack region
  have stk : ∀ c l, c + l ≤ 0x40 → ∀ x, Sep Ss (btK R romStack) x 1 → Sep (top + 0xFFFFFFC0 + BitVec.ofNat 32 c) l x 1 :=
    fun c l h x hx => by
      have e : top + 0xFFFFFFC0 + BitVec.ofNat 32 c = Ss + BitVec.ofNat 32 (16 + R + romStack + c) :=
        BitVec.eq_of_toNat_eq (by
          rw [BitVec.toNat_add (top + 0xFFFFFFC0), hsp1, BitVec.toNat_add Ss, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hSn, hKv]; omega)
      rw [e]; exact hx.sub (by rw [hKv]; omega)
  have romS : ∀ x, Sep Ss (btK R romStack) x 1 → Sep (top + 0xFFFFFFC0 - BitVec.ofNat 32 romStack) romStack x 1 :=
    fun x hx => by
      have e : top + 0xFFFFFFC0 - BitVec.ofNat 32 romStack = Ss + BitVec.ofNat 32 (16 + R) :=
        BitVec.eq_of_toNat_eq (by
          rw [hRS, BitVec.toNat_add Ss, BitVec.toNat_ofNat, hSn, hKv]; omega)
      rw [e]; exact hx.sub (by rw [hKv]; omega)
  have stkHi : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep Ss (btK R romStack) x 1 := fun x hx =>
    sep_of_le (by rw [hSn, hKv]; omega) (by have := x.isLt; omega)
  have tbl : ∀ i, i < 0x10C → Sep Ss (btK R romStack) (acc + BitVec.ofNat 32 i) 1 := fun i hi =>
    (sAS.sub (c := i) (l := 1) (by omega)).symm
  have hacc := C.hacc; have haccl := C.haccl
  have al : ∀ c : Word, c.toNat + 4 ≤ 0x40 → c.toNat % 4 = 0 →
      (top + 0xFFFFFFC0 + c).toNat % 4 = 0 ∧ Sep (top + 0xFFFFFFC0 + c) 4 BT bootFnCode.length := fun c h1 h2 => by
    have e : (top + 0xFFFFFFC0 + c).toNat = top.toNat - 0x40 + c.toNat := by
      rw [BitVec.toNat_add, hsp1]; omega
    exact ⟨by rw [e]; omega, sep_of_le (by rw [e, show BT.toNat = (img% bootFnAddress) from rfl]; omega) (by decide)⟩
  -- the prologue
  have s0 : St M0 BT m 0 (reg m) := ⟨by rw [hpc]; rfl, hM0, fun _ => rfl⟩
  have hz := s0.zero
  have hc0 := C.code
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc0 bt_at_0 (off' := 2) (by decide)
  rw [htop, show aluEval .add top 0xFFFFFFC0 = top + 0xFFFFFFC0 from rfl] at u1
  have g1sp : upd (reg m) sp (top + 0xFFFFFFC0) sp = top + 0xFFFFFFC0 := by simp +decide [upd]
  obtain ⟨n2, c2, u2⟩ := u1.block btPro hc0 btPro_end (by
    rw [btPro_eq]
    refine saveBlock_ok _ _ _ fun p hp => ?_
    rw [g1sp]
    simp only [btPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact al _ (by decide) (by decide))
  have hr2 : runBlock btPro (M0, upd (reg m) sp (top + 0xFFFFFFC0)) =
      (saveMem M0 (top + 0xFFFFFFC0) (upd (reg m) sp (top + 0xFFFFFFC0)) btPs, upd (reg m) sp (top + 0xFFFFFFC0)) := by
    rw [btPro_eq, saveBlock_run, g1sp]
  rw [hr2] at u2
  obtain ⟨M2, hM2⟩ : ∃ M2, saveMem M0 (top + 0xFFFFFFC0) (upd (reg m) sp (top + 0xFFFFFFC0)) btPs = M2 := ⟨_, rfl⟩
  rw [hM2] at u2
  have o2 : ∀ x, Sep Ss (btK R romStack) x 1 → M2 x = M0 x := fun x hx => by
    rw [← hM2]; refine saveMem_sep _ fun p hp => ?_
    simp only [btPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact stk _ 4 (by decide) x hx
  have hH2 : BtHi M0 M2 := fun x h1 _ => o2 x (stkHi x h1)
  have hc2 := hiKeep C.code hH2 (by decide) (by decide)
  -- the frame: the image's offset to register 20, the header and the slot to the stack
  obtain ⟨n3, c3, u3⟩ := u2.block btFr hc2 btFr_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, btFr]
    simp +decide only [upd, ↓reduceIte, true_and, and_true]
    exact ⟨al 8 (by decide) (by decide), al 4 (by decide) (by decide)⟩)
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 (memStore32 M2 (top + 0xFFFFFFC0 + 8) acc) (top + 0xFFFFFFC0 + 4) slot = M3 :=
    ⟨_, rfl⟩
  have e3 : (runBlock btFr (M2, upd (reg m) sp (top + 0xFFFFFFC0))).1 = M3 := by
    rw [← hM3]; simp +decide only [runBlock, BInstr.run, btFr, upd, ↓reduceIte]; rw [ha1, ha0]
  have t3 : St M3 BT n3 0x22 (reg n3) := ⟨u3.pc, u3.mem.trans e3, fun _ => rfl⟩
  have r3 : ∀ r, reg n3 r = (runBlock btFr (M2, upd (reg m) sp (top + 0xFFFFFFC0))).2 r := fun r => by rw [u3.regs]
  have q3 : ∀ r, r ≠ sp → r ≠ 20 → reg n3 r = reg m r := fun r h1 h2 => by
    rw [r3, runBlock_reg _ _ _ r (by simp [upd]) (by simp only [btFr]; revert h2; revert r; decide)]
    exact updz hz h1
  have sp3 : reg n3 sp = top + 0xFFFFFFC0 := by
    rw [r3, runBlock_reg _ _ _ sp (by simp [upd]) (by decide)]; exact g1sp
  have v20 : reg n3 20 = imgf := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, btFr, upd, ↓reduceIte]; rw [ha2]; exact BitVec.zero_add _
  have st4 : ∀ x, Sep Ss (btK R romStack) x 1 → Sep (top + 0xFFFFFFC0 + 4) 4 x 1 := fun x hx => stk 4 4 (by decide) x hx
  have st8 : ∀ x, Sep Ss (btK R romStack) x 1 → Sep (top + 0xFFFFFFC0 + 8) 4 x 1 := fun x hx => stk 8 4 (by decide) x hx
  have o3 : ∀ x, Sep Ss (btK R romStack) x 1 → M3 x = M0 x := fun x hx => by
    rw [← hM3, memStore32_get_sep (st4 x hx), memStore32_get_sep (st8 x hx), o2 x hx]
  have hS4 : (top + 0xFFFFFFC0 + 4).toNat = top.toNat - 0x3C := by
    rw [BitVec.toNat_add, hsp1, show (4 : Word).toNat = 4 from rfl]; omega
  have hS8 : (top + 0xFFFFFFC0 + 8).toNat = top.toNat - 0x38 := by
    rw [BitVec.toNat_add, hsp1, show (8 : Word).toNat = 8 from rfl]; omega
  have f4 : memLoad32 M3 (top + 0xFFFFFFC0 + 4) = slot := by rw [← hM3]; exact memLoad32_store32_same _ _ _
  have f8 : memLoad32 M3 (top + 0xFFFFFFC0 + 8) = acc := by
    rw [← hM3, memLoad32_store32_sep (sep_of_le (by rw [hS4, hS8]; omega) (by rw [hS8]; omega)),
      memLoad32_store32_same]
  have hH3 : BtHi M0 M3 := fun x h1 _ => o3 x (stkHi x h1)
  have hc3 := hiKeep C.code hH3 (by decide) (by decide)
  have hw3 : memLoad32 M3 efuseRd = memLoad32 M0 efuseRd := memLoad32_congr fun j hj => by
    have h : 0x40000000 ≤ (efuseRd + BitVec.ofNat 32 j).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, show efuseRd.toNat = 0x6000883C from rfl]; omega
    exact o3 _ (stkHi _ h)
  -- the security level, to 0x156
  have stage : (∃ n4, Steps n3 n4 ∧ St n4.mem BT n4 0x156 (reg n4) ∧
      (∀ x, Sep Ss (btK R romStack) x 1 → (x.toNat < 0x60008800 ∨ 0x60008A00 ≤ x.toNat) → n4.mem x = M3 x) ∧
      (∀ j, j < 4 → n4.mem (top + 0xFFFFFFC0 + 4 + BitVec.ofNat 32 j) = M3 (top + 0xFFFFFFC0 + 4 + BitVec.ofNat 32 j)) ∧
      (∀ j, j < 4 → n4.mem (top + 0xFFFFFFC0 + 8 + BitVec.ofNat 32 j) = M3 (top + 0xFFFFFFC0 + 8 + BitVec.ofNat 32 j)) ∧
      ((btPop (memLoad32 n4.mem efuseRd)).ult target = false ∨
        (level.ult target = false ∧ memLoad32 n4.mem efuseRd = memLoad32 M0 efuseRd)) ∧
      (∃ X, memLoad32 n4.mem efuseRd = memLoad32 M0 efuseRd ||| X) ∧
      reg n4 sp = top + 0xFFFFFFC0 ∧ reg n4 20 = imgf) ∨ HaltsWith n3 0xE1 := by
    by_cases hl : level.ult target = true
    · obtain ⟨n4, d4, u4⟩ := t3.notTaken hc3 0x26 bt_at_22 (by decide) (by
        show (!(reg n3 a4).ult (reg n3 a3)) = false
        rw [q3 a4 (by decide) (by decide), q3 a3 (by decide) (by decide), ha4, ha3, hl]; rfl)
      have t4 : St M3 BT n4 0x26 (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
      obtain ⟨n5, c5, u5⟩ := t4.block btRaise hc3 btRaise_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
      have t5 : St n5.mem BT n5 0x36 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
      have m5 : n5.mem = M3 := u5.mem
      have r5 : ∀ r, reg n5 r = (runBlock btRaise (M3, reg n4)).2 r := fun r => by rw [u5.regs]
      have k45 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ 9 → r ≠ 22 → reg n5 r = reg n3 r := fun r h0 h1 h9 h22 => by
        rw [r5, runBlock_reg _ _ _ r t4.zero (by simp only [btRaise]; revert h0 h1 h9 h22; revert r; decide), u4.regs]
      have v9 : reg n5 9 = 0x60009000 := by rw [r5]; simp +decide only [runBlock, BInstr.run, btRaise, upd, ↓reduceIte]
      have v22 : reg n5 22 = target := by
        rw [r5]; simp +decide only [runBlock, BInstr.run, btRaise, upd, ↓reduceIte]
        rw [u4.regs x0, u4.regs a3, q3 a3 (by decide) (by decide), ha3, show reg n3 x0 = 0 from t3.zero]
        exact BitVec.zero_add _
      have sp5 : reg n5 sp = top + 0xFFFFFFC0 := by
        rw [k45 sp (by decide) (by decide) (by decide) (by decide)]; exact sp3
      obtain ⟨n6, c6, t6, o6, k6⟩ := bt_romcall 0x40000040 log t5 sp5 (by rw [m5]; exact hc3)
        (by rw [m5]; exact hiKeep C.rom hH3 C.hrb C.hrl) (by rw [hsp1]; omega) bt_at_36 bt_at_3a
        (by decide) (by decide) (by decide)
      have o6' : ∀ x, Sep Ss (btK R romStack) x 1 → n6.mem x = M3 x := fun x hx => by rw [o6 x (romS x hx), m5]
      have hH6 : BtHi M0 n6.mem := fun x h1 _ => by rw [o6' x (stkHi x h1)]; exact o3 x (stkHi x h1)
      have fr6 : ∀ c, c ≤ 8 → ∀ j, j < 4 → n6.mem (top + 0xFFFFFFC0 + BitVec.ofNat 32 c + BitVec.ofNat 32 j) =
          M3 (top + 0xFFFFFFC0 + BitVec.ofNat 32 c + BitVec.ofNat 32 j) := fun c hc j hj => by
        have e : (top + 0xFFFFFFC0 + BitVec.ofNat 32 c + BitVec.ofNat 32 j).toNat = top.toNat - 0x40 + c + j := by
          rw [BitVec.toNat_add, BitVec.toNat_add, hsp1, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
        rw [o6 _ (sep_of_le (by rw [hRS, e]; omega) (by rw [e]; omega)), m5]
      have lo6 : ∀ c, c ≤ 8 → ∀ j, j < 4 →
          (top + 0xFFFFFFC0 + BitVec.ofNat 32 c + BitVec.ofNat 32 j).toNat < 0x60008800 := fun c hc j hj => by
        rw [BitVec.toNat_add, BitVec.toNat_add, hsp1, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
      rcases rs_raise (n := n6) (target := target) ⟨hiKeep C.code hH6 (by decide) (by decide), C.epr.code hH6,
          panicKeep C.panic hH6⟩ ⟨t6.pc, rfl, fun _ => rfl⟩
          ((k6 9 (by decide)).trans v9) ((k6 22 (by decide)).trans v22)
          (by rw [k6 sp (by decide), sp5]; unfold Room; rw [hsp1]; unfold dramEnd; exact ⟨by omega, by omega, by omega⟩)
        with ⟨n7, c7, s7, hO7, hge, ⟨X, hX⟩, k7⟩ | hp
      · have hfd : memLoad32 n6.mem efuseRd = memLoad32 M0 efuseRd := memLoad32_congr fun j hj => by
          have h : 0x40000000 ≤ (efuseRd + BitVec.ofNat 32 j).toNat := by
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, show efuseRd.toNat = 0x6000883C from rfl]; omega
          rw [o6' _ (stkHi _ h), o3 _ (stkHi _ h)]
        refine Or.inl ⟨n7, .cons d4 (c5.trans (c6.trans c7)), s7,
          fun x hx hE => by rw [hO7 x hE, o6' x hx],
          fun j hj => (hO7 _ (Or.inl (lo6 4 (by omega) j hj))).trans (fr6 4 (by omega) j hj),
          fun j hj => (hO7 _ (Or.inl (lo6 8 (by omega) j hj))).trans (fr6 8 (by omega) j hj), Or.inl hge,
          ⟨X, by rw [hX, hfd]⟩, ?_, ?_⟩
        · rw [k7 sp (by decide), k6 sp (by decide)]; exact sp5
        · rw [k7 20 (by decide), k6 20 (by decide), k45 20 (by decide) (by decide) (by decide) (by decide)]; exact v20
      · exact Or.inr (HaltsWith.of_steps (.cons d4 (c5.trans c6)) hp)
    · obtain ⟨n4, d4, u4⟩ := t3.taken hc3 0x156 bt_at_22 (by decide) (by
        show (!(reg n3 a4).ult (reg n3 a3)) = true
        rw [q3 a4 (by decide) (by decide), q3 a3 (by decide) (by decide), ha4, ha3]
        simp only [Bool.not_eq_true] at hl; rw [hl]; rfl)
      simp only [Bool.not_eq_true] at hl
      exact Or.inl ⟨n4, .single d4, ⟨u4.pc, rfl, fun _ => rfl⟩, fun x _ _ => by rw [u4.mem],
        fun j _ => by rw [u4.mem], fun j _ => by rw [u4.mem], Or.inr ⟨hl, by rw [u4.mem]; exact hw3⟩,
        ⟨0, by rw [u4.mem, hw3]; exact BitVec.or_zero.symm⟩, by rw [u4.regs]; exact sp3, by rw [u4.regs]; exact v20⟩
  have pre3 : Steps m n3 := .cons d1 (c2.trans c3)
  refine stage.elim (fun h => ?_) fun hp => Or.inr (.of_e1 (HaltsWith.of_steps pre3 hp))
  obtain ⟨n4, c4, t4, o4, fr4, fa4, hlev, hmono, sp4, w20⟩ := h
  -- the lock of the eFuse and flash registers, to 0x18C
  have hiOf : ∀ X, BtW n4.mem X → BtHi M0 X := fun X hW x h1 h2 => by
    rw [hW x (Or.inl (by omega)), o4 x (stkHi x h1) (Or.inl (by omega))]; exact o3 x (stkHi x h1)
  have hc4 := hiKeep C.code (hiOf _ (BtW.refl _)) (by decide) (by decide)
  obtain ⟨n5, c5, u5⟩ := t4.block btLk1 hc4 btLk1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, btLk1]
    simp +decide only [upd, ↓reduceIte, true_and, and_true]
    refine ⟨(sep_of_le (by decide) (by decide)).symm, ?_⟩
    rw [sp4]; exact (al 8 (by decide) (by decide)).1)
  have e5 : (runBlock btLk1 (n4.mem, reg n4)).1 = memStore32 n4.mem 0x600C1110 0x18002200 := by
    simp +decide only [runBlock, BInstr.run, btLk1, upd, ↓reduceIte]; rfl
  have r5 : ∀ r, reg n5 r = (runBlock btLk1 (n4.mem, reg n4)).2 r := fun r => by rw [u5.regs]
  have W5 : BtW n4.mem (memStore32 n4.mem 0x600C1110 0x18002200) := (BtW.refl _).store _ (by decide) (by decide)
  have hc5 := hiKeep C.code (hiOf _ W5) (by decide) (by decide)
  have t5 : St (memStore32 n4.mem 0x600C1110 0x18002200) BT n5 0x172 (reg n5) := ⟨u5.pc, u5.mem.trans e5, fun _ => rfl⟩
  have v1 : reg n5 a1 = 7 := by rw [r5]; simp +decide only [runBlock, BInstr.run, btLk1, upd, ↓reduceIte]
  obtain ⟨n6, d6, u6⟩ := t5.notTaken hc5 0x174 bt_at_172 (by decide) (by
    show (reg n5 a1 == reg n5 x0) = false; rw [v1, t5.zero]; rfl)
  obtain ⟨n7, c7, t7, W7, k7⟩ := bt_lock 0x18002400 7 (n := n6) 0x600C1114 ⟨u6.pc, by rw [u6.mem], fun _ => rfl⟩
    (by decide) (by rw [u6.regs]; exact v1)
    (by rw [u6.regs, r5]; simp +decide only [runBlock, BInstr.run, btLk1, upd, ↓reduceIte])
    (by rw [u6.regs, r5]; simp +decide only [runBlock, BInstr.run, btLk1, upd, ↓reduceIte])
    (by decide) (by decide) (by decide) (by rw [u6.mem]; exact hc5)
  rw [u6.mem] at W7
  have W7' := W5.trans W7
  have hc7 := hiKeep C.code (hiOf _ W7') (by decide) (by decide)
  have k7' : ∀ r, r ≠ a1 → r ≠ a2 → reg n7 r = (runBlock btLk1 (n4.mem, reg n4)).2 r := fun r h1 h2 => by
    rw [k7 r h1 h2, u6.regs, r5]
  have a07 : reg n7 a0 = 0x600C1000 := by
    rw [k7' a0 (by decide) (by decide)]; simp +decide only [runBlock, BInstr.run, btLk1, upd, ↓reduceIte]
  obtain ⟨n8, c8, u8⟩ := t7.block btLk2 hc7 btLk2_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, btLk2]
    simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [a07]
    exact ⟨by decide, ⟨by decide, (sep_of_le (by decide) (by decide)).symm⟩, by decide,
      (sep_of_le (by decide) (by decide)).symm⟩)
  obtain ⟨M5, hM5⟩ : ∃ M5, (runBlock btLk2 (n7.mem, reg n7)).1 = M5 := ⟨_, rfl⟩
  have W8 : BtW n7.mem M5 := by
    rw [← hM5]; simp +decide only [runBlock, BInstr.run, btLk2, upd, ↓reduceIte]; rw [a07]
    exact ((BtW.refl _).store _ (by decide) (by decide)).store _ (by decide) (by decide)
  have t8 : St M5 BT n8 0x18C (reg n8) := ⟨u8.pc, u8.mem.trans hM5, fun _ => rfl⟩
  have k8 : ∀ r, r = sp ∨ r = 20 → reg n8 r = reg n4 r := fun r hr => by
    have h1 : r ≠ a1 := by rcases hr with rfl | rfl <;> decide
    have h2 : r ≠ a2 := by rcases hr with rfl | rfl <;> decide
    rw [u8.regs, runBlock_reg _ _ _ r t7.zero (by simp only [btLk2]; rcases hr with rfl | rfl <;> decide),
      k7' r h1 h2, runBlock_reg _ _ _ r t4.zero (by simp only [btLk1]; rcases hr with rfl | rfl <;> decide)]
  have w23 : reg n8 23 = acc := by
    rw [u8.regs, runBlock_reg _ _ _ 23 t7.zero (by decide), k7' 23 (by decide) (by decide)]
    simp +decide only [runBlock, BInstr.run, btLk1, upd, ↓reduceIte]
    rw [sp4, memLoad32_store32_sep (sep_of_le (by
      rw [hS8]; have h := C.hsph; unfold dramEnd at h
      have e : (0x600C1000 + 0x110 : Word).toNat = 0x600C1110 := rfl; omega) (by decide)).symm, ← f8]
    exact memLoad32_congr fun j hj => fa4 j hj
  -- the memory at 0x18C
  have W : BtW n4.mem M5 := W7'.trans W8
  have hO : ∀ x, Sep Ss (btK R romStack) x 1 → (x.toNat < 0x60000000 ∨ 0x600C4000 ≤ x.toNat) → M5 x = M0 x :=
    fun x hx hw => by
      rw [W x (hw.imp_left fun h => by omega), o4 x hx (hw.imp (fun h => by omega) fun h => by omega), o3 x hx]
  have hH5 : BtHi M0 M5 := fun x h1 h2 => hO x (stkHi x h1) (Or.inl h2)
  have hh5 : HdrEq M0 M5 acc := fun i hi =>
    (hO _ (tbl i hi) (Or.inl (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))).symm
  have hslot : memLoad32 M5 (top + 0xFFFFFFC0 + 4) = slot := by
    rw [← f4]; exact memLoad32_congr fun j hj => by
      have e : (top + 0xFFFFFFC0 + 4 + BitVec.ofNat 32 j).toNat < 0x60000000 := by
        rw [BitVec.toNat_add, hS4, BitVec.toNat_ofNat]; omega
      rw [W _ (Or.inl (by omega)), fr4 j hj]
  rcases bt_body (C.transfer hH5 hh5) hROM log suspend invalidate resume t8
      (by rw [k8 sp (by simp)]; exact sp4) w23 (by rw [k8 20 (by simp)]; exact w20) hslot with
    ⟨m', c', pc', a0', mem'⟩ | hp
  · rw [hSs] at mem'
    have wfin : memLoad32 m'.mem efuseRd = memLoad32 n4.mem efuseRd := memLoad32_congr fun j hj => by
      have e : (efuseRd + BitVec.ofNat 32 j).toNat = 0x6000883C + j := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, show efuseRd.toNat = 0x6000883C from rfl]; omega
      rw [mem' (efuseRd + BitVec.ofNat 32 j) (stkHi _ (by omega)),
        bt_bootMem_hi (C.transfer hH5 hh5) (efuseRd + BitVec.ofNat 32 j) (by omega) (by omega),
        W (efuseRd + BitVec.ofNat 32 j) (Or.inl (by omega))]
    rw [← wfin] at hlev hmono
    refine Or.inl ⟨m', pre3.trans (c4.trans (c5.trans (.cons d6 (c7.trans (c8.trans c'))))), ?_, a0', hlev,
      hmono, fun x hx hw => ?_⟩
    · rw [pc', memLoad32_congr (M' := M5) (M := M0) (b := acc + 0x100) fun i hi => by
        rw [show acc + 0x100 + BitVec.ofNat 32 i = acc + BitVec.ofNat 32 (0x100 + i) from add_ofNat_assoc acc 0x100 i]
        exact (hh5 _ (by omega)).symm]
    · rw [mem' x hx]
      exact (HdrEq.bootMem hh5 (O := fun x => Sep Ss (btK R romStack) x 1 ∧ (x.toNat < 0x60000000 ∨ 0x600C4000 ≤ x.toNat))
        (fun x hx => (hO x hx.1 hx.2).symm) (fun i hi => ⟨stkHi _ (by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (icacheCtrl1).toNat = 0x600C4004 from rfl]; omega),
          Or.inr (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (icacheCtrl1).toNat = 0x600C4004 from rfl]; omega)⟩)
        x ⟨hx, hw⟩).symm
  · exact Or.inr (.of_e2 (HaltsWith.of_steps (pre3.trans (c4.trans (c5.trans (.cons d6 (c7.trans c8))))) hp))

/-- `boot_correct_halt`, with its halts as `Panics`. -/
theorem boot_correct {flash : Nat → BitVec 8} {R romStack : Nat} {romBase : Word} {romCode : List Nat}
    (m : Machine) {slot acc imgf target level : Word}
    (C : BtCtx m.mem (reg m sp) acc imgf R romStack romBase romCode) (hROM : RomRead flash R romBase romCode)
    (hpc : m.pc = BT) (ha0 : reg m a0 = slot) (ha1 : reg m a1 = acc) (ha2 : reg m a2 = imgf)
    (ha3 : reg m a3 = target) (ha4 : reg m a4 = level)
    (log : RomFn romBase romCode 0x40000040 romStack fun _ => True)
    (suspend : RomFn romBase romCode 0x40000524 romStack fun _ => True)
    (invalidate : RomFn romBase romCode 0x400004D8 romStack fun _ => True)
    (resume : RomFn romBase romCode 0x40000528 romStack fun _ => True) :
    (∃ m', Steps m m' ∧ m'.pc = memLoad32 m.mem (acc + 0x100) &&& ~~~1 ∧ reg m' a0 = slot ∧
      ((btPop (memLoad32 m'.mem efuseRd)).ult target = false ∨
        (level.ult target = false ∧ memLoad32 m'.mem efuseRd = memLoad32 m.mem efuseRd)) ∧
      (∃ X, memLoad32 m'.mem efuseRd = memLoad32 m.mem efuseRd ||| X) ∧
      ∀ x, Sep (reg m sp - BitVec.ofNat 32 (btK R romStack)) (btK R romStack) x 1 →
        (x.toNat < 0x60000000 ∨ 0x600C4000 ≤ x.toNat) → m'.mem x = bootMem flash m.mem acc imgf x) ∨
      Panics m :=
  (boot_correct_halt m C hROM hpc ha0 ha1 ha2 ha3 ha4 log suspend invalidate resume).imp_right
    HaltsDeliberately.panics

end C3.RV32.Cur
