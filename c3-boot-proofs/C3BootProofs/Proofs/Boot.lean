import C3BootProofs.Proofs.BootSpec

/-!
# `c3_bootloader::boot`

`boot_correct` covers the compiled `boot` from entry to the jump into the
application, given the ROM contracts `RomRead` (flash reads) and `RomFn`
(the log and the three cache routines it calls).
-/

namespace C3.RV32.Cur

open C3.Image

def btPs : List (Fin 32 × Word) :=
  [(ra, 0x2C), (8, 0x28), (9, 0x24), (18, 0x20), (19, 0x1C), (20, 0x18), (21, 0x14), (22, 0x10), (23, 0xC),
   (24, 0x8)]

def btPro : List BInstr :=
  [.sw sp ra 0x2C, .sw sp (8 : Fin 32) 0x28, .sw sp (9 : Fin 32) 0x24, .sw sp (18 : Fin 32) 0x20,
   .sw sp (19 : Fin 32) 0x1C, .sw sp (20 : Fin 32) 0x18, .sw sp (21 : Fin 32) 0x14, .sw sp (22 : Fin 32) 0x10,
   .sw sp (23 : Fin 32) 0xC, .sw sp (24 : Fin 32) 0x8]

theorem btPro_eq : btPro = saveBlock btPs := rfl

theorem btPro_end : blockEnd bootFnCode 0x2 btPro = some 0x16 :=
  (blockEnd_cons' (off' := 0x4) bt_at_2 rfl (blockEnd_cons' (off' := 0x6) bt_at_4 rfl (blockEnd_cons' (off' := 0x8) bt_at_6 rfl (blockEnd_cons' (off' := 0xA) bt_at_8 rfl (blockEnd_cons' (off' := 0xC) bt_at_a rfl (blockEnd_cons' (off' := 0xE) bt_at_c rfl (blockEnd_cons' (off' := 0x10) bt_at_e rfl (blockEnd_cons' (off' := 0x12) bt_at_10 rfl (blockEnd_cons' (off' := 0x14) bt_at_12 rfl (blockEnd_cons' (off' := 0x16) bt_at_14 rfl rfl))))))))))

def btMv : List BInstr := [.alu .add (21 : Fin 32) x0 a2, .alu .add (20 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0]

theorem btMv_end : blockEnd bootFnCode 0x16 btMv = some 0x1C :=
  (blockEnd_cons' (off' := 0x18) bt_at_16 rfl (blockEnd_cons' (off' := 0x1A) bt_at_18 rfl (blockEnd_cons' (off' := 0x1C) bt_at_1a rfl rfl)))

def btRaise : List BInstr := [.lui a0 0x3FCC4000, .aluImm .add a0 a0 0x198, .alu .add a1 x0 a3]

theorem btRaise_end : blockEnd bootFnCode 0x20 btRaise = some 0x2A :=
  (blockEnd_cons' (off' := 0x24) bt_at_20 rfl (blockEnd_cons' (off' := 0x28) bt_at_24 rfl (blockEnd_cons' (off' := 0x2A) bt_at_28 rfl rfl)))

def btCnt : List BInstr := [.aluImm .add a2 x0 0x10, .aluImm .sltu a1 a0 0x11, .alu .add (24 : Fin 32) x0 (20 : Fin 32)]

theorem btCnt_end : blockEnd bootFnCode 0x36 btCnt = some 0x3E :=
  (blockEnd_cons' (off' := 0x38) bt_at_36 rfl (blockEnd_cons' (off' := 0x3C) bt_at_38 rfl (blockEnd_cons' (off' := 0x3E) bt_at_3c rfl rfl)))

def btSet : List BInstr :=
  [.alu .sub a1 x0 a1, .alu .and a0 a0 a1, .aluImm .sll (8 : Fin 32) a0 0x4, .aluImm .add (19 : Fin 32) x0 0x2,
   .alu .add (22 : Fin 32) (24 : Fin 32) (8 : Fin 32), .lui (23 : Fin 32) 0xFF900000, .alu .add (9 : Fin 32) x0 (24 : Fin 32)]

theorem btSet_end : blockEnd bootFnCode 0x44 btSet = some 0x5A :=
  (blockEnd_cons' (off' := 0x48) bt_at_44 rfl (blockEnd_cons' (off' := 0x4A) bt_at_48 rfl (blockEnd_cons' (off' := 0x4E) bt_at_4a rfl (blockEnd_cons' (off' := 0x50) bt_at_4e rfl (blockEnd_cons' (off' := 0x54) bt_at_50 rfl (blockEnd_cons' (off' := 0x58) bt_at_54 rfl (blockEnd_cons' (off' := 0x5A) bt_at_58 rfl rfl)))))))

def btSusp : List BInstr := [.lui (8 : Fin 32) 0x600C5000, .aluImm .add (9 : Fin 32) x0 0x80]

theorem btSusp_end : blockEnd bootFnCode 0x88 btSusp = some 0x90 :=
  (blockEnd_cons' (off' := 0x8C) bt_at_88 rfl (blockEnd_cons' (off' := 0x90) bt_at_8c rfl rfl))

def btInv0 : List BInstr := [.alu .add (19 : Fin 32) x0 a0, .aluImm .add a0 x0 0x100]

theorem btInv0_end : blockEnd bootFnCode 0x98 btInv0 = some 0x9E :=
  (blockEnd_cons' (off' := 0x9A) bt_at_98 rfl (blockEnd_cons' (off' := 0x9E) bt_at_9a rfl rfl))

def btMap0 : List BInstr := [.aluImm .add a0 x0 0x2, .lui (9 : Fin 32) 0x600C5000, .aluImm .add a2 x0 0x7F]

theorem btMap0_end : blockEnd bootFnCode 0xA8 btMap0 = some 0xB2 :=
  (blockEnd_cons' (off' := 0xAA) bt_at_a8 rfl (blockEnd_cons' (off' := 0xAE) bt_at_aa rfl (blockEnd_cons' (off' := 0xB2) bt_at_ae rfl rfl)))

def btBus : List BInstr := [.lui a0 0x600C4000, .lw a1 a0 0x4, .aluImm .and a1 a1 0xFFFFFFFC, .sw a0 a1 0x4]

theorem btBus_end : blockEnd bootFnCode 0x100 btBus = some 0x10A :=
  (blockEnd_cons' (off' := 0x104) bt_at_100 rfl (blockEnd_cons' (off' := 0x106) bt_at_104 rfl (blockEnd_cons' (off' := 0x108) bt_at_106 rfl (blockEnd_cons' (off' := 0x10A) bt_at_108 rfl rfl))))

def btJmp : List BInstr := [.lw (8 : Fin 32) (20 : Fin 32) 0x100, .lui a0 0x3FCC4000, .aluImm .add a0 a0 0x14E, .alu .add a1 x0 (8 : Fin 32)]

theorem btJmp_end : blockEnd bootFnCode 0x11C btJmp = some 0x12A :=
  (blockEnd_cons' (off' := 0x120) bt_at_11c rfl (blockEnd_cons' (off' := 0x124) bt_at_120 rfl (blockEnd_cons' (off' := 0x128) bt_at_124 rfl (blockEnd_cons' (off' := 0x12A) bt_at_128 rfl rfl))))

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 20000 in
/-- **The compiled `c3_bootloader::boot`.** Called with the slot index in
`a0`, the accepted header at `acc` in `a1`, the image's flash address in
`a2`, and the security levels in `a3` and `a4`, under `BtCtx`, it either
halts (`Panics`, when a flash read fails) or jumps to the header's entry
point with the slot index in `a0`. At the jump, memory outside its stack
is `bootMem`: each RAM segment copied from flash, the MMU table mapping
each flash segment, and both cache buses enabled. -/
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
      ∀ x, Sep (reg m sp - BitVec.ofNat 32 (btK R romStack)) (btK R romStack) x 1 →
        m'.mem x = bootMem flash m.mem acc imgf x) ∨ Panics m := by
  obtain ⟨top, htop⟩ : ∃ top, reg m sp = top := ⟨_, rfl⟩
  rw [htop] at C ⊢
  obtain ⟨M0, hM0⟩ : ∃ M0, m.mem = M0 := ⟨_, rfl⟩
  rw [hM0] at C ⊢
  have hKv : btK R romStack = 0x30 + 16 + R + romStack := rfl
  have hspl := C.hspl; have hsph := C.hsph; have h16 := C.hsp; have hR4 := C.hR
  rw [hKv] at hspl; unfold dramEnd at hsph
  obtain ⟨Ss, hSs⟩ : ∃ Ss, top - BitVec.ofNat 32 (btK R romStack) = Ss := ⟨_, rfl⟩
  rw [hSs]
  have sAS := C.sAS; rw [hSs] at sAS
  have hSn : Ss.toNat = top.toNat - btK R romStack := by
    rw [← hSs, BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]; omega
  have hsp1 : (top + 0xFFFFFFD0).toNat = top.toNat - 0x30 := by
    rw [BitVec.toNat_add, show (0xFFFFFFD0 : Word).toNat = 2 ^ 32 - 0x30 from rfl]; omega
  -- the stack region
  have stk : ∀ c l, c + l ≤ 0x30 → ∀ x, Sep Ss (btK R romStack) x 1 → Sep (top + 0xFFFFFFD0 + BitVec.ofNat 32 c) l x 1 :=
    fun c l h x hx => by
      have e : top + 0xFFFFFFD0 + BitVec.ofNat 32 c = Ss + BitVec.ofNat 32 (16 + R + romStack + c) :=
        BitVec.eq_of_toNat_eq (by
          rw [BitVec.toNat_add (top + 0xFFFFFFD0), hsp1, BitVec.toNat_add Ss, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hSn, hKv]; omega)
      rw [e]; exact hx.sub (by rw [hKv]; omega)
  have romS : ∀ x, Sep Ss (btK R romStack) x 1 → Sep (top + 0xFFFFFFD0 - BitVec.ofNat 32 romStack) romStack x 1 :=
    fun x hx => by
      have e : top + 0xFFFFFFD0 - BitVec.ofNat 32 romStack = Ss + BitVec.ofNat 32 (16 + R) :=
        BitVec.eq_of_toNat_eq (by
          rw [BitVec.toNat_sub, hsp1, BitVec.toNat_add Ss, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hSn, hKv]; omega)
      rw [e]; exact hx.sub (by rw [hKv]; omega)
  have stkHi : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep Ss (btK R romStack) x 1 := fun x hx =>
    sep_of_le (by rw [hSn, hKv]; omega) (by have := x.isLt; omega)
  have tbl : ∀ i, i < 0x10C → Sep Ss (btK R romStack) (acc + BitVec.ofNat 32 i) 1 := fun i hi =>
    (sAS.sub (c := i) (l := 1) (by omega)).symm
  -- a call to a ROM routine that keeps memory outside its stack
  have romcall : ∀ (F : Word) (n : Machine) (g : Fin 32 → Word) (off : Nat) (imm o : Word),
      RomFn romBase romCode F romStack (fun _ => True) → St n.mem BT n off g → g sp = top + 0xFFFFFFD0 →
      BtHi M0 n.mem →
      fetchRel bootFnCode off = some (.auipc ra imm, 4) → fetchRel bootFnCode (off + 4) = some (.jalr ra ra o, 4) →
      BT + BitVec.ofNat 32 off + imm + o = F → F.toNat % 2 = 0 → (BT + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0 →
      ∃ n', Steps n n' ∧ St n'.mem BT n' (off + 8) (reg n') ∧
        (∀ x, Sep Ss (btK R romStack) x 1 → n'.mem x = n.mem x) ∧ BtHi M0 n'.mem ∧
        ∀ q, romKeep q = true → reg n' q = g q := by
    intro F n g off imm o hF s hgs hH h1 h2 hb he he8
    obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (hiKeep C.code hH (by decide) (by decide)) h1 h2 hb he
    have sp1 : reg n1 sp = top + 0xFFFFFFD0 := by rw [regs1, updz s.zero (by decide)]; exact hgs
    obtain ⟨n2, c2, pc2, keep2, mem2⟩ := hF n1 (by rw [mem1]; exact hiKeep C.rom hH C.hrb C.hrl) pc1 trivial
      (by rw [sp1, hsp1]; omega)
    have fr : ∀ x, Sep Ss (btK R romStack) x 1 → n2.mem x = n.mem x := fun x hx => by
      rw [mem2 x (by rw [sp1]; exact romS x hx), mem1]
    refine ⟨n2, c1.trans c2, ⟨?_, rfl, fun _ => rfl⟩, fr, fun x h1 h2 => by rw [fr x (stkHi x h1)]; exact hH x h1 h2,
      fun q hq => ?_⟩
    · rw [pc2, regs1]; simp +decide only [upd, ite_true, ite_false]; exact even_clear _ he8
    · rw [keep2 q hq, regs1]; exact updz s.zero (by rintro rfl; exact absurd hq (by decide))
  -- the prologue
  have s0 : St M0 BT m 0 (reg m) := ⟨by rw [hpc]; rfl, hM0, fun _ => rfl⟩
  have hc0 := C.code
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc0 bt_at_0 (off' := 2) (by decide)
  rw [htop, show aluEval .add top 0xFFFFFFD0 = top + 0xFFFFFFD0 from rfl] at u1
  have g1sp : upd (reg m) sp (top + 0xFFFFFFD0) sp = top + 0xFFFFFFD0 := by simp +decide [upd]
  obtain ⟨n2, c2, u2⟩ := u1.block btPro hc0 btPro_end (by
    rw [btPro_eq]
    refine saveBlock_ok _ _ _ fun p hp => ?_
    rw [g1sp]
    simp only [btPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    have al : ∀ c : Word, c.toNat + 4 ≤ 0x30 → c.toNat % 4 = 0 →
        (top + 0xFFFFFFD0 + c).toNat % 4 = 0 ∧ Sep (top + 0xFFFFFFD0 + c) 4 BT bootFnCode.length := fun c h1 h2 => by
      have e : (top + 0xFFFFFFD0 + c).toNat = top.toNat - 0x30 + c.toNat := by
        rw [BitVec.toNat_add, hsp1]; omega
      exact ⟨by rw [e]; omega, sep_of_le (by rw [e, show BT.toNat = (img% bootFnAddress) from rfl]; omega) (by decide)⟩
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact al _ (by decide) (by decide))
  have hr2 : runBlock btPro (M0, upd (reg m) sp (top + 0xFFFFFFD0)) =
      (saveMem M0 (top + 0xFFFFFFD0) (upd (reg m) sp (top + 0xFFFFFFD0)) btPs, upd (reg m) sp (top + 0xFFFFFFD0)) := by
    rw [btPro_eq, saveBlock_run, g1sp]
  rw [hr2] at u2
  obtain ⟨M2, hM2⟩ : ∃ M2, saveMem M0 (top + 0xFFFFFFD0) (upd (reg m) sp (top + 0xFFFFFFD0)) btPs = M2 := ⟨_, rfl⟩
  rw [hM2] at u2
  have o2 : ∀ x, Sep Ss (btK R romStack) x 1 → M2 x = M0 x := fun x hx => by
    rw [← hM2]; refine saveMem_sep _ fun p hp => ?_
    simp only [btPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact stk _ 4 (by decide) x hx
  have hH2 : BtHi M0 M2 := fun x h1 _ => o2 x (stkHi x h1)
  have hc2 := hiKeep C.code hH2 (by decide) (by decide)
  obtain ⟨n3, c3, u3⟩ := u2.block btMv hc2 btMv_end ⟨trivial, trivial, trivial, trivial⟩
  have t3 : St M2 BT n3 0x1C (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  have r3 : ∀ r, reg n3 r = (runBlock btMv (M2, upd (reg m) sp (top + 0xFFFFFFD0))).2 r := fun r => by rw [u3.regs]
  have hz := s0.zero
  have q3 : ∀ r, r ≠ sp → r ≠ 18 → r ≠ 20 → r ≠ 21 → reg n3 r = reg m r := fun r h1 h2 h3 h4 => by
    rw [r3, runBlock_reg _ _ _ r (by simp [upd]) (by simp only [btMv]; revert h2 h3 h4; revert r; decide)]
    exact updz hz h1
  have sp3 : reg n3 sp = top + 0xFFFFFFD0 := by
    rw [r3, runBlock_reg _ _ _ sp (by simp [upd]) (by decide)]; exact g1sp
  have v18 : reg n3 18 = slot := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, btMv, upd, ↓reduceIte]; rw [ha0]; exact BitVec.zero_add _
  have v20 : reg n3 20 = acc := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, btMv, upd, ↓reduceIte]; rw [ha1]; exact BitVec.zero_add _
  have v21 : reg n3 21 = imgf := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, btMv, upd, ↓reduceIte]; rw [ha2]; exact BitVec.zero_add _
  -- raise's log when `target` is above `level`, then 0x32
  obtain ⟨n5, c5, t5, o5, hH5, k5⟩ : ∃ n5, Steps n3 n5 ∧ St n5.mem BT n5 0x32 (reg n5) ∧
      (∀ x, Sep Ss (btK R romStack) x 1 → n5.mem x = M2 x) ∧ BtHi M0 n5.mem ∧
      ∀ q, romKeep q = true → reg n5 q = reg n3 q := by
    by_cases hl : (reg n3 a4).ult (reg n3 a3) = true
    · obtain ⟨n4, d4, u4⟩ := t3.notTaken hc2 0x20 bt_at_1c (by decide) (by
        show (!(reg n3 a4).ult (reg n3 a3)) = false; rw [hl]; rfl)
      have t4 : St M2 BT n4 0x20 (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
      obtain ⟨n5, c5, u5⟩ := t4.block btRaise hc2 btRaise_end ⟨trivial, trivial, trivial, trivial⟩
      have t5 : St n5.mem BT n5 0x2A (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
      have m5 : n5.mem = M2 := u5.mem
      have k45 : ∀ r, r ≠ a0 → r ≠ a1 → reg n5 r = reg n3 r := fun r h0 h1 => by
        rw [u5.regs, runBlock_reg _ _ _ r t4.zero (by simp only [btRaise]; revert h0 h1; revert r; decide), u4.regs]
      obtain ⟨n6, c6, t6, o6, hH6, k6⟩ := romcall 0x40000040 n5 (reg n5) 0x2A _ _ log t5
        (by rw [k45 sp (by decide) (by decide)]; exact sp3) (by rw [m5]; exact hH2) bt_at_2a bt_at_2e
        (by decide) (by decide) (by decide)
      refine ⟨n6, .cons d4 (c5.trans c6), t6, fun x hx => by rw [o6 x hx, m5], hH6, fun q hq => ?_⟩
      rw [k6 q hq, k45 q (by rintro rfl; exact absurd hq (by decide)) (by rintro rfl; exact absurd hq (by decide))]
    · obtain ⟨n4, d4, u4⟩ := t3.taken hc2 0x32 bt_at_1c (by decide) (by
        show (!(reg n3 a4).ult (reg n3 a3)) = true; simp only [Bool.not_eq_true] at hl; rw [hl]; rfl)
      exact ⟨n4, .single d4, ⟨u4.pc, rfl, fun _ => rfl⟩, fun x _ => by rw [u4.mem], by rw [u4.mem]; exact hH2,
        fun q _ => by rw [u4.regs]⟩
  have sp5 : reg n5 sp = top + 0xFFFFFFD0 := by rw [k5 sp (by decide)]; exact sp3
  have w18 : reg n5 18 = slot := by rw [k5 18 (by decide)]; exact v18
  have w20 : reg n5 20 = acc := by rw [k5 20 (by decide)]; exact v20
  have w21 : reg n5 21 = imgf := by rw [k5 21 (by decide)]; exact v21
  have o5' : ∀ x, Sep Ss (btK R romStack) x 1 → n5.mem x = M0 x := fun x hx => by rw [o5 x hx, o2 x hx]
  have hacc := C.hacc; have haccl := C.haccl
  have hc5 := hiKeep C.code hH5 (by decide) (by decide)
  -- the segment count
  obtain ⟨cw, hcw⟩ : ∃ cw, memLoad32 M0 (acc + 0x108) = cw := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, sgCount M0 acc = N := ⟨_, rfl⟩
  have hNv : N = if cw.toNat ≤ 16 then cw.toNat else 0 := by rw [← hN, ← hcw]; rfl
  have hN16 : N ≤ 16 := by rw [← hN]; exact sgCount_le M0 acc
  obtain ⟨n6, d6, u6⟩ := t5.lw hc5 bt_at_32 (off' := 0x36) (by decide)
    (by rw [w20, BitVec.toNat_add]; simp; omega)
  have t6 := u6.self
  have v0 : reg n6 a0 = cw := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]; rw [w20, ← hcw]
    exact memLoad32_congr fun i hi => by
      rw [show acc + 0x108 + BitVec.ofNat 32 i = acc + BitVec.ofNat 32 (0x108 + i) from add_ofNat_assoc acc 0x108 i]
      exact o5' _ (tbl _ (by omega))
  have k6 : ∀ r, r ≠ a0 → reg n6 r = reg n5 r := fun r h => by rw [u6.regs]; exact updz t5.zero h
  obtain ⟨n7, c7, u7⟩ := t6.block btCnt hc5 btCnt_end ⟨trivial, trivial, trivial, trivial⟩
  have t7 : St n5.mem BT n7 0x3E (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
  have r7 : ∀ r, reg n7 r = (runBlock btCnt (n5.mem, reg n6)).2 r := fun r => by rw [u7.regs]
  have e2 : reg n7 a2 = 16 := by rw [r7]; simp +decide only [runBlock, BInstr.run, btCnt, upd, ↓reduceIte]; rw [t6.zero]; rfl
  have e0 : reg n7 a0 = cw := by rw [r7, runBlock_reg _ _ _ a0 t6.zero (by decide)]; exact v0
  have e1 : reg n7 a1 = aluEval .sltu cw 0x11 := by
    rw [r7]; simp +decide only [runBlock, BInstr.run, btCnt, upd, ↓reduceIte]; rw [v0]
  have e24 : reg n7 24 = acc := by
    rw [r7]; simp +decide only [runBlock, BInstr.run, btCnt, upd, ↓reduceIte]
    rw [k6 20 (by decide), w20]; exact BitVec.zero_add _
  have k7 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ 24 → reg n7 r = reg n5 r := fun r h0 h1 h2 h24 => by
    rw [r7, runBlock_reg _ _ _ r t6.zero (by simp only [btCnt]; revert h1 h2 h24; revert r; decide), k6 r h0]
  -- the clamp: `s8` is the header when the count is at most 16
  obtain ⟨n8, c8, t8, P0, y24, hP0, k8⟩ : ∃ n8, Steps n7 n8 ∧ St n5.mem BT n8 0x44 (reg n8) ∧ ∃ P0,
      reg n8 24 = P0 ∧ (cw.toNat ≤ 16 → P0 = acc) ∧ ∀ r, r ≠ 24 → reg n8 r = reg n7 r := by
    by_cases hc : cw.toNat ≤ 16
    · obtain ⟨n8, d8, u8⟩ := t7.taken hc5 0x44 bt_at_3e (by decide) (by
        show (!(reg n7 a2).ult (reg n7 a0)) = true
        rw [e2, e0]; simp only [BitVec.ult]; rw [show (16 : Word).toNat = 16 from rfl]
        rw [decide_eq_false (show ¬ 16 < cw.toNat by omega)]; rfl)
      exact ⟨n8, .single d8, ⟨u8.pc, u8.mem, fun _ => rfl⟩, acc, by rw [u8.regs]; exact e24, fun _ => rfl,
        fun r _ => by rw [u8.regs]⟩
    · obtain ⟨n8, d8, u8⟩ := t7.notTaken hc5 0x42 bt_at_3e (by decide) (by
        show (!(reg n7 a2).ult (reg n7 a0)) = false
        rw [e2, e0]; simp only [BitVec.ult]; rw [show (16 : Word).toNat = 16 from rfl]
        rw [decide_eq_true (show 16 < cw.toNat by omega)]; rfl)
      have t8 : St n5.mem BT n8 0x42 (reg n8) := ⟨u8.pc, u8.mem, fun _ => rfl⟩
      obtain ⟨n9, d9, u9⟩ := t8.aluImm hc5 bt_at_42 (off' := 0x44) (by decide)
      exact ⟨n9, .cons d8 (.single d9), ⟨u9.pc, u9.mem, fun _ => rfl⟩, _, rfl, fun h => absurd h hc,
        fun r h => by rw [u9.regs, updz t8.zero h, u8.regs]⟩
  obtain ⟨n9, c9, u9⟩ := t8.block btSet hc5 btSet_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have t9 : St n5.mem BT n9 0x5A (reg n9) := ⟨u9.pc, u9.mem, fun _ => rfl⟩
  have r9 : ∀ r, reg n9 r = (runBlock btSet (n5.mem, reg n8)).2 r := fun r => by rw [u9.regs]
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
    rw [r9]; simp +decide only [runBlock, BInstr.run, btSet, upd, ↓reduceIte]; rw [y24]; exact BitVec.zero_add _
  have z24 : reg n9 24 = P0 := by rw [r9, runBlock_reg _ _ _ 24 t8.zero (by decide)]; exact y24
  have z22 : reg n9 22 = P0 + BitVec.ofNat 32 (16 * N) := by
    rw [r9]; simp +decide only [runBlock, BInstr.run, btSet, upd, ↓reduceIte]; rw [g0, g1, t8.zero, hmask, shl4, y24]; rfl
  have z19 : reg n9 19 = 2 := by
    rw [r9]; simp +decide only [runBlock, BInstr.run, btSet, upd, ↓reduceIte]; (try rw [t8.zero]); try rfl
  have z23 : reg n9 23 = 0xFF900000 := by rw [r9]; simp +decide only [runBlock, BInstr.run, btSet, upd, ↓reduceIte]
  have k9 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ 8 → r ≠ 9 → r ≠ 19 → r ≠ 22 → r ≠ 23 → r ≠ 24 → reg n9 r = reg n5 r :=
    fun r h0 h1 h2 h8 h9 h19 h22 h23 h24 => by
      rw [r9, runBlock_reg _ _ _ r t8.zero (by simp only [btSet]; revert h0 h1 h8 h9 h19 h22 h23; revert r; decide),
        k8 r h24, k7 r h0 h1 h2 h24]
  -- the RAM copies, to 0x88
  have stage88 : (∃ n10, Steps n9 n10 ∧ St n10.mem BT n10 0x88 (reg n10) ∧ BtHi M0 n10.mem ∧
      (∀ x, Sep Ss (btK R romStack) x 1 → n10.mem x = ramLoad flash M0 acc imgf N x) ∧
      ∀ r, romKeep r = true → r ≠ 8 → r ≠ 9 → reg n10 r = reg n9 r) ∨ Panics n9 := by
    by_cases hN0 : N = 0
    · obtain ⟨n10, d10, u10⟩ := t9.taken hc5 0x88 bt_at_5a (by decide) (by
        show (reg n9 8 == reg n9 x0) = true; rw [z8, t9.zero, hN0]; rfl)
      exact Or.inl ⟨n10, .single d10, ⟨u10.pc, rfl, fun _ => rfl⟩, by rw [u10.mem]; exact hH5,
        fun x hx => by rw [u10.mem, o5' x hx, hN0]; rfl, fun r _ _ _ => by rw [u10.regs]⟩
    · obtain ⟨n10, d10, u10⟩ := t9.notTaken hc5 0x5C bt_at_5a (by decide) (by
        show (reg n9 8 == reg n9 x0) = false; rw [z8, t9.zero]
        exact decide_eq_false fun e => hN0 (by
          have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          simp at this; omega))
      have hcw : cw.toNat ≤ 16 := by
        by_cases h : cw.toNat ≤ 16
        · exact h
        · rw [hNv, ite_eq_right h] at hN0; exact absurd rfl hN0
      have kk : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ 8 → r ≠ 9 → r ≠ 19 → r ≠ 22 → r ≠ 23 → r ≠ 24 → reg n10 r = reg n5 r :=
        fun r h0 h1 h2 h8 h9 h19 h22 h23 h24 => by rw [u10.regs]; exact k9 r h0 h1 h2 h8 h9 h19 h22 h23 h24
      rcases bt_copy C hROM N 0 (by rw [hN]; omega) (by rw [hN]; omega)
          (⟨u10.pc, rfl, fun _ => rfl⟩ : St n10.mem BT n10 0x5C (reg n10)) (by rw [u10.mem]; exact hH5)
          (fun x hx => by rw [u10.mem, o5' x (by rw [← hSs]; exact hx)]; rfl)
          (by rw [kk sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]; exact sp5)
          (by unfold sgPtr; rw [u10.regs, z9, hP0 hcw, Nat.mul_zero, add_ofNat_zero]) (by rw [u10.regs, z8, hN, Nat.sub_zero])
          (by rw [u10.regs]; exact z19) (by rw [u10.regs]; exact z23)
          (by rw [kk 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]; exact w21) with ⟨n', c', s', hH', o', k'⟩ | hp
      · rw [hN, hSs] at o'
        exact Or.inl ⟨n', .cons d10 c', s', hH', o', fun r hr h8 h9 => by rw [k' r hr h8 h9, u10.regs]⟩
      · exact Or.inr (Panics.of_steps (.single d10) hp)
  have pre9 : Steps m n9 := .cons d1 (c2.trans (c3.trans (c5.trans (.cons d6 (c7.trans (c8.trans c9))))))
  refine stage88.elim (fun h => ?_) fun hp => Or.inr (Panics.of_steps pre9 hp)
  obtain ⟨n10, c10, t10, hH10, o10, k10⟩ := h
  have q10 : ∀ r, r = sp ∨ r = 18 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 24 → reg n10 r = reg n9 r := fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact k10 _ (by decide) (by decide) (by decide)
  have sp10 : reg n10 sp = top + 0xFFFFFFD0 := by
    rw [q10 sp (by simp), k9 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact sp5
  have s18 : reg n10 18 = slot := by
    rw [q10 18 (by simp), k9 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact w18
  have s20 : reg n10 20 = acc := by
    rw [q10 20 (by simp), k9 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact w20
  have s21 : reg n10 21 = imgf := by
    rw [q10 21 (by simp), k9 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact w21
  have s22 : reg n10 22 = P0 + BitVec.ofNat 32 (16 * N) := by rw [q10 22 (by simp)]; exact z22
  have s24 : reg n10 24 = P0 := by rw [q10 24 (by simp)]; exact z24
  -- the registers `boot` still needs, through a step that keeps them
  have keepS : ∀ {n n' : Machine}, (∀ r, r = sp ∨ r = 18 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 24 → reg n' r = reg n r) →
      reg n sp = top + 0xFFFFFFD0 ∧ reg n 18 = slot ∧ reg n 20 = acc ∧ reg n 21 = imgf ∧
        reg n 22 = P0 + BitVec.ofNat 32 (16 * N) ∧ reg n 24 = P0 →
      reg n' sp = top + 0xFFFFFFD0 ∧ reg n' 18 = slot ∧ reg n' 20 = acc ∧ reg n' 21 = imgf ∧
        reg n' 22 = P0 + BitVec.ofNat 32 (16 * N) ∧ reg n' 24 = P0 := fun h ⟨h1, h2, h3, h4, h5, h6⟩ =>
    ⟨by rw [h sp (by simp)]; exact h1, by rw [h 18 (by simp)]; exact h2, by rw [h 20 (by simp)]; exact h3,
      by rw [h 21 (by simp)]; exact h4, by rw [h 22 (by simp)]; exact h5, by rw [h 24 (by simp)]; exact h6⟩
  have romK : ∀ r, r = sp ∨ r = 18 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 24 → romKeep r = true := fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have R10 := (⟨sp10, s18, s20, s21, s22, s24⟩ : reg n10 sp = top + 0xFFFFFFD0 ∧ reg n10 18 = slot ∧ reg n10 20 = acc ∧
    reg n10 21 = imgf ∧ reg n10 22 = P0 + BitVec.ofNat 32 (16 * N) ∧ reg n10 24 = P0)
  have hc10 := hiKeep C.code hH10 (by decide) (by decide)
  -- cache_suspend, then the 128 invalid entries
  obtain ⟨n11, c11, u11⟩ := t10.block btSusp hc10 btSusp_end ⟨trivial, trivial, trivial⟩
  have t11 : St n11.mem BT n11 0x90 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have r11 : ∀ r, reg n11 r = (runBlock btSusp (n10.mem, reg n10)).2 r := fun r => by rw [u11.regs]
  have R11 := keepS (n := n10) (n' := n11) (fun r hr => by
    rw [r11, runBlock_reg _ _ _ r t10.zero (by simp only [btSusp]; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]) R10
  have v11 : reg n11 9 = 0x80 := by rw [r11]; simp +decide only [runBlock, BInstr.run, btSusp, upd, ↓reduceIte]; (try rw [t10.zero]); try rfl
  obtain ⟨n12, c12, t12, o12, hH12, k12⟩ := romcall 0x40000524 n11 (reg n11) 0x90 _ _ suspend t11 R11.1
    (by rw [m11]; exact hH10) bt_at_90 bt_at_94 (by decide) (by decide) (by decide)
  have R12 := keepS (n := n11) (n' := n12) (fun r hr => k12 r (romK r hr)) R11
  have hc12 := hiKeep C.code hH12 (by decide) (by decide)
  obtain ⟨n13, c13, u13⟩ := t12.block btInv0 hc12 btInv0_end ⟨trivial, trivial, trivial⟩
  have t13 : St n12.mem BT n13 0x9E (reg n13) := ⟨u13.pc, u13.mem, fun _ => rfl⟩
  have r13 : ∀ r, reg n13 r = (runBlock btInv0 (n12.mem, reg n12)).2 r := fun r => by rw [u13.regs]
  have R13 := keepS (n := n12) (n' := n13) (fun r hr => by
    rw [r13, runBlock_reg _ _ _ r t12.zero (by simp only [btInv0]; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]) R12
  have v13 : reg n13 9 = 0x80 := by
    rw [r13, runBlock_reg _ _ _ 9 t12.zero (by decide), k12 9 (by decide)]; exact v11
  have a13 : reg n13 a0 = 0x100 := by rw [r13]; simp +decide only [runBlock, BInstr.run, btInv0, upd, ↓reduceIte]; (try rw [t12.zero]); try rfl
  have e13 : reg n13 8 = 0x600C5000 := by
    rw [r13, runBlock_reg _ _ _ 8 t12.zero (by decide), k12 8 (by decide), r11]
    simp +decide only [runBlock, BInstr.run, btSusp, upd, ↓reduceIte]
  obtain ⟨n14, d14, u14⟩ := t13.notTaken hc12 0xA0 bt_at_9e (by decide) (by
    show (reg n13 9 == reg n13 x0) = false; rw [v13, t13.zero]; rfl)
  have mi0 : mmuInv n12.mem 0 = n12.mem := funext fun x => by unfold mmuInv; rw [ite_eq_right (by omega)]
  obtain ⟨n15, c15, t15, k15⟩ := bt_inv hc12 128 0 (n := n14) rfl (by decide)
    (by rw [mi0]; exact ⟨u14.pc, u14.mem, fun _ => rfl⟩) (by rw [u14.regs, e13]; rfl) (by rw [u14.regs, v13]; rfl)
    (by rw [u14.regs]; exact a13)
  have R15 := keepS (n := n13) (n' := n15) (fun r hr => by
    rw [k15 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), u14.regs]) R13
  -- the agreement of the memory so far with the specification
  have hMx : ∀ x, Sep Ss (btK R romStack) x 1 → n12.mem x = ramLoad flash M0 acc imgf N x := fun x hx => by
    rw [o12 x hx, m11, o10 x hx]
  have hH15 : BtHi M0 (mmuInv n12.mem 128) := fun x h1 h2 => by
    unfold mmuInv; rw [ite_eq_right (by rw [BitVec.toNat_sub, show (mmuBase).toNat = 0x600C5000 from rfl]; omega)]
    exact hH12 x h1 h2
  have hc15 := hiKeep C.code hH15 (by decide) (by decide)
  obtain ⟨n16, c16, u16⟩ := t15.block btMap0 hc15 btMap0_end ⟨trivial, trivial, trivial, trivial⟩
  have t16 : St (mmuInv n12.mem 128) BT n16 0xB2 (reg n16) := ⟨u16.pc, u16.mem, fun _ => rfl⟩
  have r16 : ∀ r, reg n16 r = (runBlock btMap0 (mmuInv n12.mem 128, reg n15)).2 r := fun r => by rw [u16.regs]
  have R16 := keepS (n := n15) (n' := n16) (fun r hr => by
    rw [r16, runBlock_reg _ _ _ r t15.zero (by simp only [btMap0]; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]) R15
  -- the MMU entries, to 0x100
  have hT : ∀ i, i < 0x10C → mmuInv n12.mem 128 (acc + BitVec.ofNat 32 i) = M0 (acc + BitVec.ofNat 32 i) :=
    fun i hi => by
      have hlo : (acc + BitVec.ofNat 32 i).toNat < 0x40000000 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      unfold mmuInv; rw [ite_eq_right (by rw [BitVec.toNat_sub, show (mmuBase).toNat = 0x600C5000 from rfl]; omega)]
      rw [hMx _ (tbl i hi)]
      exact ramLoad_out _ N fun j hj hk => ((C.ram j (by rw [hN]; omega) hk).2.2.1.symm.sub (c := i) (l := 1) (by omega)).symm
  obtain ⟨n17, c17, t17, k17⟩ : ∃ n17, Steps n16 n17 ∧
      St (mmuMap M0 acc imgf (mmuInv n12.mem 128) N) BT n17 0x100 (reg n17) ∧
      ∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → r ≠ 24 → reg n17 r = reg n16 r := by
    by_cases hN0 : N = 0
    · subst hN0
      obtain ⟨n17, d17, u17⟩ := t16.taken hc15 0x100 bt_at_b2 (by decide) (by
        show (reg n16 24 == reg n16 22) = true
        rw [R16.2.2.2.2.2, R16.2.2.2.2.1, Nat.mul_zero, add_ofNat_zero]; exact decide_eq_true rfl)
      exact ⟨n17, .single d17, ⟨u17.pc, u17.mem, fun _ => rfl⟩, fun r _ _ _ _ _ _ => by rw [u17.regs]⟩
    · have hcw : cw.toNat ≤ 16 := by
        by_cases h : cw.toNat ≤ 16
        · exact h
        · rw [hNv, ite_eq_right h] at hN0; exact absurd rfl hN0
      have hbt : BT.toNat + bootFnCode.length ≤ 0x600C4000 := by decide
      obtain ⟨n17, c17, t17, k17⟩ := bt_map hbt hN16 hacc haccl (fun j hj => C.kind j (by rw [hN]; exact hj)) hT
        (hiKeep C.code hH15 (by decide) (by decide)) N 0 (by omega) (by omega) t16
        (by rw [R16.2.2.2.2.2, hP0 hcw]; unfold sgPtr; rw [Nat.mul_zero, add_ofNat_zero])
        (by rw [R16.2.2.2.2.1, hP0 hcw]; rfl)
        (by rw [r16]; simp +decide only [runBlock, BInstr.run, btMap0, upd, ↓reduceIte]; (try rw [t15.zero]); try rfl)
        (by rw [r16]; simp +decide only [runBlock, BInstr.run, btMap0, upd, ↓reduceIte]; (try rw [t15.zero]); try rfl)
        (by rw [r16]; simp +decide only [runBlock, BInstr.run, btMap0, upd, ↓reduceIte])
        R16.2.2.2.1
      exact ⟨n17, c17, t17, k17⟩
  have k17' : ∀ r, r = sp ∨ r = 18 ∨ r = 20 → reg n17 r = reg n16 r := fun r hr => by
    rcases hr with rfl | rfl | rfl <;> exact k17 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have sp17 : reg n17 sp = top + 0xFFFFFFD0 := by rw [k17' sp (by simp)]; exact R16.1
  have s18' : reg n17 18 = slot := by rw [k17' 18 (by simp)]; exact R16.2.1
  have s20' : reg n17 20 = acc := by rw [k17' 20 (by simp)]; exact R16.2.2.1
  -- both cache buses on
  obtain ⟨Mm, hMm⟩ : ∃ Mm, mmuMap M0 acc imgf (mmuInv n12.mem 128) N = Mm := ⟨_, rfl⟩
  rw [hMm] at t17
  have hHm : BtHi M0 Mm := fun x h1 h2 => by rw [← hMm, mmuMap_low N x h2]; exact hH15 x h1 h2
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
  have t18 : St n18.mem BT n18 0x10A (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have hHb : BtHi M0 n18.mem := fun x h1 h2 => by
    rw [m18]; unfold busOn; rw [st32_low Mm _ (by decide) (by decide) h2]; exact hHm x h1 h2
  obtain ⟨n19, c19, t19, o19, hH19, k19⟩ := romcall 0x400004D8 n18 (reg n18) 0x10A _ _ invalidate t18
    (by rw [q18 sp (by decide) (by decide)]; exact sp17) hHb bt_at_10a bt_at_10e (by decide) (by decide) (by decide)
  have hc19 := hiKeep C.code hH19 (by decide) (by decide)
  obtain ⟨n20, d20, u20⟩ := t19.alu hc19 bt_at_112 (off' := 0x114) (by decide)
  have t20 := u20.self
  have q20 : ∀ r, r ≠ a0 → reg n20 r = reg n19 r := fun r h => by rw [u20.regs]; exact updz t19.zero h
  obtain ⟨n21, c21, t21, o21, hH21, k21⟩ := romcall 0x40000528 n20 (reg n20) 0x114 _ _ resume
    (⟨t20.pc, rfl, fun _ => rfl⟩ : St n20.mem BT n20 0x114 (reg n20))
    (by rw [q20 sp (by decide), k19 sp (by decide), q18 sp (by decide) (by decide)]; exact sp17)
    (by rw [u20.mem]; exact hH19) bt_at_114 bt_at_118 (by decide) (by decide) (by decide)
  have keep21 : ∀ r, r = sp ∨ r = 18 ∨ r = 20 → reg n21 r = reg n17 r := fun r hr => by
    have hk : romKeep r = true := by rcases hr with rfl | rfl | rfl <;> decide
    have h0 : r ≠ a0 := by rcases hr with rfl | rfl | rfl <;> decide
    have h1 : r ≠ a1 := by rcases hr with rfl | rfl | rfl <;> decide
    rw [k21 r hk, q20 r h0, k19 r hk, q18 r h0 h1]
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
    simp only [BlockOk, BInstr.ok, BInstr.run, btJmp]
    simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [keep21 20 (by simp), s20', BitVec.toNat_add]; simp; omega)
  have t22 : St n22.mem BT n22 0x12A (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have r22 : ∀ r, reg n22 r = (runBlock btJmp (n21.mem, reg n21)).2 r := fun r => by rw [u22.regs]
  have e22 : reg n22 8 = memLoad32 M0 (acc + 0x100) := by
    rw [r22]; simp +decide only [runBlock, BInstr.run, btJmp, upd, ↓reduceIte]; rw [keep21 20 (by simp), s20', hent]
  have q22 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ 8 → reg n22 r = reg n21 r := fun r h0 h1 h8 => by
    rw [r22, runBlock_reg _ _ _ r t21.zero (by simp only [btJmp]; revert h0 h1 h8; revert r; decide)]
  obtain ⟨n23, c23, t23, o23, hH23, k23⟩ := romcall 0x40000040 n22 (reg n22) 0x12A _ _ log t22
    (by rw [q22 sp (by decide) (by decide) (by decide), keep21 sp (by simp)]; exact sp17) (by rw [m22]; exact hH21)
    bt_at_12a bt_at_12e (by decide) (by decide) (by decide)
  have hc23 := hiKeep C.code hH23 (by decide) (by decide)
  obtain ⟨n24, d24, u24⟩ := t23.alu hc23 bt_at_132 (off' := 0x134) (by decide)
  obtain ⟨n25, d25, pc25, mem25, regs25⟩ := u24.call hc23 bt_at_134
  refine Or.inl ⟨n25, pre9.trans (c10.trans (c11.trans (c12.trans (c13.trans (.cons d14 (c15.trans (c16.trans
    (c17.trans (c18.trans (c19.trans (.cons d20 (c21.trans (c22.trans (c23.trans (.cons d24 (.single d25)))))))))))))))),
    ?_, ?_, fun x hx => ?_⟩
  · rw [pc25]; simp +decide only [upd, ↓reduceIte]
    rw [k23 8 (by decide), e22, add_lit_zero]
  · rw [regs25]; simp +decide only [upd, ↓reduceIte]
    rw [k23 18 (by decide), q22 18 (by decide) (by decide) (by decide), keep21 18 (by simp)]
    rw [t23.zero]; exact (BitVec.zero_add _).trans s18'
  · rw [mem25, o23 x hx, m22, o21' x hx]
    unfold bootMem; rw [hN, ← hMm]
    refine busOn_agree (O := fun x => Sep Ss (btK R romStack) x 1)
      (mmuMap_agree (mmuInv_agree hMx 128) N) (fun i hi => stkHi _ ?_) x hx
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (icacheCtrl1).toNat = 0x600C4004 from rfl]; omega

end C3.RV32.Cur
