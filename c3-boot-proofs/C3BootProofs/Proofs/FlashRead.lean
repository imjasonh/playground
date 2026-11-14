import C3BootProofs.Proofs.Fe25519

/-!
# Flash reads

The bootloader reads flash only through the ROM's `esp_rom_spiflash_read`,
whose code is outside the image. `RomRead` states what the proofs assume it
does; the `boot-sim` lockstep runs check the same behavior against QEMU on
whole boots. `rom::flash_read_words` wraps the call, and `flash::read`
reads any byte range through a 256-byte bounce buffer.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem rfw_at_0 : fetchRel romFlashReadWordsCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem rfw_at_2 : fetchRel romFlashReadWordsCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem rfw_at_4 : fetchRel romFlashReadWordsCode 0x4 = some (.aluImm .sll a2 a2 0x2, 2) := by decide
theorem rfw_at_6 : fetchRel romFlashReadWordsCode 0x6 = some (.auipc ra 0xFFC5F000, 4) := by decide
theorem rfw_at_a : fetchRel romFlashReadWordsCode 0xA = some (.jalr ra ra 0xFFFFF9FA, 4) := by decide
theorem rfw_at_e : fetchRel romFlashReadWordsCode 0xE = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem rfw_at_12 : fetchRel romFlashReadWordsCode 0x12 = some (.load .lw ra sp 0xC, 2) := by decide
theorem rfw_at_14 : fetchRel romFlashReadWordsCode 0x14 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem rfw_at_16 : fetchRel romFlashReadWordsCode 0x16 = some (.jalr x0 ra 0x0, 2) := by decide

theorem frd_at_0 : fetchRel flashReadCode 0x0 = some (.aluImm .add sp sp 0xFFFFFEC0, 2) := by decide
theorem frd_at_2 : fetchRel flashReadCode 0x2 = some (.aluImm .add a3 sp 0x100, 2) := by decide
theorem frd_at_4 : fetchRel flashReadCode 0x4 = some (.store .sw a3 ra 0x3C, 4) := by decide
theorem frd_at_8 : fetchRel flashReadCode 0x8 = some (.store .sw a3 (8 : Fin 32) 0x38, 2) := by decide
theorem frd_at_a : fetchRel flashReadCode 0xA = some (.store .sw a3 (9 : Fin 32) 0x34, 2) := by decide
theorem frd_at_c : fetchRel flashReadCode 0xC = some (.store .sw a3 (18 : Fin 32) 0x30, 4) := by decide
theorem frd_at_10 : fetchRel flashReadCode 0x10 = some (.store .sw a3 (19 : Fin 32) 0x2C, 4) := by decide
theorem frd_at_14 : fetchRel flashReadCode 0x14 = some (.store .sw a3 (20 : Fin 32) 0x28, 4) := by decide
theorem frd_at_18 : fetchRel flashReadCode 0x18 = some (.store .sw a3 (21 : Fin 32) 0x24, 4) := by decide
theorem frd_at_1c : fetchRel flashReadCode 0x1C = some (.store .sw a3 (22 : Fin 32) 0x20, 4) := by decide
theorem frd_at_20 : fetchRel flashReadCode 0x20 = some (.store .sw a3 (23 : Fin 32) 0x1C, 4) := by decide
theorem frd_at_24 : fetchRel flashReadCode 0x24 = some (.store .sw a3 (24 : Fin 32) 0x18, 4) := by decide
theorem frd_at_28 : fetchRel flashReadCode 0x28 = some (.store .sw a3 (25 : Fin 32) 0x14, 4) := by decide
theorem frd_at_2c : fetchRel flashReadCode 0x2C = some (.store .sw a3 (26 : Fin 32) 0x10, 4) := by decide
theorem frd_at_30 : fetchRel flashReadCode 0x30 = some (.alu .add (21 : Fin 32) x0 a2, 2) := by decide
theorem frd_at_32 : fetchRel flashReadCode 0x32 = some (.alu .add (19 : Fin 32) x0 a1, 2) := by decide
theorem frd_at_34 : fetchRel flashReadCode 0x34 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem frd_at_36 : fetchRel flashReadCode 0x36 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem frd_at_38 : fetchRel flashReadCode 0x38 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem frd_at_3a : fetchRel flashReadCode 0x3A = some (.aluImm .add a2 x0 0x100, 4) := by decide
theorem frd_at_3e : fetchRel flashReadCode 0x3E = some (.aluImm .add (22 : Fin 32) sp 0xC, 4) := by decide
theorem frd_at_42 : fetchRel flashReadCode 0x42 = some (.aluImm .add (20 : Fin 32) x0 0x100, 4) := by decide
theorem frd_at_46 : fetchRel flashReadCode 0x46 = some (.auipc ra 0x13000, 4) := by decide
theorem frd_at_4a : fetchRel flashReadCode 0x4A = some (.jalr ra ra 0x58, 4) := by decide
theorem frd_at_4e : fetchRel flashReadCode 0x4E = some (.aluImm .add (23 : Fin 32) x0 0x0, 2) := by decide
theorem frd_at_50 : fetchRel flashReadCode 0x50 = some (.alu .add (9 : Fin 32) (19 : Fin 32) (21 : Fin 32), 4) := by decide
theorem frd_at_54 : fetchRel flashReadCode 0x54 = some (.aluImm .add (24 : Fin 32) x0 0xFF, 4) := by decide
theorem frd_at_58 : fetchRel flashReadCode 0x58 = some (.aluImm .add (25 : Fin 32) sp 0x10C, 4) := by decide
theorem frd_at_5c : fetchRel flashReadCode 0x5C = some (.branch .beq (21 : Fin 32) x0 0x88, 4) := by decide
theorem frd_at_60 : fetchRel flashReadCode 0x60 = some (.alu .add a0 (23 : Fin 32) (18 : Fin 32), 4) := by decide
theorem frd_at_64 : fetchRel flashReadCode 0x64 = some (.branch .bltu a0 (23 : Fin 32) 0x80, 4) := by decide
theorem frd_at_68 : fetchRel flashReadCode 0x68 = some (.aluImm .and (8 : Fin 32) a0 0x3, 4) := by decide
theorem frd_at_6c : fetchRel flashReadCode 0x6C = some (.alu .sub a1 (21 : Fin 32) (23 : Fin 32), 4) := by decide
theorem frd_at_70 : fetchRel flashReadCode 0x70 = some (.alu .sub (26 : Fin 32) (20 : Fin 32) (8 : Fin 32), 4) := by decide
theorem frd_at_74 : fetchRel flashReadCode 0x74 = some (.branch .bltu (26 : Fin 32) a1 0x6, 4) := by decide
theorem frd_at_78 : fetchRel flashReadCode 0x78 = some (.alu .add (26 : Fin 32) x0 a1, 2) := by decide
theorem frd_at_7a : fetchRel flashReadCode 0x7A = some (.alu .add a1 (26 : Fin 32) (8 : Fin 32), 4) := by decide
theorem frd_at_7e : fetchRel flashReadCode 0x7E = some (.aluImm .add a1 a1 0x3, 2) := by decide
theorem frd_at_80 : fetchRel flashReadCode 0x80 = some (.aluImm .srl a2 a1 0x2, 4) := by decide
theorem frd_at_84 : fetchRel flashReadCode 0x84 = some (.aluImm .and a0 a0 0xFFFFFFFC, 2) := by decide
theorem frd_at_86 : fetchRel flashReadCode 0x86 = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem frd_at_88 : fetchRel flashReadCode 0x88 = some (.auipc ra 0x0, 4) := by decide
theorem frd_at_8c : fetchRel flashReadCode 0x8C = some (.jalr ra ra 0xFFFFFF60, 4) := by decide
theorem frd_at_90 : fetchRel flashReadCode 0x90 = some (.branch .beq a0 x0 0x54, 2) := by decide
theorem frd_at_92 : fetchRel flashReadCode 0x92 = some (.alu .sub a0 x0 (26 : Fin 32), 4) := by decide
theorem frd_at_96 : fetchRel flashReadCode 0x96 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem frd_at_98 : fetchRel flashReadCode 0x98 = some (.alu .add a2 x0 (23 : Fin 32), 2) := by decide
theorem frd_at_9a : fetchRel flashReadCode 0x9A = some (.branch .beq a0 x0 0x44, 2) := by decide
theorem frd_at_9c : fetchRel flashReadCode 0x9C = some (.branch .bne a2 x0 0x14, 2) := by decide
theorem frd_at_9e : fetchRel flashReadCode 0x9E = some (.branch .beq a1 (9 : Fin 32) 0x40, 4) := by decide
theorem frd_at_a2 : fetchRel flashReadCode 0xA2 = some (.branch .bltu (24 : Fin 32) (8 : Fin 32) 0x1C, 4) := by decide
theorem frd_at_a6 : fetchRel flashReadCode 0xA6 = some (.aluImm .and a2 (8 : Fin 32) 0xFFFFFFFC, 4) := by decide
theorem frd_at_aa : fetchRel flashReadCode 0xAA = some (.alu .add a2 a2 (22 : Fin 32), 2) := by decide
theorem frd_at_ac : fetchRel flashReadCode 0xAC = some (.load .lw a3 a2 0x0, 2) := by decide
theorem frd_at_ae : fetchRel flashReadCode 0xAE = some (.jal x0 0x12, 2) := by decide
theorem frd_at_b0 : fetchRel flashReadCode 0xB0 = some (.alu .sub a3 (9 : Fin 32) a1, 4) := by decide
theorem frd_at_b4 : fetchRel flashReadCode 0xB4 = some (.branch .bgeu a2 a3 0x2A, 4) := by decide
theorem frd_at_b8 : fetchRel flashReadCode 0xB8 = some (.alu .add a1 a1 a2, 2) := by decide
theorem frd_at_ba : fetchRel flashReadCode 0xBA = some (.branch .bgeu (24 : Fin 32) (8 : Fin 32) 0xFFFFFFEC, 4) := by decide
theorem frd_at_be : fetchRel flashReadCode 0xBE = some (.aluImm .add a3 x0 0x0, 2) := by decide
theorem frd_at_c0 : fetchRel flashReadCode 0xC0 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem frd_at_c2 : fetchRel flashReadCode 0xC2 = some (.aluImm .and a4 (8 : Fin 32) 0x3, 4) := by decide
theorem frd_at_c6 : fetchRel flashReadCode 0xC6 = some (.store .sw sp a3 0x10C, 4) := by decide
theorem frd_at_ca : fetchRel flashReadCode 0xCA = some (.alu .or a3 (25 : Fin 32) a4, 4) := by decide
theorem frd_at_ce : fetchRel flashReadCode 0xCE = some (.load .lbu a3 a3 0x0, 4) := by decide
theorem frd_at_d2 : fetchRel flashReadCode 0xD2 = some (.store .sb a1 a3 0x0, 4) := by decide
theorem frd_at_d6 : fetchRel flashReadCode 0xD6 = some (.aluImm .add a1 a1 0x1, 2) := by decide
theorem frd_at_d8 : fetchRel flashReadCode 0xD8 = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem frd_at_da : fetchRel flashReadCode 0xDA = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x1, 2) := by decide
theorem frd_at_dc : fetchRel flashReadCode 0xDC = some (.branch .bne a0 x0 0xFFFFFFC0, 2) := by decide
theorem frd_at_de : fetchRel flashReadCode 0xDE = some (.alu .add (23 : Fin 32) (23 : Fin 32) (26 : Fin 32), 2) := by decide
theorem frd_at_e0 : fetchRel flashReadCode 0xE0 = some (.branch .bltu (23 : Fin 32) (21 : Fin 32) 0xFFFFFF80, 4) := by decide
theorem frd_at_e4 : fetchRel flashReadCode 0xE4 = some (.alu .sltu a0 (23 : Fin 32) (21 : Fin 32), 4) := by decide
theorem frd_at_e8 : fetchRel flashReadCode 0xE8 = some (.aluImm .xor a0 a0 0x1, 4) := by decide
theorem frd_at_ec : fetchRel flashReadCode 0xEC = some (.aluImm .add a1 sp 0x100, 2) := by decide
theorem frd_at_ee : fetchRel flashReadCode 0xEE = some (.load .lw ra a1 0x3C, 4) := by decide
theorem frd_at_f2 : fetchRel flashReadCode 0xF2 = some (.load .lw (8 : Fin 32) a1 0x38, 2) := by decide
theorem frd_at_f4 : fetchRel flashReadCode 0xF4 = some (.load .lw (9 : Fin 32) a1 0x34, 2) := by decide
theorem frd_at_f6 : fetchRel flashReadCode 0xF6 = some (.load .lw (18 : Fin 32) a1 0x30, 4) := by decide
theorem frd_at_fa : fetchRel flashReadCode 0xFA = some (.load .lw (19 : Fin 32) a1 0x2C, 4) := by decide
theorem frd_at_fe : fetchRel flashReadCode 0xFE = some (.load .lw (20 : Fin 32) a1 0x28, 4) := by decide
theorem frd_at_102 : fetchRel flashReadCode 0x102 = some (.load .lw (21 : Fin 32) a1 0x24, 4) := by decide
theorem frd_at_106 : fetchRel flashReadCode 0x106 = some (.load .lw (22 : Fin 32) a1 0x20, 4) := by decide
theorem frd_at_10a : fetchRel flashReadCode 0x10A = some (.load .lw (23 : Fin 32) a1 0x1C, 4) := by decide
theorem frd_at_10e : fetchRel flashReadCode 0x10E = some (.load .lw (24 : Fin 32) a1 0x18, 4) := by decide
theorem frd_at_112 : fetchRel flashReadCode 0x112 = some (.load .lw (25 : Fin 32) a1 0x14, 4) := by decide
theorem frd_at_116 : fetchRel flashReadCode 0x116 = some (.load .lw (26 : Fin 32) a1 0x10, 4) := by decide
theorem frd_at_11a : fetchRel flashReadCode 0x11A = some (.aluImm .add sp sp 0x140, 2) := by decide
theorem frd_at_11c : fetchRel flashReadCode 0x11C = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- The registers a ROM function leaves as they were: the callee-saved ones. -/
def romKeep (q : Fin 32) : Bool := q.val ∈ [0, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- What the ROM's `esp_rom_spiflash_read` at 0x40000130 does, as the proofs
assume it, when the ROM's code `romCode` is in memory at `romBase`. Called
with a flash address `src`, a destination `dst`, and a byte count `n`, all
multiples of 4, with `romStack` bytes of stack below `sp`, it returns to `ra`
with the callee-saved registers unchanged. When it returns 0 in `a0`, the `n`
bytes at `dst` hold `flash` from `src`. Either way it changes no memory but
those bytes and its stack. -/
def RomRead (flash : Nat → BitVec 8) (romStack : Nat) (romBase : Word) (romCode : List Nat) : Prop :=
  ∀ (m : Machine) (src dst n : Word), CodeIn m.mem romBase romCode → m.pc = 0x40000130 → reg m a0 = src →
    reg m a1 = dst → reg m a2 = n →
    src.toNat % 4 = 0 → dst.toNat % 4 = 0 → n.toNat % 4 = 0 → dst.toNat + n.toNat ≤ 2 ^ 32 →
    romStack ≤ (reg m sp).toNat →
    ∃ m', Steps m m' ∧ m'.pc = reg m ra &&& ~~~1 ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧
      (reg m' a0 = 0 → ∀ i, i < n.toNat → m'.mem (dst + BitVec.ofNat 32 i) = flash (src.toNat + i)) ∧
      ∀ x, Sep (reg m sp - BitVec.ofNat 32 romStack) romStack x 1 → Sep dst n.toNat x 1 → m'.mem x = m.mem x

theorem sltu1_cases (x : Word) : (aluEval .sltu x 0x1 = 1 ∧ x = 0) ∨ (aluEval .sltu x 0x1 = 0 ∧ x ≠ 0) := by
  by_cases h : x = 0
  · subst h; exact .inl ⟨rfl, rfl⟩
  · refine .inr ⟨?_, h⟩
    rcases tn_sltu (a := x) (b := 0x1) rfl with ⟨hl, _⟩ | ⟨_, hr⟩
    · exact absurd (BitVec.eq_of_toNat_eq (by show x.toNat = 0; have : (0x1 : Word).toNat = 1 := rfl; omega)) h
    · exact BitVec.eq_of_toNat_eq hr

theorem and_cmask (a : Word) : (a &&& 0xFFFFFFFC).toNat = a.toNat / 4 * 4 := by
  have h : a &&& 0xFFFFFFFC = BitVec.ofNat 32 (a.toNat / 4 * 4) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_ofNat]
    have hm : ∀ i : Fin 32, (0xFFFFFFFC : Word).getLsbD i.val = decide (2 ≤ i.val) := by decide
    rw [hm ⟨i, hi⟩, show a.toNat / 4 * 4 = 2 ^ 2 * (a.toNat / 2 ^ 2) by omega, Nat.testBit_two_pow_mul]
    simp only [BitVec.getLsbD, hi, decide_true, Bool.true_and]
    by_cases h2 : 2 ≤ i
    · simp only [h2, decide_true, Bool.and_true, Bool.true_and]
      rw [Nat.testBit_div_two_pow, show i - 2 + 2 = i by omega]
    · simp only [h2, decide_false, Bool.and_false, Bool.false_and]
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; have := a.isLt; omega

theorem and_3 (a : Word) : (a &&& 0x3).toNat = a.toNat % 4 :=
  and_low (k := 2) (by decide) (by decide)

/-- The register `rd` after a step that wrote it. -/
theorem St.newReg {M : Word → BitVec 8} {base : Word} {m : Machine} {off : Nat} {f : Fin 32 → Word}
    {rd : Fin 32} {v : Word} (u : St M base m off (upd f rd v)) (h : rd.val ≠ 0) : reg m rd = v := by
  rw [u.regs]; simp [upd, h]

/-- Every other register after a step that wrote `rd`. -/
theorem St.oldReg {M : Word → BitVec 8} {base : Word} {m : Machine} {off : Nat} {f : Fin 32 → Word}
    {rd : Fin 32} {v : Word} (u : St M base m off (upd f rd v)) (hz : f 0 = 0) (q : Fin 32) (hq : q ≠ rd) :
    reg m q = f q := by
  rw [u.regs]
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; simp [upd]; exact hz.symm
  · simp [upd, h0, hq]

/-- A ROM whose `esp_rom_spiflash_read` always fails: `li a0, 1; ret`. It
meets `RomRead` for any flash, so `RomRead` is satisfiable; the audit uses it
to show that `flashRead_correct`'s hypotheses are. -/
def romStubCode : List Nat := [0x05, 0x45, 0x82, 0x80]

theorem rs_at_0 : fetchRel romStubCode 0x0 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem rs_at_2 : fetchRel romStubCode 0x2 = some (.jalr x0 ra 0x0, 2) := by decide

theorem romStub_read (flash : Nat → BitVec 8) : RomRead flash 0 0x40000130 romStubCode := by
  intro m src dst n hc hpc _ _ _ _ _ _ _ _
  have s0 : St m.mem 0x40000130 m 0 (reg m) := ⟨by rw [hpc]; rfl, rfl, fun _ => rfl⟩
  obtain ⟨m1, d1, u1⟩ := s0.aluImm hc rs_at_0 (off' := 2) (by decide)
  obtain ⟨m2, d2, pc2, mem2, regs2⟩ := u1.jalr hc rs_at_2
  have a0v : reg m2 a0 = 1 := by rw [regs2]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [s0.zero]; rfl
  refine ⟨m2, .cons d1 (.single d2), ?_, fun q hq => ?_, fun h => absurd (a0v.symm.trans h) (by decide), ?_⟩
  · rw [pc2]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero]
  · have ha : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
    rw [regs2, ← u1.regs, u1.oldReg s0.zero q ha]
  · intro x _ _; rw [mem2]

/-- Where `rom::flash_read_words` runs: its code at the image's address (its
pc-relative call reaches the ROM only from there), `16 + romStack` bytes of
stack at `G`, its own 16 at the top and the ROM's below, and the
destination's `4 w` bytes. -/
structure RFWEnv (M : Word → BitVec 8) (P G dst w : Word) (romStack : Nat) : Prop where
  hP : P = 0x403A1730
  code : CodeIn M P romFlashReadWordsCode
  hG : G.toNat % 4 = 0
  hR : romStack % 4 = 0
  hGt : G.toNat + 16 + romStack ≤ 2 ^ 32
  hdst : dst.toNat % 4 = 0
  hw : dst.toNat + 4 * w.toNat < 2 ^ 32
  sGC : Sep G (16 + romStack) P romFlashReadWordsCode.length
  sDC : Sep dst (4 * w.toNat) P romFlashReadWordsCode.length
  sDG : Sep dst (4 * w.toNat) G (16 + romStack)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `rom::flash_read_words`**, given `RomRead`: called with a
4-aligned flash address `src`, a destination `dst`, and a word count `w`, it
returns 1 or 0 in `a0`; when it returns 1, the `4 w` bytes at `dst` hold the
flash's bytes from `src`. It keeps `sp` and the callee-saved registers, and
changes no memory outside its stack region and the destination. -/
theorem romFlashReadWords_correct {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat}
    (hROM : RomRead flash R romBase romCode) (m : Machine)
    {P G src dst w retAddr : Word} (env : RFWEnv m.mem P G dst w R) (hpc : m.pc = P) (ha0 : reg m a0 = src)
    (ha1 : reg m a1 = dst) (ha2 : reg m a2 = w) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = G + BitVec.ofNat 32 (16 + R)) (hsrc : src.toNat % 4 = 0)
    (hrom : CodeIn m.mem romBase romCode) (sGR : Sep G (16 + R) romBase romCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = G + BitVec.ofNat 32 (16 + R) ∧
      (∀ q, romKeep q = true → reg m' q = reg m q) ∧ (reg m' a0 = 0 ∨ reg m' a0 = 1) ∧
      (reg m' a0 = 1 → ∀ i, i < 4 * w.toNat → m'.mem (dst + BitVec.ofNat 32 i) = flash (src.toNat + i)) ∧
      ∀ x, Sep G (16 + R) x 1 → Sep dst (4 * w.toNat) x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨F, hF⟩ : ∃ F, G + BitVec.ofNat 32 R = F := ⟨_, rfl⟩
  have hGt := env.hGt
  have hFsp : G + BitVec.ofNat 32 (16 + R) + 0xFFFFFFF0 = F := by
    rw [← hF, BitVec.add_assoc, show (0xFFFFFFF0 : Word) = BitVec.ofNat 32 4294967280 from rfl, ofNat_add_ofNat]
    rw [show BitVec.ofNat 32 (16 + R + 4294967280) = BitVec.ofNat 32 R from
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)]
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hG (k := R) env.hR
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (R + c) := fun c => by
    rw [← hF, add_ofNat_assoc]
  have hcS : ∀ {c : Nat}, c + 4 ≤ 16 → Sep (F + BitVec.ofNat 32 c) 4 P romFlashReadWordsCode.length := fun {c} h => by
    rw [fG]; exact env.sGC.sub (c := R + c) (l := 4) (by omega)
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code rfw_at_0 (off' := 2) (by decide)
  have r1sp : reg m1 sp = F := by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [hsp, hFsp]
  have rk1 : ∀ r, r ≠ sp → reg m1 r = reg m r := fun r h1 => by
    rw [u1.regs]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, h1]
  obtain ⟨m2, d2, u2⟩ := u1.self.swG env.code rfw_at_2 (off' := 4) (by decide)
    (by rw [r1sp]; exact fr_al' hFa (by decide)) (a := F + 0xC) (v := reg m ra) (by rw [r1sp])
    (rk1 _ (by decide))
  obtain ⟨M1, hM1⟩ : ∃ M', memStore32 m.mem (F + 0xC) (reg m ra) = M' := ⟨_, rfl⟩
  rw [hM1] at u2
  have hc2 : CodeIn M1 P romFlashReadWordsCode := by
    rw [← hM1]; exact env.code.store32 (hcS (c := 0xC) (by decide))
  have sF : ∀ x, Sep G (16 + R) x 1 → Sep (F + 0xC) 4 x 1 := fun x hx => by
    rw [show F + 0xC = G + BitVec.ofNat 32 (R + 12) from fG 12]; exact hx.sub (c := R + 12) (l := 4) (by omega)
  have fM1 : ∀ x, Sep G (16 + R) x 1 → M1 x = m.mem x := fun x hx => by
    rw [← hM1, memStore32_get_sep (sF x hx)]
  obtain ⟨m3, d3, u3⟩ := u2.aluImm hc2 rfw_at_4 (off' := 6) (by decide)
  have hw4 : w <<< 2 = BitVec.ofNat 32 (4 * w.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have := env.hw; omega
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.callRa hc2 rfw_at_6 rfw_at_a (cb := 0x40000130)
    (by rw [env.hP]; rfl) (by decide)
  have r4 := PEnv.reg1 regs4 u3.zero
  have r4a : ∀ q, q ≠ ra → q ≠ a2 → reg m4 q = reg m1 q := fun q h1 h2 => by
    rw [r4 q h1]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u1.self.zero.symm
    · simp [upd, h0, h2]
  have sp4 : reg m4 sp = F := by rw [r4a _ (by decide) (by decide), r1sp]
  have n4 : reg m4 a2 = BitVec.ofNat 32 (4 * w.toNat) := by
    rw [r4 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [rk1 _ (by decide), ha2]
    exact hw4
  have nN : (BitVec.ofNat 32 (4 * w.toNat)).toNat = 4 * w.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; have := env.hw; have := env.hdst; omega
  have hRsp : R ≤ (reg m4 sp).toNat := by
    rw [sp4, ← hF, BitVec.toNat_add, BitVec.toNat_ofNat]; have := env.hGt
    rw [Nat.mod_eq_of_lt (a := R) (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨m5, c5, pc5, k5, by5, fr5⟩ := hROM m4 src dst _
    (fun i hi => by rw [mem4, fM1 _ (sGR.subR (c := i) (l := 1) (by omega))]; exact hrom i hi) pc4
    (by rw [r4a _ (by decide) (by decide), rk1 _ (by decide), ha0])
    (by rw [r4a _ (by decide) (by decide), rk1 _ (by decide), ha1]) n4 hsrc env.hdst
    (by rw [nN]; omega) (by rw [nN]; exact Nat.le_of_lt env.hw) hRsp
  rw [nN] at by5 fr5
  have eR : reg m4 sp - BitVec.ofNat 32 R = G := by rw [sp4, ← hF, BitVec.add_sub_cancel]
  rw [eR] at fr5
  have inR : ∀ x, Sep G (16 + R) x 1 → Sep G R x 1 := fun x hx => by
    have := hx.sub (c := 0) (l := R) (by omega); rwa [add_ofNat_zero] at this
  have fr5G : ∀ x, Sep G (16 + R) x 1 → Sep dst (4 * w.toNat) x 1 → m5.mem x = m.mem x := fun x hx hd => by
    rw [fr5 x (inR x hx) hd, mem4, fM1 x hx]
  have hc5 : CodeIn m5.mem P romFlashReadWordsCode := fun i hi => by
    rw [fr5G _ (env.sGC.subR (c := i) (l := 1) (by omega)) (env.sDC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  have w5 : St m5.mem P m5 0xE (reg m5) := ⟨by
    rw [pc5, regs4]; simp +decide only [upd_app, ↓reduceIte]
    rw [env.hP]; decide, rfl, fun _ => rfl⟩
  obtain ⟨m6, d6, u6⟩ := w5.aluImm hc5 rfw_at_e (off' := 0x12) (by decide)
  have rd : memLoad32 m5.mem (F + 0xC) = reg m ra := by
    rw [load_frame2 fr5 (by rw [show F + 0xC = G + BitVec.ofNat 32 (R + 12) from fG 12]; exact (sep_offsets G (c := 0) (n := R) (d := R + 12) (k := 4) (.inl (by omega))
      (by omega) (by omega)) |> fun h => by rwa [add_ofNat_zero] at h)
      (by rw [show F + 0xC = G + BitVec.ofNat 32 (R + 12) from fG 12]; exact env.sDG.subR (c := R + 12) (l := 4) (by omega)), mem4, ← hM1, memLoad32_store32_same]
  obtain ⟨m7, d7, u7⟩ := u6.lwE hc5 rfw_at_12 (off' := 0x14) (by decide)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [k5 _ rfl, sp4]; exact fr_al' hFa (by decide))
    (v := reg m ra) (by simp +decide only [upd_app, ↓reduceIte]; rw [k5 _ rfl, sp4]; exact rd)
  obtain ⟨m8, d8, u8⟩ := u7.aluImm hc5 rfw_at_14 (off' := 0x16) (by decide)
  obtain ⟨m9, d9, pc9, mem9, regs9⟩ := u8.jalr hc5 rfw_at_16
  have hseqz := sltu1_cases (reg m5 a0)
  have fin_sp : F + 0x10 = G + BitVec.ofNat 32 (16 + R) := by
    rw [← hF, show (0x10 : Word) = BitVec.ofNat 32 16 from rfl, add_ofNat_assoc, Nat.add_comm]
  refine ⟨m9, .cons d1 (.cons d2 (.cons d3 (c4.trans (c5.trans (.cons d6 (.cons d7 (.cons d8 (.single d9)))))))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc9]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, hra, hret]
  · rw [regs9]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [k5 _ rfl, sp4, fin_sp]
  · intro q hq
    rw [regs9]
    by_cases hs : q = sp
    · subst hs; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [k5 _ rfl, sp4, fin_sp, hsp]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    have hr : q ≠ ra := fun e => by subst e; exact absurd hq (by decide)
    have ha : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
    have h2 : q ≠ a2 := fun e => by subst e; exact absurd hq (by decide)
    rw [upd_ne h0 hs, upd_ne h0 hr, upd_ne h0 ha, k5 q hq, r4a q hr h2, rk1 q hs]
  · rw [regs9]; simp +decide only [upd_app, ↓reduceIte]
    rcases hseqz with ⟨h, _⟩ | ⟨h, _⟩
    · exact .inr h
    · exact .inl h
  · intro h1 i hi
    rw [mem9]
    have h0 : reg m5 a0 = 0 := by
      rw [regs9] at h1; simp +decide only [upd_app, ↓reduceIte] at h1
      rcases hseqz with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · rw [h] at h1; exact absurd h1 (by decide)
    exact by5 h0 i hi
  · intro x hx hd
    rw [mem9, fr5G x hx hd]

/-- Byte `k` of a word stored at `a`, read back. -/
theorem st32_byte (M : Word → BitVec 8) (a v : Word) :
    ∀ k, k < 4 → memStore32 M a v (a + BitVec.ofNat 32 k) = v.extractLsb' (8 * k) 8 := by
  intro k hk
  have ne : ∀ i j : Nat, i < 4 → j < 4 → i ≠ j → a + BitVec.ofNat 32 i ≠ a + BitVec.ofNat 32 j :=
    fun i j hi hj h => add_ofNat_ne a (by omega) (by omega) h
  unfold memStore32
  rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, show (2 : Word) = BitVec.ofNat 32 2 from rfl,
    show (3 : Word) = BitVec.ofNat 32 3 from rfl]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [memStore8_ne (ne 0 3 (by decide) (by decide) (by decide)), memStore8_ne (ne 0 2 (by decide) (by decide) (by decide)),
      memStore8_ne (ne 0 1 (by decide) (by decide) (by decide)), add_ofNat_zero, memStore8_same]
  · rw [memStore8_ne (ne 1 3 (by decide) (by decide) (by decide)), memStore8_ne (ne 1 2 (by decide) (by decide) (by decide)),
      memStore8_same]
  · rw [memStore8_ne (ne 2 3 (by decide) (by decide) (by decide)), memStore8_same]
  · rw [memStore8_same]

set_option maxRecDepth 100000 in
theorem frd_and_c : ∀ v : Fin 256, BitVec.ofNat 32 v.val &&& 0xFFFFFFFC = BitVec.ofNat 32 (4 * (v.val / 4)) := by
  decide

set_option maxRecDepth 100000 in
theorem frd_and_3 : ∀ v : Fin 256, BitVec.ofNat 32 v.val &&& 0x3 = BitVec.ofNat 32 (v.val % 4) := by
  decide

set_option maxHeartbeats 4000000 in
/-- The inner loop of `flash::read`, from 0xA6, copies the next `r` bytes of
the bounce buffer at `B` from offset `sk + j` to the result at `O` from
offset `d + j`, through the 4-byte scratch word at `Sc`. -/
theorem frd_inner {M0 : Word → BitVec 8} {P F O : Word} {d sk W L : Nat} (hP : P.toNat % 2 = 0)
    (hc0 : CodeIn M0 P flashReadCode) (hF : F.toNat % 4 = 0)
    (sOC : Sep O L P flashReadCode.length) (sSC : Sep (F + 0x10C) 4 P flashReadCode.length)
    (sOB : Sep O L (F + 0xC) 0x100) (sOS : Sep O L (F + 0x10C) 4) (hO : O.toNat + L < 2 ^ 32)
    (hW : sk + W ≤ 256) (hD : d + W ≤ L) :
    ∀ r j (n : Machine) (Mj : Word → BitVec 8), j + r = W → 0 < r →
      St Mj P n 0xA6 (reg n) → reg n a1 = O + BitVec.ofNat 32 (d + j) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (sk + j) → reg n a0 = BitVec.ofNat 32 (2 ^ 32 - r) →
      reg n (9 : Fin 32) = O + BitVec.ofNat 32 L → reg n (22 : Fin 32) = F + 0xC →
      reg n (24 : Fin 32) = 0xFF → reg n (25 : Fin 32) = F + 0x10C → reg n sp = F →
      (∀ t, t < j → Mj (O + BitVec.ofNat 32 (d + t)) = M0 (F + 0xC + BitVec.ofNat 32 (sk + t))) →
      (∀ x, Sep (F + 0x10C) 4 x 1 → Sep (O + BitVec.ofNat 32 d) j x 1 → Mj x = M0 x) →
      ∃ n' Mw, Steps n n' ∧ St Mw P n' 0xDE (reg n') ∧
        (∀ t, t < W → Mw (O + BitVec.ofNat 32 (d + t)) = M0 (F + 0xC + BitVec.ofNat 32 (sk + t))) ∧
        (∀ x, Sep (F + 0x10C) 4 x 1 → Sep (O + BitVec.ofNat 32 d) W x 1 → Mw x = M0 x) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  intro r
  induction r with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ r ih =>
    intro j n Mj hjr _ s ha1 hs0 ha0 hs1 hs6 hs8 hs9 hsp hcp hfr
    have hz := s.zero
    have sOd : ∀ {k : Nat}, d + k ≤ L → ∀ x, Sep O L x 1 → Sep (O + BitVec.ofNat 32 d) k x 1 := fun {k} h x hx => by
      intro a ha b hb e; exact hx (d + a) (by omega) b hb (by rw [← add_ofNat_assoc]; exact e)
    have hcj : CodeIn Mj P flashReadCode := fun i hi => by
      rw [hfr _ (sSC.subR (c := i) (l := 1) (by omega)) (sOd (by omega) _ (sOC.subR (c := i) (l := 1) (by omega)))]
      exact hc0 i hi
    have hsk : sk + j < 256 := by omega
    -- the bounce word and the byte
    obtain ⟨n1, d1, u1⟩ := s.aluImm hcj frd_at_a6 (off' := 0xAA) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.alu hcj frd_at_aa (off' := 0xAC) (by decide)
    have e4 : BitVec.ofNat 32 (sk + j) &&& 0xFFFFFFFC = BitVec.ofNat 32 (4 * ((sk + j) / 4)) :=
      frd_and_c ⟨sk + j, hsk⟩
    have hq4 : 4 * ((sk + j) / 4) + (sk + j) % 4 = sk + j := by omega
    have kp : ∀ {m1 : Machine} {f : Fin 32 → Word} {rd : Fin 32} {v : Word} {M' : Word → BitVec 8} {o : Nat},
        St M' P m1 o (upd f rd v) → f 0 = 0 → ∀ q, q ≠ rd → reg m1 q = f q := fun u hz0 q hq => by
      rw [u.regs]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz0.symm
      · simp [upd, h0, hq]
    have nw : ∀ {m1 : Machine} {f : Fin 32 → Word} {rd : Fin 32} {v : Word} {M' : Word → BitVec 8} {o : Nat},
        St M' P m1 o (upd f rd v) → rd.val ≠ 0 → reg m1 rd = v := fun u h => by rw [u.regs]; simp [upd, h]
    -- 0xA6 `andi a2, s0, -4` and 0xAA `add a2, a2, s6`
    obtain ⟨n1, d1, u1⟩ := s.aluImm hcj frd_at_a6 (off' := 0xAA) (by decide)
    have a2_1 : reg n1 a2 = BitVec.ofNat 32 (4 * ((sk + j) / 4)) := by
      rw [nw u1 (by decide)]; show reg n (8 : Fin 32) &&& 0xFFFFFFFC = _; rw [hs0, e4]
    have k1 := kp u1 hz
    obtain ⟨n2, d2, u2⟩ := u1.self.alu hcj frd_at_aa (off' := 0xAC) (by decide)
    have a2_2 : reg n2 a2 = F + 0xC + BitVec.ofNat 32 (4 * ((sk + j) / 4)) := by
      rw [nw u2 (by decide)]; show reg n1 a2 + reg n1 (22 : Fin 32) = _
      rw [a2_1, k1 _ (by decide), hs6, BitVec.add_comm]
    have k2 := kp u2 u1.self.zero
    -- 0xAC `lw a3, 0(a2)`: the bounce word
    have hB4 : (F + 0xC + BitVec.ofNat 32 (4 * ((sk + j) / 4))).toNat % 4 = 0 :=
      aligned_add (fr_al' hF (by decide)) (by omega)
    obtain ⟨n3, d3, u3⟩ := u2.self.lw hcj frd_at_ac (off' := 0xAE) (by decide) (by rw [a2_2, add_lit_zero]; exact hB4)
    have k3 := kp u3 u2.self.zero
    have wd : memLoad32 Mj (reg n2 a2 + 0x0) = memLoad32 M0 (F + 0xC + BitVec.ofNat 32 (4 * ((sk + j) / 4))) := by
      rw [a2_2, add_lit_zero]
      apply memLoad32_congr; intro i hi
      apply hfr
      · rw [show F + 0x10C = F + 0xC + BitVec.ofNat 32 0x100 from by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]
        exact sep_offsets (F + 0xC) (c := 0x100) (n := 4) (d := 4 * ((sk + j) / 4) + i) (k := 1) (.inr (by omega))
          (by decide) (by omega)
      · rw [add_ofNat_assoc]
        exact (sOB.sub (c := d) (l := j) (by omega)).subR (c := 4 * ((sk + j) / 4) + i) (l := 1) (by omega)
    have a3_3 : reg n3 a3 = memLoad32 M0 (F + 0xC + BitVec.ofNat 32 (4 * ((sk + j) / 4))) := by
      rw [nw u3 (by decide), wd]
    -- 0xAE `j 0xC0`, 0xC0 `li a2, 0`, 0xC2 `andi a4, s0, 3`
    obtain ⟨n4, d4, u4⟩ := u3.self.jump hcj frd_at_ae (off' := 0xC0) (by decide) (pc_even (off := 0xAE) (off' := 0xC0) hP u3.self.pc (by decide) (by decide))
    obtain ⟨n5, d5, u5⟩ := u4.aluImm hcj frd_at_c0 (off' := 0xC2) (by decide)
    have k5 := kp u5 u4.zero
    obtain ⟨n6, d6, u6⟩ := u5.self.aluImm hcj frd_at_c2 (off' := 0xC6) (by decide)
    have k6 := kp u6 u5.self.zero
    have a4_6 : reg n6 a4 = BitVec.ofNat 32 ((sk + j) % 4) := by
      rw [nw u6 (by decide)]; show reg n5 (8 : Fin 32) &&& 0x3 = _
      rw [k5 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), hs0]
      exact frd_and_3 ⟨sk + j, hsk⟩
    -- constant registers through the step
    have sp6 : reg n6 sp = F := by
      rw [k6 _ (by decide), k5 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), hsp]
    have s9_6 : reg n6 (25 : Fin 32) = F + 0x10C := by
      rw [k6 _ (by decide), k5 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), hs9]
    have a3_6 : reg n6 a3 = memLoad32 M0 (F + 0xC + BitVec.ofNat 32 (4 * ((sk + j) / 4))) := by
      rw [k6 _ (by decide), k5 _ (by decide), a3_3]
    -- 0xC6 `sw a3, 0x10C(sp)`: the word to the scratch slot
    have hSc : (F + 0x10C).toNat % 4 = 0 := fr_al' hF (by decide)
    obtain ⟨n7, d7, u7⟩ := u6.self.swG hcj frd_at_c6 (off' := 0xCA) (by decide) (by rw [sp6]; exact hSc)
      (a := F + 0x10C) (v := memLoad32 M0 (F + 0xC + BitVec.ofNat 32 (4 * ((sk + j) / 4)))) (by rw [sp6]) a3_6
    obtain ⟨Mj1, hMj1⟩ : ∃ M', memStore32 Mj (F + 0x10C) (memLoad32 M0 (F + 0xC + BitVec.ofNat 32 (4 * ((sk + j) / 4)))) = M' :=
      ⟨_, rfl⟩
    rw [hMj1] at u7
    have hc7 : CodeIn Mj1 P flashReadCode := by rw [← hMj1]; exact hcj.store32 sSC
    -- 0xCA `or a3, s9, a4` and 0xCE `lbu a3, 0(a3)`: the byte
    obtain ⟨n8, d8, u8⟩ := u7.alu hc7 frd_at_ca (off' := 0xCE) (by decide)
    have a3_8 : reg n8 a3 = F + 0x10C + BitVec.ofNat 32 ((sk + j) % 4) := by
      rw [nw u8 (by decide), s9_6, a4_6]; exact or_small hSc (by omega)
    have k8 := kp u8 u6.self.zero
    obtain ⟨n9, d9, u9⟩ := u8.self.lbu hc7 frd_at_ce (off' := 0xD2) (by decide)
    have byte : Mj1 (reg n8 a3 + 0x0) = M0 (F + 0xC + BitVec.ofNat 32 (sk + j)) := by
      rw [a3_8, add_lit_zero, ← hMj1, st32_byte _ _ _ _ (Nat.mod_lt _ (by decide)), load_byte _ _ _ (Nat.mod_lt _ (by decide)),
        add_ofNat_assoc, hq4]
    have k9 := kp u9 u8.self.zero
    -- 0xD2 `sb a3, 0(a1)`
    have a1_9 : reg n9 a1 = O + BitVec.ofNat 32 (d + j) := by
      rw [k9 _ (by decide), k8 _ (by decide), k6 _ (by decide), k5 _ (by decide), k3 _ (by decide), k2 _ (by decide),
        k1 _ (by decide), ha1]
    obtain ⟨n10, d10, u10⟩ := u9.self.sb hc7 frd_at_d2 (off' := 0xD6) (by decide)
    have st10 : memStore8 Mj1 (reg n9 a1 + 0x0) ((reg n9 a3).extractLsb' 0 8) =
        memStore8 Mj1 (O + BitVec.ofNat 32 (d + j)) (M0 (F + 0xC + BitVec.ofNat 32 (sk + j))) := by
      rw [a1_9, add_lit_zero, nw u9 (by decide), byte, zext_byte]
    rw [st10] at u10
    obtain ⟨Mj2, hMj2⟩ : ∃ M', memStore8 Mj1 (O + BitVec.ofNat 32 (d + j)) (M0 (F + 0xC + BitVec.ofNat 32 (sk + j))) = M' :=
      ⟨_, rfl⟩
    rw [hMj2] at u10
    have hc10 : CodeIn Mj2 P flashReadCode := by
      rw [← hMj2]; exact hc7.store8 (by
        have := sOC.sub (c := d + j) (l := 1) (by omega); exact this)
    -- 0xD6, 0xD8, 0xDA: the three increments
    obtain ⟨n11, d11, u11⟩ := u10.aluImm hc10 frd_at_d6 (off' := 0xD8) (by decide)
    obtain ⟨n12, d12, u12⟩ := u11.aluImm hc10 frd_at_d8 (off' := 0xDA) (by decide)
    obtain ⟨n13, d13, u13⟩ := u12.aluImm hc10 frd_at_da (off' := 0xDC) (by decide)
    have a1_13 : reg n13 a1 = O + BitVec.ofNat 32 (d + (j + 1)) := by
      rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [a1_9]
      exact add_ofNat_assoc O (d + j) 1
    have a0_13 : reg n13 a0 = BitVec.ofNat 32 (2 ^ 32 - r) := by
      rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]
      rw [k9 _ (by decide), k8 _ (by decide), k6 _ (by decide), k5 _ (by decide), k3 _ (by decide), k2 _ (by decide),
        k1 _ (by decide), ha0]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0x1 : Word).toNat = 1 from rfl]
      omega
    have s0_13 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 (sk + (j + 1)) := by
      rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]
      rw [k9 _ (by decide), k8 _ (by decide), k6 _ (by decide), k5 _ (by decide), k3 _ (by decide), k2 _ (by decide),
        k1 _ (by decide), hs0]
      exact ofNat_add_lit (sk + j) 1
    have k13 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (8 : Fin 32) → reg n13 q = reg n q :=
      fun q h0' h1 h2 h3 h4 h8 => by
        rw [u13.regs]
        by_cases h0 : q.val = 0
        · have : q = 0 := Fin.ext h0
          subst this; simp [upd]; exact hz.symm
        simp only [upd, h0, h1, h0', h8, ite_false]
        rw [k9 _ h3, k8 _ h3, k6 _ h4, k5 _ h2, k3 _ h3, k2 _ h2, k1 _ h2]
    have hz13 : reg n13 0 = 0 := u13.self.zero
    -- the memory after the step
    have hcp2 : ∀ t, t < j + 1 → Mj2 (O + BitVec.ofNat 32 (d + t)) = M0 (F + 0xC + BitVec.ofNat 32 (sk + t)) := by
      intro t ht
      rw [← hMj2]
      by_cases htj : t = j
      · subst htj; rw [memStore8_same]
      · rw [memStore8_ne (add_ofNat_ne O (by omega) (by omega) (by omega)), ← hMj1,
          memStore32_get_sep ((sOS.symm.subR (c := d + t) (l := 1) (by omega))), hcp t (by omega)]
    have hfr2 : ∀ x, Sep (F + 0x10C) 4 x 1 → Sep (O + BitVec.ofNat 32 d) (j + 1) x 1 → Mj2 x = M0 x := by
      intro x hx hd
      rw [← hMj2, memStore8_ne (fun e => hd j (by omega) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_assoc]; exact e.symm)),
        ← hMj1, memStore32_get_sep hx]
      exact hfr x hx (fun i hi k hk e => hd i (by omega) k hk e)
    by_cases hr : r = 0
    · subst hr
      obtain ⟨n14, d14, u14⟩ := u13.self.notTaken hc10 0xDE frd_at_dc (by decide) (by
        simp only [branchTaken, a0_13, hz13]; decide)
      refine ⟨n14, Mj2, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10
        (.cons d11 (.cons d12 (.cons d13 (.single d14))))))))))))), u14.self, ?_, ?_, ?_⟩
      · intro t ht; exact hcp2 t (by omega)
      · intro x hx hd; exact hfr2 x hx (by rw [show j + 1 = W by omega]; exact hd)
      · intro q h0 h1 h2 h3 h4 h8; rw [u14.regs, k13 q h0 h1 h2 h3 h4 h8]
    have hrr : 0 < r := Nat.pos_of_ne_zero hr
    -- back to 0x9C, then through its three checks to 0xA6
    obtain ⟨n14, d14, u14⟩ := u13.self.taken hc10 0x9C frd_at_dc (by decide) (by
      simp only [branchTaken, a0_13, hz13, bne_iff_ne, ne_eq]
      exact fun e => absurd (ofNat_inj (c := 2 ^ 32 - r) (d := 0) (by omega) (by decide) e) (by omega))
    have a2_13 : reg n13 a2 = 0 := by
      rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [k9 _ (by decide), k8 _ (by decide), k6 _ (by decide), nw u5 (by decide)]; rfl
    obtain ⟨n15, d15, u15⟩ := u14.notTaken hc10 0x9E frd_at_9c (by decide) (by
      simp only [branchTaken, a2_13, hz13]; decide)
    obtain ⟨n16, d16, u16⟩ := u15.notTaken hc10 0xA2 frd_at_9e (by decide) (by
      simp only [branchTaken, a1_13, k13 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hs1]
      exact beq_false_of_ne (add_ofNat_ne O (c := d + (j + 1)) (d := L) (by omega) (by omega) (by omega)))
    obtain ⟨n17, d17, u17⟩ := u16.notTaken hc10 0xA6 frd_at_a2 (by decide) (by
      simp only [branchTaken, s0_13, k13 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hs8]
      rw [show (0xFF : Word) = BitVec.ofNat 32 255 from rfl, ult_lit (x := 255) (y := sk + (j + 1)) (by decide) (by omega)]
      exact decide_eq_false (by omega))
    obtain ⟨n', Mw, c', u', hcp', hfr', k'⟩ := ih (j + 1) n17 Mj2 (by omega) hrr u17.self
      (by rw [u17.regs]; exact a1_13)
      (by rw [u17.regs]; exact s0_13)
      (by rw [u17.regs]; exact a0_13)
      (by rw [u17.regs, k13 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hs1])
      (by rw [u17.regs, k13 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hs6])
      (by rw [u17.regs, k13 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hs8])
      (by rw [u17.regs, k13 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hs9])
      (by rw [u17.regs, k13 sp (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hsp])
      hcp2 hfr2
    refine ⟨n', Mw, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10
      (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 c')))))))))))))))), u', hcp', hfr', ?_⟩
    intro q h0 h1 h2 h3 h4 h8
    rw [k' q h0 h1 h2 h3 h4 h8, u17.regs, k13 q h0 h1 h2 h3 h4 h8]

/-- Where `flash::read` runs: its code at the image's address (it reaches
`rom::flash_read_words` with a pc-relative call), `memset`'s and
`flash_read_words`'s code where its calls reach them, `0x150 + romStack`
bytes of stack at `G` (from the top: its 0x140-byte frame,
`flash_read_words`'s 16, and the ROM's), and the result's `len` bytes at
`out`, apart from all of those. -/
structure FRdEnv (M : Word → BitVec 8) (P G out len : Word) (romStack : Nat) (romBase : Word)
    (romCode : List Nat) : Prop where
  hP : P = 0x403A1748
  code : CodeIn M P flashReadCode
  mset : CodeIn M (P + 0x1309E) memsetCode
  fw : CodeIn M (P + 0xFFFFFFE8) romFlashReadWordsCode
  hG : G.toNat % 4 = 0
  hR : romStack % 4 = 0
  hGt : G.toNat + 0x150 + romStack ≤ 2 ^ 32
  hlen : out.toNat + len.toNat < 2 ^ 32
  sGC : Sep G (0x150 + romStack) P flashReadCode.length
  sGM : Sep G (0x150 + romStack) (P + 0x1309E) memsetCode.length
  sGW : Sep G (0x150 + romStack) (P + 0xFFFFFFE8) romFlashReadWordsCode.length
  sOC : Sep out len.toNat P flashReadCode.length
  sOW : Sep out len.toNat (P + 0xFFFFFFE8) romFlashReadWordsCode.length
  sOG : Sep out len.toNat G (0x150 + romStack)
  rom : CodeIn M romBase romCode
  sGR : Sep G (0x150 + romStack) romBase romCode.length
  sOR : Sep out len.toNat romBase romCode.length

theorem beq_toNat {a b : Word} (h : a.toNat ≠ b.toNat) : (a == b) = false :=
  beq_eq_false_iff_ne.mpr fun e => h (e ▸ rfl)

theorem bne_toNat {a b : Word} (h : a.toNat ≠ b.toNat) : (a != b) = true :=
  bne_iff_ne.mpr fun e => h (e ▸ rfl)

theorem zero_toNat : (0 : Word).toNat = 0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The outer loop of `flash::read`, from 0x60 with `d` bytes read: it reads
the rest a chunk at a time and reaches 0xE4 with `d'` bytes read, all of
them when `d' = len`. -/
theorem frd_outer {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat}
    (hROM : RomRead flash R romBase romCode) {M0 Mp : Word → BitVec 8}
    {P G out len addr : Word} (env : FRdEnv M0 P G out len R romBase romCode) :
    ∀ k d (n : Machine) (Mo : Word → BitVec 8), len.toNat - d ≤ k → d < len.toNat →
      St Mo P n 0x60 (reg n) →
      reg n (18 : Fin 32) = addr → reg n (19 : Fin 32) = out → reg n (21 : Fin 32) = len →
      reg n (20 : Fin 32) = 0x100 → reg n (22 : Fin 32) = G + BitVec.ofNat 32 (16 + R) + 0xC →
      reg n (23 : Fin 32) = BitVec.ofNat 32 d → reg n (24 : Fin 32) = 0xFF →
      reg n (25 : Fin 32) = G + BitVec.ofNat 32 (16 + R) + 0x10C → reg n (9 : Fin 32) = out + len →
      reg n sp = G + BitVec.ofNat 32 (16 + R) →
      (∀ i, i < d → Mo (out + BitVec.ofNat 32 i) = flash (addr.toNat + i)) →
      (∀ x, Sep G (0x150 + R) x 1 → Sep out len.toNat x 1 → Mo x = M0 x) →
      (∀ i, i < 0x30 → Mo (G + BitVec.ofNat 32 (16 + R) + BitVec.ofNat 32 (0x110 + i)) =
        Mp (G + BitVec.ofNat 32 (16 + R) + BitVec.ofNat 32 (0x110 + i))) →
      ∃ n' M' d', Steps n n' ∧ St M' P n' 0xE4 (reg n') ∧ reg n' (23 : Fin 32) = BitVec.ofNat 32 d' ∧
        reg n' (21 : Fin 32) = len ∧ reg n' sp = G + BitVec.ofNat 32 (16 + R) ∧ d' ≤ len.toNat ∧
        (d' = len.toNat → ∀ i, i < len.toNat → M' (out + BitVec.ofNat 32 i) = flash (addr.toNat + i)) ∧
        (∀ x, Sep G (0x150 + R) x 1 → Sep out len.toNat x 1 → M' x = M0 x) ∧
        (∀ i, i < 0x30 → M' (G + BitVec.ofNat 32 (16 + R) + BitVec.ofNat 32 (0x110 + i)) =
          Mp (G + BitVec.ofNat 32 (16 + R) + BitVec.ofNat 32 (0x110 + i))) ∧
        ∀ q, romKeep q = true → q ≠ (8 : Fin 32) → q ≠ (23 : Fin 32) → q ≠ (26 : Fin 32) → reg n' q = reg n q := by
  intro k
  induction k with
  | zero => intro d _ _ hk hd; exact absurd hd (by omega)
  | succ k ih =>
  intro d n Mo hk hd s h18 h19 h21 h20 h22 h23 h24 h25 h9 hsp hcp hfr hsl
  obtain ⟨F, hF⟩ : ∃ F, G + BitVec.ofNat 32 (16 + R) = F := ⟨_, rfl⟩
  rw [hF] at h22 h25 hsp hsl ⊢
  have hz := s.zero
  have hGt := env.hGt
  have hlen := env.hlen
  have hFn : F.toNat = G.toNat + (16 + R) := by
    rw [← hF, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 + R) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hG (k := 16 + R) (by have := env.hR; omega)
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (16 + R + c) := fun c => by
    rw [← hF, add_ofNat_assoc]
  have hcP : CodeIn Mo P flashReadCode := fun i hi => by
    rw [hfr _ (env.sGC.subR (c := i) (l := 1) (by omega)) (env.sOC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  have hcW : CodeIn Mo (P + 0xFFFFFFE8) romFlashReadWordsCode := fun i hi => by
    rw [hfr _ (env.sGW.subR (c := i) (l := 1) (by omega)) (env.sOW.subR (c := i) (l := 1) (by omega))]
    exact env.fw i hi
  have hPe : P.toNat % 2 = 0 := by rw [env.hP]; decide
  -- 0x60 `add a0, s7, s2`, 0x64 `bltu a0, s7`: an address past 2^32 ends the loop
  obtain ⟨n1, d1, u1⟩ := s.alu hcP frd_at_60 (off' := 0x64) (by decide)
  have a0_1 : reg n1 a0 = BitVec.ofNat 32 d + addr := by
    rw [u1.newReg (by decide)]; show reg n (23 : Fin 32) + reg n (18 : Fin 32) = _; rw [h23, h18]
  have k1 := u1.oldReg hz
  have hdl : d < 2 ^ 32 := by omega
  by_cases hov : d + addr.toNat < 2 ^ 32
  case neg =>
    obtain ⟨n2, d2, u2⟩ := u1.self.taken hcP 0xE4 frd_at_64 (by decide) (by
      simp only [branchTaken, a0_1, k1 (23 : Fin 32) (by decide), h23, BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hdl]
      exact decide_eq_true (by have := addr.isLt; omega))
    refine ⟨n2, Mo, d, .cons d1 (.single d2), u2.self, ?_, ?_, ?_, by omega, fun h => absurd h (by omega), hfr, hsl,
      fun q hq _ _ _ => ?_⟩
    · rw [u2.regs, k1 _ (by decide), h23]
    · rw [u2.regs, k1 _ (by decide), h21]
    · rw [u2.regs, k1 _ (by decide), hsp]
    · rw [u2.regs, k1 q (fun e => by subst e; exact absurd hq (by decide))]
  have hpos : (BitVec.ofNat 32 d + addr).toNat = d + addr.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdl, Nat.mod_eq_of_lt hov]
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hcP 0x68 frd_at_64 (by decide) (by
    simp only [branchTaken, a0_1, k1 (23 : Fin 32) (by decide), h23, BitVec.ult, hpos, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdl]
    exact decide_eq_false (by omega))
  have k2 := u2.regs
  -- 0x68 `andi s0, a0, 3`: where the chunk starts in its word
  obtain ⟨n3, d3, u3⟩ := u2.aluImm hcP frd_at_68 (off' := 0x6C) (by decide)
  have s0_3 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 ((d + addr.toNat) % 4) := by
    rw [u3.newReg (by decide)]; show reg n1 a0 &&& 0x3 = _
    rw [a0_1]; apply BitVec.eq_of_toNat_eq
    rw [and_3, hpos, BitVec.toNat_ofNat]; omega
  have k3 := u3.oldReg u2.zero
  -- 0x6C `sub a1, s5, s7` and 0x70 `sub s10, s4, s0`
  obtain ⟨n4, d4, u4⟩ := u3.self.alu hcP frd_at_6c (off' := 0x70) (by decide)
  have a1_4 : reg n4 a1 = BitVec.ofNat 32 (len.toNat - d) := by
    rw [u4.newReg (by decide)]; show reg n3 (21 : Fin 32) - reg n3 (23 : Fin 32) = _
    rw [k3 _ (by decide), k3 (23 : Fin 32) (by decide), k1 _ (by decide), k1 (23 : Fin 32) (by decide), h21, h23]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdl]; have := len.isLt; omega
  have k4 := u4.oldReg u3.self.zero
  obtain ⟨n5, d5, u5⟩ := u4.self.alu hcP frd_at_70 (off' := 0x74) (by decide)
  have s10_5 : reg n5 (26 : Fin 32) = BitVec.ofNat 32 (256 - (d + addr.toNat) % 4) := by
    rw [u5.newReg (by decide)]; show reg n4 (20 : Fin 32) - reg n4 (8 : Fin 32) = _
    rw [k4 _ (by decide), k4 (8 : Fin 32) (by decide), k3 _ (by decide), s0_3, k1 _ (by decide), h20]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0x100 : Word).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (a := (d + addr.toNat) % 4) (by omega)]; omega
  have k5 := u5.oldReg u4.self.zero
  -- 0x74 `bltu s10, a1` and 0x78 `mv s10, a1`: the chunk is the rest or what the buffer holds
  obtain ⟨W, hW⟩ : ∃ W, min (len.toNat - d) (256 - (d + addr.toNat) % 4) = W := ⟨_, rfl⟩
  have hW1 : 0 < W := by rw [← hW]; omega
  have hWd : d + W ≤ len.toNat := by rw [← hW]; omega
  have hWs : (d + addr.toNat) % 4 + W ≤ 256 := by rw [← hW]; omega
  obtain ⟨n6, c6, u6, s10_6, k6⟩ : ∃ n6, Steps n5 n6 ∧ St Mo P n6 0x7A (reg n6) ∧
      reg n6 (26 : Fin 32) = BitVec.ofNat 32 W ∧ ∀ q, q ≠ (26 : Fin 32) → reg n6 q = reg n5 q := by
    by_cases hlt : 256 - (d + addr.toNat) % 4 < len.toNat - d
    · obtain ⟨n6, d6, u6⟩ := u5.self.taken hcP 0x7A frd_at_74 (by decide) (by
        simp only [branchTaken, s10_5, k5 a1 (by decide), a1_4]
        rw [ult_lit (by omega) (by omega)]; exact decide_eq_true hlt)
      refine ⟨n6, .single d6, u6.self, by rw [u6.regs, s10_5, ← hW]; congr 1; omega, fun q _ => u6.regs q⟩
    · obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hcP 0x78 frd_at_74 (by decide) (by
        simp only [branchTaken, s10_5, k5 a1 (by decide), a1_4]
        rw [ult_lit (by omega) (by omega)]; exact decide_eq_false hlt)
      obtain ⟨n7, d7, u7⟩ := u6.aluE hcP frd_at_78 (off' := 0x7A) (by decide) (v := BitVec.ofNat 32 W) (by
        show reg n5 0 + reg n5 a1 = _
        rw [u5.self.zero, k5 a1 (by decide), a1_4, ← hW,
          show min (len.toNat - d) (256 - (d + addr.toNat) % 4) = len.toNat - d by omega]
        exact BitVec.zero_add _)
      refine ⟨n7, .cons d6 (.single d7), u7.self, u7.newReg (by decide), fun q hq => ?_⟩
      exact u7.oldReg u5.self.zero q hq
  have sk_ : reg n6 (8 : Fin 32) = BitVec.ofNat 32 ((d + addr.toNat) % 4) := by
    rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), s0_3]
  -- 0x7A..0x86: the word count, the aligned flash address, and the buffer
  obtain ⟨n7, d7, u7⟩ := u6.alu hcP frd_at_7a (off' := 0x7E) (by decide)
  have k7 := u7.oldReg u6.zero
  obtain ⟨n8, d8, u8⟩ := u7.self.aluImm hcP frd_at_7e (off' := 0x80) (by decide)
  have k8 := u8.oldReg u7.self.zero
  have a1_8 : reg n8 a1 = BitVec.ofNat 32 (W + (d + addr.toNat) % 4 + 3) := by
    rw [u8.newReg (by decide)]; show reg n7 a1 + 0x3 = _
    rw [u7.newReg (by decide)]; show reg n6 (26 : Fin 32) + reg n6 (8 : Fin 32) + 0x3 = _
    rw [s10_6, sk_, ofNat_add_lit, show (0x3 : Word) = BitVec.ofNat 32 3 from rfl, ofNat_add_lit]
  obtain ⟨n9, d9, u9⟩ := u8.self.aluImm hcP frd_at_80 (off' := 0x84) (by decide)
  have k9 := u9.oldReg u8.self.zero
  obtain ⟨wd, hwd⟩ : ∃ wd, (W + (d + addr.toNat) % 4 + 3) / 4 = wd := ⟨_, rfl⟩
  have hwd4 : 4 * wd ≤ 256 + 3 := by rw [← hwd]; omega
  have hwd4' : 4 * wd ≤ 256 := by rw [← hwd]; omega
  have hwdc : (d + addr.toNat) % 4 + W ≤ 4 * wd := by rw [← hwd]; omega
  have a2_9 : reg n9 a2 = BitVec.ofNat 32 wd := by
    rw [u9.newReg (by decide)]; apply BitVec.eq_of_toNat_eq
    rw [tn_srl (a := reg n8 a1) (k := 0x2) rfl, a1_8, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (0x2 : Word).toNat % 32 = 2 from rfl]
    omega
  obtain ⟨n10, d10, u10⟩ := u9.self.aluImm hcP frd_at_84 (off' := 0x86) (by decide)
  have k10 := u10.oldReg u9.self.zero
  obtain ⟨al, hal⟩ : ∃ al, BitVec.ofNat 32 ((d + addr.toNat) / 4 * 4) = al := ⟨_, rfl⟩
  have hal4 : al.toNat = (d + addr.toNat) / 4 * 4 := by rw [← hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have a0_10 : reg n10 a0 = al := by
    rw [u10.newReg (by decide)]; show reg n9 a0 &&& 0xFFFFFFFC = _
    rw [k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), k4 _ (by decide),
      k3 _ (by decide), a0_1]
    apply BitVec.eq_of_toNat_eq; rw [and_cmask, hpos, hal4]
  obtain ⟨n11, d11, u11⟩ := u10.self.aluImm hcP frd_at_86 (off' := 0x88) (by decide)
  have k11 := u11.oldReg u10.self.zero
  have sp10 : reg n10 sp = F := by
    rw [k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide),
      k4 _ (by decide), k3 _ (by decide), k1 _ (by decide), hsp]
  have a1_11 : reg n11 a1 = F + 0xC := by
    rw [u11.newReg (by decide)]; show reg n10 sp + 0xC = _; rw [sp10]
  -- 0x88: the call to `rom::flash_read_words`
  obtain ⟨n12, c12, pc12, mem12, regs12⟩ := u11.self.callRa hcP frd_at_88 frd_at_8c (cb := P + 0xFFFFFFE8)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hPe 0xFFFFFFE8 (by decide))
  have r12 := PEnv.reg1 regs12 u11.self.zero
  have hwn : (BitVec.ofNat 32 wd).toNat = wd := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have RE : RFWEnv n12.mem (P + 0xFFFFFFE8) G (F + 0xC) (BitVec.ofNat 32 wd) R := by
    rw [mem12]
    refine ⟨by rw [env.hP]; rfl, hcW, env.hG, env.hR, by omega, fr_al' hFa (by decide), ?_, ?_, ?_, ?_⟩
    · rw [hwn, BitVec.toNat_add, show (0xC : Word).toNat = 12 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
    · have := env.sGW.sub (c := 0) (l := 16 + R) (by omega); rwa [add_ofNat_zero] at this
    · rw [hwn, show F + 0xC = G + BitVec.ofNat 32 (16 + R + 12) from fG 12]
      exact env.sGW.sub (c := 16 + R + 12) (l := 4 * wd) (by omega)
    · rw [hwn, show F + 0xC = G + BitVec.ofNat 32 (16 + R + 12) from fG 12]
      have := sep_offsets G (c := 16 + R + 12) (n := 4 * wd) (d := 0) (k := 16 + R) (.inr (by omega)) (by omega)
        (by omega)
      rwa [add_ofNat_zero] at this
  obtain ⟨n13, c13, pc13, sp13, k13, a013, by13, fr13⟩ := romFlashReadWords_correct hROM n12 RE pc12
    (by rw [r12 _ (by decide), k11 _ (by decide), a0_10])
    (by rw [r12 _ (by decide), a1_11])
    (by rw [r12 _ (by decide), k11 _ (by decide), k10 _ (by decide), a2_9])
    (by rw [regs12]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P hPe (0x88 + 8) (by decide)))
    (by rw [r12 _ (by decide), k11 _ (by decide), sp10, hF])
    (by rw [hal4]; omega)
    (fun i hi => by
      rw [mem12, hfr _ (env.sGR.subR (c := i) (l := 1) (by omega)) (env.sOR.subR (c := i) (l := 1) (by omega))]
      exact env.rom i hi)
    (by have := env.sGR.sub (c := 0) (l := 16 + R) (by omega); rwa [add_ofNat_zero] at this)
  rw [hwn] at by13 fr13
  have cst : ∀ q, romKeep q = true → q ≠ (8 : Fin 32) → q ≠ (26 : Fin 32) → reg n13 q = reg n q := by
    intro q hq h8 h26
    have hra : q ≠ ra := fun e => by subst e; exact absurd hq (by decide)
    have ha0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
    have ha1 : q ≠ a1 := fun e => by subst e; exact absurd hq (by decide)
    have ha2 : q ≠ a2 := fun e => by subst e; exact absurd hq (by decide)
    rw [k13 q hq, r12 q hra, k11 q ha1, k10 q ha0, k9 q ha2, k8 q ha1, k7 q ha1, k6 q h26, k5 q h26, k4 q ha1,
      k3 q h8, k1 q ha0]
  have hBF : ∀ x, Sep G (0x150 + R) x 1 → Sep G (16 + R) x 1 ∧ Sep (F + 0xC) (4 * wd) x 1 := fun x hx => by
    refine ⟨by have := hx.sub (c := 0) (l := 16 + R) (by omega); rwa [add_ofNat_zero] at this, ?_⟩
    rw [show F + 0xC = G + BitVec.ofNat 32 (16 + R + 12) from fG 12]
    exact hx.sub (c := 16 + R + 12) (l := 4 * wd) (by omega)
  have fr13G : ∀ x, Sep G (0x150 + R) x 1 → n13.mem x = Mo x := fun x hx => by
    rw [fr13 x (hBF x hx).1 (hBF x hx).2, mem12]
  have hc13 : CodeIn n13.mem P flashReadCode := fun i hi => by
    rw [fr13G _ (env.sGC.subR (c := i) (l := 1) (by omega))]; exact hcP i hi
  have w13 : St n13.mem P n13 0x90 (reg n13) := ⟨by rw [pc13], rfl, fun _ => rfl⟩
  have s7_13 : reg n13 (23 : Fin 32) = BitVec.ofNat 32 d := by rw [cst _ (by decide) (by decide) (by decide), h23]
  have s5_13 : reg n13 (21 : Fin 32) = len := by rw [cst _ (by decide) (by decide) (by decide), h21]
  have sp_13 : reg n13 sp = F := by rw [sp13, hF]
  have hslF : ∀ i, i < 0x30 → Sep G (16 + R) (F + BitVec.ofNat 32 (0x110 + i)) 1 ∧
      Sep (F + 0xC) (4 * wd) (F + BitVec.ofNat 32 (0x110 + i)) 1 := fun i hi => by
    rw [fG (0x110 + i), show F + 0xC = G + BitVec.ofNat 32 (16 + R + 12) from fG 12]
    refine ⟨?_, sep_offsets G (.inl (by omega)) (by omega) (by omega)⟩
    have := sep_offsets G (c := 0) (n := 16 + R) (d := 16 + R + (0x110 + i)) (k := 1) (.inl (by omega)) (by omega)
      (by omega)
    rwa [add_ofNat_zero] at this
  -- 0x90 `beqz a0`: a failed read ends the loop
  rcases a013 with h0 | h1
  · obtain ⟨n14, d14, u14⟩ := w13.taken hc13 0xE4 frd_at_90 (by decide) (by
      simp only [branchTaken, h0, w13.zero]; decide)
    refine ⟨n14, n13.mem, d, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (c6.trans (.cons d7 (.cons d8 (.cons d9
      (.cons d10 (.cons d11 (c12.trans (c13.trans (.single d14))))))))))))), u14.self, ?_, ?_, ?_, by omega,
      fun h => absurd h (by omega), ?_, ?_, fun q hq h8 _ h26 => by rw [u14.regs, cst q hq h8 h26]⟩
    · rw [u14.regs, s7_13]
    · rw [u14.regs, s5_13]
    · rw [u14.regs, sp_13]
    · intro x hx ho; rw [fr13G x hx, hfr x hx ho]
    · intro i hi; rw [fr13 _ (hslF i hi).1 (hslF i hi).2, mem12, hsl i hi]
  have hdl' : d < 2 ^ 32 := hdl
  obtain ⟨n14, d14, u14⟩ := w13.notTaken hc13 0x92 frd_at_90 (by decide) (by
    simp only [branchTaken, h1, w13.zero]; decide)
  have s10_13 : reg n13 (26 : Fin 32) = BitVec.ofNat 32 W := by
    rw [k13 _ (by decide), r12 _ (by decide), k11 _ (by decide), k10 _ (by decide), k9 _ (by decide),
      k8 _ (by decide), k7 _ (by decide), s10_6]
  -- 0x92..0x98: the countdown, the destination, and the bytes read so far
  obtain ⟨n15, d15, u15⟩ := u14.alu hc13 frd_at_92 (off' := 0x96) (by decide)
  have a0_15 : reg n15 a0 = BitVec.ofNat 32 (2 ^ 32 - W) := by
    rw [u15.newReg (by decide)]; show reg n13 0 - reg n13 (26 : Fin 32) = _
    rw [w13.zero, s10_13]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, zero_toNat]; omega
  have k15 := u15.oldReg u14.self.zero
  obtain ⟨n16, d16, u16⟩ := u15.self.alu hc13 frd_at_96 (off' := 0x98) (by decide)
  have a1_16 : reg n16 a1 = out := by
    rw [u16.newReg (by decide)]; show reg n15 0 + reg n15 (19 : Fin 32) = _
    rw [u15.self.zero, k15 _ (by decide), cst _ (by decide) (by decide) (by decide), h19]
    exact BitVec.zero_add _
  have k16 := u16.oldReg u15.self.zero
  obtain ⟨n17, d17, u17⟩ := u16.self.alu hc13 frd_at_98 (off' := 0x9A) (by decide)
  have a2_17 : reg n17 a2 = BitVec.ofNat 32 d := by
    rw [u17.newReg (by decide)]; show reg n16 0 + reg n16 (23 : Fin 32) = _
    rw [u16.self.zero, k16 _ (by decide), k15 _ (by decide), s7_13]; exact BitVec.zero_add _
  have k17 := u17.oldReg u16.self.zero
  have a0_17 : reg n17 a0 = BitVec.ofNat 32 (2 ^ 32 - W) := by rw [k17 _ (by decide), k16 _ (by decide), a0_15]
  have a1_17 : reg n17 a1 = out := by rw [k17 _ (by decide), a1_16]
  -- 0x9A `beqz a0`: the chunk is not empty
  obtain ⟨n18, d18, u18⟩ := u17.self.notTaken hc13 0x9C frd_at_9a (by decide) (by
    simp only [branchTaken, a0_17, u17.self.zero]
    exact beq_toNat (by rw [BitVec.toNat_ofNat, zero_toNat]; omega))
  have c18 : ∀ q, romKeep q = true → q ≠ (8 : Fin 32) → q ≠ (26 : Fin 32) → reg n18 q = reg n q := by
    intro q hq h8 h26
    have ha0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
    have ha1 : q ≠ a1 := fun e => by subst e; exact absurd hq (by decide)
    have ha2 : q ≠ a2 := fun e => by subst e; exact absurd hq (by decide)
    rw [u18.regs, k17 q ha2, k16 q ha1, k15 q ha0, cst q hq h8 h26]
  have s0_18 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 ((d + addr.toNat) % 4) := by
    rw [u18.regs, k17 _ (by decide), k16 _ (by decide), k15 _ (by decide), k13 _ (by decide),
      r12 _ (by decide), k11 _ (by decide), k10 _ (by decide), k9 _ (by decide), k8 _ (by decide),
      k7 _ (by decide), sk_]
  have s8_18 : reg n18 (24 : Fin 32) = 0xFF := by rw [c18 _ (by decide) (by decide) (by decide), h24]
  have s1_18 : reg n18 (9 : Fin 32) = out + len := by rw [c18 _ (by decide) (by decide) (by decide), h9]
  have hsk255 : ¬ (0xFF : Word).ult (BitVec.ofNat 32 ((d + addr.toNat) % 4)) := by
    rw [show (0xFF : Word) = BitVec.ofNat 32 255 from rfl, ult_lit (by omega) (by omega)]; simp only [decide_eq_true_eq]
    omega
  -- 0x9C..0xBA: the bounds checks before the copy
  obtain ⟨nA, cA, uA, a0A, a1A, kA⟩ : ∃ nA, Steps n18 nA ∧ St n13.mem P nA 0xA6 (reg nA) ∧
      reg nA a0 = BitVec.ofNat 32 (2 ^ 32 - W) ∧ reg nA a1 = out + BitVec.ofNat 32 (d + 0) ∧
      ∀ q, q ≠ a1 → q ≠ a3 → reg nA q = reg n18 q := by
    by_cases hd0 : d = 0
    · subst hd0
      obtain ⟨n19, d19, u19⟩ := u18.self.notTaken hc13 0x9E frd_at_9c (by decide) (by
        simp only [branchTaken, u18.regs, a2_17, u17.self.zero]; decide)
      obtain ⟨n20, d20, u20⟩ := u19.self.notTaken hc13 0xA2 frd_at_9e (by decide) (by
        simp only [branchTaken, u19.regs, u18.regs, a1_17]; rw [← u18.regs, s1_18]
        exact beq_toNat (by rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega))
      obtain ⟨n21, d21, u21⟩ := u20.self.notTaken hc13 0xA6 frd_at_a2 (by decide) (by
        simp only [branchTaken, u20.regs, u19.regs, s8_18, s0_18]; exact Bool.eq_false_iff.mpr hsk255)
      refine ⟨n21, .cons d19 (.cons d20 (.single d21)), u21.self, ?_, ?_, fun q _ _ => ?_⟩
      · rw [u21.regs, u20.regs, u19.regs, u18.regs, a0_17]
      · rw [u21.regs, u20.regs, u19.regs, u18.regs, a1_17, add_ofNat_zero]
      · rw [u21.regs, u20.regs, u19.regs]
    · obtain ⟨n19, d19, u19⟩ := u18.self.taken hc13 0xB0 frd_at_9c (by decide) (by
        simp only [branchTaken, u18.regs, a2_17, u17.self.zero]
        exact bne_toNat (by rw [BitVec.toNat_ofNat, zero_toNat]; omega))
      obtain ⟨n20, d20, u20⟩ := u19.self.alu hc13 frd_at_b0 (off' := 0xB4) (by decide)
      have a3_20 : reg n20 a3 = len := by
        rw [u20.newReg (by decide)]; show reg n19 (9 : Fin 32) - reg n19 a1 = _
        rw [u19.regs, u19.regs, s1_18, u18.regs, a1_17]; apply BitVec.eq_of_toNat_eq
        have := len.isLt
        rw [BitVec.toNat_sub, BitVec.toNat_add, Nat.mod_eq_of_lt env.hlen]; omega
      have k20 := u20.oldReg u19.self.zero
      obtain ⟨n21, d21, u21⟩ := u20.self.notTaken hc13 0xB8 frd_at_b4 (by decide) (by
        simp only [branchTaken, k20 a2 (by decide), u19.regs, u18.regs, a2_17, a3_20]
        rw [← ofNat_toNat_self len, ult_lit (by omega) len.isLt, decide_eq_true (by omega : d < len.toNat)]; rfl)
      obtain ⟨n22, d22, u22⟩ := u21.self.alu hc13 frd_at_b8 (off' := 0xBA) (by decide)
      have a1_22 : reg n22 a1 = out + BitVec.ofNat 32 (d + 0) := by
        rw [u22.newReg (by decide)]; show reg n21 a1 + reg n21 a2 = _
        rw [u21.regs, u21.regs, k20 _ (by decide), k20 _ (by decide), u19.regs, u19.regs, u18.regs, u18.regs, a1_17,
          a2_17, Nat.add_zero]
      have k22 := u22.oldReg u21.self.zero
      obtain ⟨n23, d23, u23⟩ := u22.self.taken hc13 0xA6 frd_at_ba (by decide) (by
        simp only [branchTaken]
        rw [k22 (24 : Fin 32) (by decide), k22 (8 : Fin 32) (by decide), u21.regs, u21.regs, k20 (24 : Fin 32) (by decide),
          k20 (8 : Fin 32) (by decide), u19.regs, u19.regs, s8_18, s0_18, Bool.eq_false_iff.mpr hsk255]; rfl)
      refine ⟨n23, .cons d19 (.cons d20 (.cons d21 (.cons d22 (.single d23)))), u23.self, ?_, ?_, fun q h1 h3 => ?_⟩
      · rw [u23.regs, k22 _ (by decide), u21.regs, k20 _ (by decide), u19.regs, u18.regs, a0_17]
      · rw [u23.regs, a1_22]
      · rw [u23.regs, k22 _ h1, u21.regs, k20 _ h3, u19.regs]
  have cpre : Steps n n18 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (c6.trans (.cons d7 (.cons d8 (.cons d9
    (.cons d10 (.cons d11 (c12.trans (c13.trans (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.single d18)))))))))))))))))
  have cA' : ∀ q, romKeep q = true → q ≠ (8 : Fin 32) → q ≠ (26 : Fin 32) → reg nA q = reg n q := by
    intro q hq h8 h26
    have ha1 : q ≠ a1 := fun e => by subst e; exact absurd hq (by decide)
    have ha3 : q ≠ a3 := fun e => by subst e; exact absurd hq (by decide)
    rw [kA q ha1 ha3, c18 q hq h8 h26]
  have hSF : ∀ x, Sep G (0x150 + R) x 1 → Sep (F + 0x10C) 4 x 1 := fun x hx => by
    rw [show F + 0x10C = G + BitVec.ofNat 32 (16 + R + 0x10C) from fG 0x10C]
    exact hx.sub (c := 16 + R + 0x10C) (l := 4) (by omega)
  have eC : F + 0xC = G + BitVec.ofNat 32 (16 + R + 0xC) := fG 0xC
  have eS : F + 0x10C = G + BitVec.ofNat 32 (16 + R + 0x10C) := fG 0x10C
  have sSC : Sep (F + 0x10C) 4 P flashReadCode.length := by
    rw [eS]; exact env.sGC.sub (c := 16 + R + 0x10C) (l := 4) (by omega)
  have sOB : Sep out len.toNat (F + 0xC) 0x100 := by
    rw [eC]; exact env.sOG.subR (c := 16 + R + 0xC) (l := 0x100) (by omega)
  have sOS : Sep out len.toNat (F + 0x10C) 4 := by
    rw [eS]; exact env.sOG.subR (c := 16 + R + 0x10C) (l := 4) (by omega)
  -- 0xA6..0xDE: copy the chunk out of the bounce buffer
  obtain ⟨nB, Mw, cB, uB, cpB, frB, kB⟩ := frd_inner (O := out) (L := len.toNat) (d := d)
    (sk := (d + addr.toNat) % 4) (W := W) hPe hc13 hFa env.sOC sSC sOB sOS
    env.hlen hWs hWd W 0 nA n13.mem (Nat.zero_add W) hW1 uA a1A
    (by rw [kA _ (by decide) (by decide), s0_18]; rfl)
    a0A
    (by rw [kA _ (by decide) (by decide), s1_18, ofNat_toNat_self])
    (by rw [cA' _ (by decide) (by decide) (by decide), h22])
    (by rw [kA _ (by decide) (by decide), s8_18])
    (by rw [cA' _ (by decide) (by decide) (by decide), h25])
    (by rw [cA' _ (by decide) (by decide) (by decide), hsp])
    (fun t ht => absurd ht (Nat.not_lt_zero _)) (fun _ _ _ => rfl)
  have frW : ∀ x, Sep G (0x150 + R) x 1 → Sep out len.toNat x 1 → Mw x = Mo x := fun x h1 h2 => by
    rw [frB x (hSF x h1) (h2.sub (c := d) (l := W) hWd), fr13G x h1]
  have hcB : CodeIn Mw P flashReadCode := fun i hi => by
    rw [frW _ (env.sGC.subR (c := i) (l := 1) (by omega)) (env.sOC.subR (c := i) (l := 1) (by omega))]
    exact hcP i hi
  have hcp' : ∀ i, i < d + W → Mw (out + BitVec.ofNat 32 i) = flash (addr.toNat + i) := by
    intro i hi
    by_cases hid : i < d
    · have hO1 := env.sOG.sub (c := i) (l := 1) (by omega)
      rw [frB _ (hSF _ hO1.symm) (sep_offsets out (c := d) (n := W) (d := i) (k := 1) (.inr (by omega)) (by omega)
        (by omega)), fr13G _ hO1.symm, hcp i hid]
    · obtain ⟨t, rfl⟩ : ∃ t, i = d + t := ⟨i - d, by omega⟩
      rw [cpB t (by omega), by13 h1 ((d + addr.toNat) % 4 + t) (by omega), hal4]
      congr 1; omega
  have hfr' : ∀ x, Sep G (0x150 + R) x 1 → Sep out len.toNat x 1 → Mw x = M0 x := fun x h1 h2 => by
    rw [frW x h1 h2, hfr x h1 h2]
  have hsl' : ∀ i, i < 0x30 → Mw (F + BitVec.ofNat 32 (0x110 + i)) = Mp (F + BitVec.ofNat 32 (0x110 + i)) := by
    intro i hi
    rw [frB _ (by rw [eS, fG]; exact sep_offsets G (.inl (by omega)) (by omega) (by omega))
      (by rw [fG]; exact (env.sOG.sub (c := d) (l := W) hWd).subR (c := 16 + R + (0x110 + i)) (l := 1) (by omega)),
      fr13 _ (hslF i hi).1 (hslF i hi).2, mem12, hsl i hi]
  -- 0xDE `add s7, s7, s10`, 0xE0 `bltu s7, s5`: loop while bytes remain
  have s10_A : reg nA (26 : Fin 32) = BitVec.ofNat 32 W := by
    rw [kA _ (by decide) (by decide), u18.regs, k17 _ (by decide), k16 _ (by decide), k15 _ (by decide), s10_13]
  obtain ⟨nC, dC, uC⟩ := uB.alu hcB frd_at_de (off' := 0xE0) (by decide)
  have s7_C : reg nC (23 : Fin 32) = BitVec.ofNat 32 (d + W) := by
    rw [uC.newReg (by decide)]; show reg nB (23 : Fin 32) + reg nB (26 : Fin 32) = _
    rw [kB _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      kB (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s10_A,
      cA' _ (by decide) (by decide) (by decide), h23, ofNat_add_lit]
  have kC := uC.oldReg uB.zero
  have cC : ∀ q, romKeep q = true → q ≠ (8 : Fin 32) → q ≠ (26 : Fin 32) → q ≠ (23 : Fin 32) →
      reg nC q = reg n q := by
    intro q hq h8 h26 h23
    have ha0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
    have ha1 : q ≠ a1 := fun e => by subst e; exact absurd hq (by decide)
    have ha2 : q ≠ a2 := fun e => by subst e; exact absurd hq (by decide)
    have ha3 : q ≠ a3 := fun e => by subst e; exact absurd hq (by decide)
    have ha4 : q ≠ a4 := fun e => by subst e; exact absurd hq (by decide)
    rw [kC q h23, kB q ha0 ha1 ha2 ha3 ha4 h8, cA' q hq h8 h26]
  have s5_C : reg nC (21 : Fin 32) = len := by rw [cC _ (by decide) (by decide) (by decide) (by decide), h21]
  have hdW : d + W < 2 ^ 32 := by omega
  by_cases hlt : d + W < len.toNat
  · obtain ⟨nD, dD, uD⟩ := uC.self.taken hcB 0x60 frd_at_e0 (by decide) (by
      simp only [branchTaken, s7_C, s5_C]
      rw [← ofNat_toNat_self len, ult_lit hdW len.isLt]; exact decide_eq_true hlt)
    have cD : ∀ q, romKeep q = true → q ≠ (8 : Fin 32) → q ≠ (26 : Fin 32) → q ≠ (23 : Fin 32) →
        reg nD q = reg n q := fun q hq h8 h26 h23 => by rw [uD.regs, cC q hq h8 h26 h23]
    obtain ⟨n', M', d', cE, rest⟩ := ih (d + W) nD Mw (by omega) hlt uD.self
      (by rw [cD _ (by decide) (by decide) (by decide) (by decide), h18])
      (by rw [cD _ (by decide) (by decide) (by decide) (by decide), h19])
      (by rw [cD _ (by decide) (by decide) (by decide) (by decide), h21])
      (by rw [cD _ (by decide) (by decide) (by decide) (by decide), h20])
      (by rw [cD _ (by decide) (by decide) (by decide) (by decide), h22, hF])
      (by rw [uD.regs, s7_C])
      (by rw [cD _ (by decide) (by decide) (by decide) (by decide), h24])
      (by rw [cD _ (by decide) (by decide) (by decide) (by decide), h25, hF])
      (by rw [cD _ (by decide) (by decide) (by decide) (by decide), h9])
      (by rw [cD _ (by decide) (by decide) (by decide) (by decide), hsp, hF])
      hcp' hfr' (by rw [hF]; exact hsl')
    rw [hF] at rest
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, rk⟩ := rest
    exact ⟨n', M', d', cpre.trans (cA.trans (cB.trans (.cons dC (.cons dD cE)))), r1, r2, r3, r4, r5, r6, r7, r8,
      fun q hq h8 h23 h26 => by rw [rk q hq h8 h23 h26, cD q hq h8 h26 h23]⟩
  · obtain ⟨nD, dD, uD⟩ := uC.self.notTaken hcB 0xE4 frd_at_e0 (by decide) (by
      simp only [branchTaken, s7_C, s5_C]
      rw [← ofNat_toNat_self len, ult_lit hdW len.isLt]; exact decide_eq_false hlt)
    refine ⟨nD, Mw, d + W, cpre.trans (cA.trans (cB.trans (.cons dC (.single dD)))), uD.self, ?_, ?_, ?_, hWd,
      fun h i hi => hcp' i (by omega), hfr', hsl', fun q hq h8 h23 h26 => by rw [uD.regs, cC q hq h8 h26 h23]⟩
    · rw [uD.regs, s7_C]
    · rw [uD.regs, s5_C]
    · rw [uD.regs, cC _ (by decide) (by decide) (by decide) (by decide), hsp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The compiled `c3_bootloader::flash::read`**, called with a flash address
`addr` and the slice `out` of `len` bytes, with the 0x140 bytes of its frame
and `romStack` more for the ROM below `sp`: it returns 1 or 0 in `a0`, with
`sp` and the callee-saved registers as they were. When it returns 1, `out`
holds the `len` bytes of `flash` from `addr`. Either way it changes no memory
outside its stack and `out`. -/
theorem flashRead_correct {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat}
    (hROM : RomRead flash R romBase romCode) (m : Machine)
    {P G addr out len retAddr : Word} (env : FRdEnv m.mem P G out len R romBase romCode) (hpc : m.pc = P)
    (ha0 : reg m a0 = addr) (ha1 : reg m a1 = out) (ha2 : reg m a2 = len) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = G + BitVec.ofNat 32 (0x150 + R)) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = G + BitVec.ofNat 32 (0x150 + R) ∧
      (∀ q, romKeep q = true → reg m' q = reg m q) ∧ (reg m' a0 = 0 ∨ reg m' a0 = 1) ∧
      (reg m' a0 = 1 → ∀ i, i < len.toNat → m'.mem (out + BitVec.ofNat 32 i) = flash (addr.toNat + i)) ∧
      ∀ x, Sep G (0x150 + R) x 1 → Sep out len.toNat x 1 → m'.mem x = m.mem x := by
  obtain ⟨F, hF⟩ : ∃ F, G + BitVec.ofNat 32 (16 + R) = F := ⟨_, rfl⟩
  have hGt := env.hGt
  have hlen := env.hlen
  have hPe : P.toNat % 2 = 0 := by rw [env.hP]; decide
  have hFn : F.toNat = G.toNat + (16 + R) := by
    rw [← hF, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 + R) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hG (k := 16 + R) (by have := env.hR; omega)
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (16 + R + c) := fun c => by
    rw [← hF, add_ofNat_assoc]
  have hFsp : G + BitVec.ofNat 32 (0x150 + R) + 0xFFFFFEC0 = F := by
    rw [← hF, BitVec.add_assoc, show (0xFFFFFEC0 : Word) = BitVec.ofNat 32 4294966976 from rfl, ofNat_add_ofNat]
    rw [show BitVec.ofNat 32 (0x150 + R + 4294966976) = BitVec.ofNat 32 (16 + R) from
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)]
  have hspF : F + 0x140 = G + BitVec.ofNat 32 (0x150 + R) := by
    rw [show (0x140 : Word) = BitVec.ofNat 32 0x140 from rfl, fG, show 16 + R + 0x140 = 0x150 + R by omega]
  have sFC : Sep F 0x140 P flashReadCode.length := by
    rw [← hF]; exact env.sGC.sub (c := 16 + R) (l := 0x140) (by omega)
  have sFM : Sep F 0x140 (P + 0x1309E) memsetCode.length := by
    rw [← hF]; exact env.sGM.sub (c := 16 + R) (l := 0x140) (by omega)
  have inF : ∀ x, Sep G (0x150 + R) x 1 → Sep F 0x140 x 1 := fun x hx => by
    rw [← hF]; exact hx.sub (c := 16 + R) (l := 0x140) (by omega)
  -- the prologue: the frame, and `ra` and `s0` through `s10` saved at its top
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code frd_at_0 (off' := 2) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.aluImm env.code frd_at_2 (off' := 4) (by decide)
  have r2sp : reg m2 sp = F := by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [hsp, hFsp]
  have r2a3 : reg m2 a3 = F + 0x100 := by
    rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [hsp, hFsp]
  have rk2 : ∀ r, r ≠ sp → r ≠ a3 → reg m2 r = reg m r := fun r h1 h2 => by
    rw [u2.regs]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, h1, h2]
  obtain ⟨p0, dp0, up0⟩ := u2.self.swG env.code frd_at_4 (off' := 0x8) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x13C) (v := reg m ra)
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P0, hP0⟩ : ∃ M', memStore32 m.mem (F + 0x13C) (reg m ra) = M' := ⟨_, rfl⟩
  rw [hP0] at up0
  have hcp0 : CodeIn P0 P flashReadCode := by rw [← hP0]; exact env.code.store32 (frm_sep' sFC (by decide))
  obtain ⟨p1, dp1, up1⟩ := up0.swG hcp0 frd_at_8 (off' := 0xA) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x138) (v := reg m (8 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P1, hP1⟩ : ∃ M', memStore32 P0 (F + 0x138) (reg m (8 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP1] at up1
  have hcp1 : CodeIn P1 P flashReadCode := by rw [← hP1]; exact hcp0.store32 (frm_sep' sFC (by decide))
  obtain ⟨p2, dp2, up2⟩ := up1.swG hcp1 frd_at_a (off' := 0xC) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x134) (v := reg m (9 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P2, hP2⟩ : ∃ M', memStore32 P1 (F + 0x134) (reg m (9 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP2] at up2
  have hcp2 : CodeIn P2 P flashReadCode := by rw [← hP2]; exact hcp1.store32 (frm_sep' sFC (by decide))
  obtain ⟨p3, dp3, up3⟩ := up2.swG hcp2 frd_at_c (off' := 0x10) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x130) (v := reg m (18 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P3, hP3⟩ : ∃ M', memStore32 P2 (F + 0x130) (reg m (18 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP3] at up3
  have hcp3 : CodeIn P3 P flashReadCode := by rw [← hP3]; exact hcp2.store32 (frm_sep' sFC (by decide))
  obtain ⟨p4, dp4, up4⟩ := up3.swG hcp3 frd_at_10 (off' := 0x14) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x12C) (v := reg m (19 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P4, hP4⟩ : ∃ M', memStore32 P3 (F + 0x12C) (reg m (19 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP4] at up4
  have hcp4 : CodeIn P4 P flashReadCode := by rw [← hP4]; exact hcp3.store32 (frm_sep' sFC (by decide))
  obtain ⟨p5, dp5, up5⟩ := up4.swG hcp4 frd_at_14 (off' := 0x18) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x128) (v := reg m (20 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P5, hP5⟩ : ∃ M', memStore32 P4 (F + 0x128) (reg m (20 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP5] at up5
  have hcp5 : CodeIn P5 P flashReadCode := by rw [← hP5]; exact hcp4.store32 (frm_sep' sFC (by decide))
  obtain ⟨p6, dp6, up6⟩ := up5.swG hcp5 frd_at_18 (off' := 0x1C) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x124) (v := reg m (21 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P6, hP6⟩ : ∃ M', memStore32 P5 (F + 0x124) (reg m (21 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP6] at up6
  have hcp6 : CodeIn P6 P flashReadCode := by rw [← hP6]; exact hcp5.store32 (frm_sep' sFC (by decide))
  obtain ⟨p7, dp7, up7⟩ := up6.swG hcp6 frd_at_1c (off' := 0x20) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x120) (v := reg m (22 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P7, hP7⟩ : ∃ M', memStore32 P6 (F + 0x120) (reg m (22 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP7] at up7
  have hcp7 : CodeIn P7 P flashReadCode := by rw [← hP7]; exact hcp6.store32 (frm_sep' sFC (by decide))
  obtain ⟨p8, dp8, up8⟩ := up7.swG hcp7 frd_at_20 (off' := 0x24) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x11C) (v := reg m (23 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P8, hP8⟩ : ∃ M', memStore32 P7 (F + 0x11C) (reg m (23 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP8] at up8
  have hcp8 : CodeIn P8 P flashReadCode := by rw [← hP8]; exact hcp7.store32 (frm_sep' sFC (by decide))
  obtain ⟨p9, dp9, up9⟩ := up8.swG hcp8 frd_at_24 (off' := 0x28) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x118) (v := reg m (24 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P9, hP9⟩ : ∃ M', memStore32 P8 (F + 0x118) (reg m (24 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP9] at up9
  have hcp9 : CodeIn P9 P flashReadCode := by rw [← hP9]; exact hcp8.store32 (frm_sep' sFC (by decide))
  obtain ⟨p10, dp10, up10⟩ := up9.swG hcp9 frd_at_28 (off' := 0x2C) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x114) (v := reg m (25 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P10, hP10⟩ : ∃ M', memStore32 P9 (F + 0x114) (reg m (25 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP10] at up10
  have hcp10 : CodeIn P10 P flashReadCode := by rw [← hP10]; exact hcp9.store32 (frm_sep' sFC (by decide))
  obtain ⟨p11, dp11, up11⟩ := up10.swG hcp10 frd_at_2c (off' := 0x30) (by decide)
    (by rw [r2a3, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x110) (v := reg m (26 : Fin 32))
    (by rw [r2a3, BitVec.add_assoc]; rfl) (rk2 _ (by decide) (by decide))
  obtain ⟨P11, hP11⟩ : ∃ M', memStore32 P10 (F + 0x110) (reg m (26 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP11] at up11
  have hcp11 : CodeIn P11 P flashReadCode := by rw [← hP11]; exact hcp10.store32 (frm_sep' sFC (by decide))
  have fpro : ∀ x, Sep F 0x140 x 1 → P11 x = m.mem x := fun x hx => by
    rw [← hP11, memStore32_get_sep (frm_sep' hx (by decide)), ← hP10, memStore32_get_sep (frm_sep' hx (by decide)), ← hP9, memStore32_get_sep (frm_sep' hx (by decide)), ← hP8, memStore32_get_sep (frm_sep' hx (by decide)), ← hP7, memStore32_get_sep (frm_sep' hx (by decide)), ← hP6, memStore32_get_sep (frm_sep' hx (by decide)), ← hP5, memStore32_get_sep (frm_sep' hx (by decide)), ← hP4, memStore32_get_sep (frm_sep' hx (by decide)), ← hP3, memStore32_get_sep (frm_sep' hx (by decide)), ← hP2, memStore32_get_sep (frm_sep' hx (by decide)), ← hP1, memStore32_get_sep (frm_sep' hx (by decide)), ← hP0, memStore32_get_sep (frm_sep' hx (by decide))]
  have sv13C : memLoad32 P11 (F + 0x13C) = reg m ra := by
    rw [← hP11, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x13C) 4 from sep_offsets F (c := 0x110) (n := 4) (d := 0x13C) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x13C) 4 from sep_offsets F (c := 0x114) (n := 4) (d := 0x13C) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x13C) 4 from sep_offsets F (c := 0x118) (n := 4) (d := 0x13C) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x13C) 4 from sep_offsets F (c := 0x11C) (n := 4) (d := 0x13C) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x13C) 4 from sep_offsets F (c := 0x120) (n := 4) (d := 0x13C) (k := 4) (by decide) (by decide) (by decide)), ← hP6, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x13C) 4 from sep_offsets F (c := 0x124) (n := 4) (d := 0x13C) (k := 4) (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x13C) 4 from sep_offsets F (c := 0x128) (n := 4) (d := 0x13C) (k := 4) (by decide) (by decide) (by decide)), ← hP4, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x13C) 4 from sep_offsets F (c := 0x12C) (n := 4) (d := 0x13C) (k := 4) (by decide) (by decide) (by decide)), ← hP3, memLoad32_store32_sep (show Sep (F + 0x130) 4 (F + 0x13C) 4 from sep_offsets F (c := 0x130) (n := 4) (d := 0x13C) (k := 4) (by decide) (by decide) (by decide)), ← hP2, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x13C) 4 from sep_offsets F (c := 0x134) (n := 4) (d := 0x13C) (k := 4) (by decide) (by decide) (by decide)), ← hP1, memLoad32_store32_sep (show Sep (F + 0x138) 4 (F + 0x13C) 4 from sep_offsets F (c := 0x138) (n := 4) (d := 0x13C) (k := 4) (by decide) (by decide) (by decide)), ← hP0, memLoad32_store32_same]
  have sv138 : memLoad32 P11 (F + 0x138) = reg m (8 : Fin 32) := by
    rw [← hP11, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x138) 4 from sep_offsets F (c := 0x110) (n := 4) (d := 0x138) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x138) 4 from sep_offsets F (c := 0x114) (n := 4) (d := 0x138) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x138) 4 from sep_offsets F (c := 0x118) (n := 4) (d := 0x138) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x138) 4 from sep_offsets F (c := 0x11C) (n := 4) (d := 0x138) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x138) 4 from sep_offsets F (c := 0x120) (n := 4) (d := 0x138) (k := 4) (by decide) (by decide) (by decide)), ← hP6, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x138) 4 from sep_offsets F (c := 0x124) (n := 4) (d := 0x138) (k := 4) (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x138) 4 from sep_offsets F (c := 0x128) (n := 4) (d := 0x138) (k := 4) (by decide) (by decide) (by decide)), ← hP4, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x138) 4 from sep_offsets F (c := 0x12C) (n := 4) (d := 0x138) (k := 4) (by decide) (by decide) (by decide)), ← hP3, memLoad32_store32_sep (show Sep (F + 0x130) 4 (F + 0x138) 4 from sep_offsets F (c := 0x130) (n := 4) (d := 0x138) (k := 4) (by decide) (by decide) (by decide)), ← hP2, memLoad32_store32_sep (show Sep (F + 0x134) 4 (F + 0x138) 4 from sep_offsets F (c := 0x134) (n := 4) (d := 0x138) (k := 4) (by decide) (by decide) (by decide)), ← hP1, memLoad32_store32_same]
  have sv134 : memLoad32 P11 (F + 0x134) = reg m (9 : Fin 32) := by
    rw [← hP11, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x134) 4 from sep_offsets F (c := 0x110) (n := 4) (d := 0x134) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x134) 4 from sep_offsets F (c := 0x114) (n := 4) (d := 0x134) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x134) 4 from sep_offsets F (c := 0x118) (n := 4) (d := 0x134) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x134) 4 from sep_offsets F (c := 0x11C) (n := 4) (d := 0x134) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x134) 4 from sep_offsets F (c := 0x120) (n := 4) (d := 0x134) (k := 4) (by decide) (by decide) (by decide)), ← hP6, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x134) 4 from sep_offsets F (c := 0x124) (n := 4) (d := 0x134) (k := 4) (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x134) 4 from sep_offsets F (c := 0x128) (n := 4) (d := 0x134) (k := 4) (by decide) (by decide) (by decide)), ← hP4, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x134) 4 from sep_offsets F (c := 0x12C) (n := 4) (d := 0x134) (k := 4) (by decide) (by decide) (by decide)), ← hP3, memLoad32_store32_sep (show Sep (F + 0x130) 4 (F + 0x134) 4 from sep_offsets F (c := 0x130) (n := 4) (d := 0x134) (k := 4) (by decide) (by decide) (by decide)), ← hP2, memLoad32_store32_same]
  have sv130 : memLoad32 P11 (F + 0x130) = reg m (18 : Fin 32) := by
    rw [← hP11, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x130) 4 from sep_offsets F (c := 0x110) (n := 4) (d := 0x130) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x130) 4 from sep_offsets F (c := 0x114) (n := 4) (d := 0x130) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x130) 4 from sep_offsets F (c := 0x118) (n := 4) (d := 0x130) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x130) 4 from sep_offsets F (c := 0x11C) (n := 4) (d := 0x130) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x130) 4 from sep_offsets F (c := 0x120) (n := 4) (d := 0x130) (k := 4) (by decide) (by decide) (by decide)), ← hP6, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x130) 4 from sep_offsets F (c := 0x124) (n := 4) (d := 0x130) (k := 4) (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x130) 4 from sep_offsets F (c := 0x128) (n := 4) (d := 0x130) (k := 4) (by decide) (by decide) (by decide)), ← hP4, memLoad32_store32_sep (show Sep (F + 0x12C) 4 (F + 0x130) 4 from sep_offsets F (c := 0x12C) (n := 4) (d := 0x130) (k := 4) (by decide) (by decide) (by decide)), ← hP3, memLoad32_store32_same]
  have sv12C : memLoad32 P11 (F + 0x12C) = reg m (19 : Fin 32) := by
    rw [← hP11, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x12C) 4 from sep_offsets F (c := 0x110) (n := 4) (d := 0x12C) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x12C) 4 from sep_offsets F (c := 0x114) (n := 4) (d := 0x12C) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x12C) 4 from sep_offsets F (c := 0x118) (n := 4) (d := 0x12C) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x12C) 4 from sep_offsets F (c := 0x11C) (n := 4) (d := 0x12C) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x12C) 4 from sep_offsets F (c := 0x120) (n := 4) (d := 0x12C) (k := 4) (by decide) (by decide) (by decide)), ← hP6, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x12C) 4 from sep_offsets F (c := 0x124) (n := 4) (d := 0x12C) (k := 4) (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_sep (show Sep (F + 0x128) 4 (F + 0x12C) 4 from sep_offsets F (c := 0x128) (n := 4) (d := 0x12C) (k := 4) (by decide) (by decide) (by decide)), ← hP4, memLoad32_store32_same]
  have sv128 : memLoad32 P11 (F + 0x128) = reg m (20 : Fin 32) := by
    rw [← hP11, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x128) 4 from sep_offsets F (c := 0x110) (n := 4) (d := 0x128) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x128) 4 from sep_offsets F (c := 0x114) (n := 4) (d := 0x128) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x128) 4 from sep_offsets F (c := 0x118) (n := 4) (d := 0x128) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x128) 4 from sep_offsets F (c := 0x11C) (n := 4) (d := 0x128) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x128) 4 from sep_offsets F (c := 0x120) (n := 4) (d := 0x128) (k := 4) (by decide) (by decide) (by decide)), ← hP6, memLoad32_store32_sep (show Sep (F + 0x124) 4 (F + 0x128) 4 from sep_offsets F (c := 0x124) (n := 4) (d := 0x128) (k := 4) (by decide) (by decide) (by decide)), ← hP5, memLoad32_store32_same]
  have sv124 : memLoad32 P11 (F + 0x124) = reg m (21 : Fin 32) := by
    rw [← hP11, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x124) 4 from sep_offsets F (c := 0x110) (n := 4) (d := 0x124) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x124) 4 from sep_offsets F (c := 0x114) (n := 4) (d := 0x124) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x124) 4 from sep_offsets F (c := 0x118) (n := 4) (d := 0x124) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x124) 4 from sep_offsets F (c := 0x11C) (n := 4) (d := 0x124) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_sep (show Sep (F + 0x120) 4 (F + 0x124) 4 from sep_offsets F (c := 0x120) (n := 4) (d := 0x124) (k := 4) (by decide) (by decide) (by decide)), ← hP6, memLoad32_store32_same]
  have sv120 : memLoad32 P11 (F + 0x120) = reg m (22 : Fin 32) := by
    rw [← hP11, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x120) 4 from sep_offsets F (c := 0x110) (n := 4) (d := 0x120) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x120) 4 from sep_offsets F (c := 0x114) (n := 4) (d := 0x120) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x120) 4 from sep_offsets F (c := 0x118) (n := 4) (d := 0x120) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_sep (show Sep (F + 0x11C) 4 (F + 0x120) 4 from sep_offsets F (c := 0x11C) (n := 4) (d := 0x120) (k := 4) (by decide) (by decide) (by decide)), ← hP7, memLoad32_store32_same]
  have sv11C : memLoad32 P11 (F + 0x11C) = reg m (23 : Fin 32) := by
    rw [← hP11, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x11C) 4 from sep_offsets F (c := 0x110) (n := 4) (d := 0x11C) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x11C) 4 from sep_offsets F (c := 0x114) (n := 4) (d := 0x11C) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x11C) 4 from sep_offsets F (c := 0x118) (n := 4) (d := 0x11C) (k := 4) (by decide) (by decide) (by decide)), ← hP8, memLoad32_store32_same]
  have sv118 : memLoad32 P11 (F + 0x118) = reg m (24 : Fin 32) := by
    rw [← hP11, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x118) 4 from sep_offsets F (c := 0x110) (n := 4) (d := 0x118) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_sep (show Sep (F + 0x114) 4 (F + 0x118) 4 from sep_offsets F (c := 0x114) (n := 4) (d := 0x118) (k := 4) (by decide) (by decide) (by decide)), ← hP9, memLoad32_store32_same]
  have sv114 : memLoad32 P11 (F + 0x114) = reg m (25 : Fin 32) := by
    rw [← hP11, memLoad32_store32_sep (show Sep (F + 0x110) 4 (F + 0x114) 4 from sep_offsets F (c := 0x110) (n := 4) (d := 0x114) (k := 4) (by decide) (by decide) (by decide)), ← hP10, memLoad32_store32_same]
  have sv110 : memLoad32 P11 (F + 0x110) = reg m (26 : Fin 32) := by
    rw [← hP11, memLoad32_store32_same]
  have cOf : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep F 0x140 b code.length →
      CodeIn P11 b code := fun hc hs i hi => by
    rw [fpro _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hcM := cOf env.mset sFM
  obtain ⟨n1, e1, v1⟩ := up11.alu hcp11 frd_at_30 (off' := 0x32) (by decide)
  have k1 := v1.oldReg up11.zero
  obtain ⟨n2, e2, v2⟩ := v1.self.alu hcp11 frd_at_32 (off' := 0x34) (by decide)
  have k2 := v2.oldReg v1.self.zero
  obtain ⟨n3, e3, v3⟩ := v2.self.alu hcp11 frd_at_34 (off' := 0x36) (by decide)
  have k3 := v3.oldReg v2.self.zero
  obtain ⟨n4, e4, v4⟩ := v3.self.aluImm hcp11 frd_at_36 (off' := 0x38) (by decide)
  have k4 := v4.oldReg v3.self.zero
  obtain ⟨n5, e5, v5⟩ := v4.self.aluImm hcp11 frd_at_38 (off' := 0x3A) (by decide)
  have k5 := v5.oldReg v4.self.zero
  obtain ⟨n6, e6, v6⟩ := v5.self.aluImm hcp11 frd_at_3a (off' := 0x3E) (by decide)
  have k6 := v6.oldReg v5.self.zero
  obtain ⟨n7, e7, v7⟩ := v6.self.aluImm hcp11 frd_at_3e (off' := 0x42) (by decide)
  have k7 := v7.oldReg v6.self.zero
  obtain ⟨n8, e8, v8⟩ := v7.self.aluImm hcp11 frd_at_42 (off' := 0x46) (by decide)
  have k8 := v8.oldReg v7.self.zero
  have x1 : reg n1 (21 : Fin 32) = len := by
    rw [v1.newReg (by decide)]; show reg m2 0 + reg m2 a2 = _
    rw [up11.zero, rk2 _ (by decide) (by decide), ha2]; exact BitVec.zero_add _
  have x2 : reg n2 (19 : Fin 32) = out := by
    rw [v2.newReg (by decide)]; show reg n1 0 + reg n1 a1 = _
    rw [v1.self.zero, k1 _ (by decide), rk2 _ (by decide) (by decide), ha1]; exact BitVec.zero_add _
  have x3 : reg n3 (18 : Fin 32) = addr := by
    rw [v3.newReg (by decide)]; show reg n2 0 + reg n2 a0 = _
    rw [v2.self.zero, k2 _ (by decide), k1 _ (by decide), rk2 _ (by decide) (by decide), ha0]; exact BitVec.zero_add _
  have x4 : reg n4 a1 = 0 := by
    rw [v4.newReg (by decide)]; show reg n3 0 + 0x0 = _; rw [v3.self.zero]; rfl
  have x5 : reg n5 a0 = F + 0xC := by
    rw [v5.newReg (by decide)]; show reg n4 sp + 0xC = _
    rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), r2sp]
  have x6 : reg n6 a2 = 0x100 := by
    rw [v6.newReg (by decide)]; show reg n5 0 + 0x100 = _; rw [v5.self.zero]; rfl
  have x7 : reg n7 (22 : Fin 32) = F + 0xC := by
    rw [v7.newReg (by decide)]; show reg n6 sp + 0xC = _
    rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), r2sp]
  have x8 : reg n8 (20 : Fin 32) = 0x100 := by
    rw [v8.newReg (by decide)]; show reg n7 0 + 0x100 = _; rw [v7.self.zero]; rfl
  -- 0x46: `memset` clears the bounce buffer
  obtain ⟨n9, c9, pc9, mem9, regs9⟩ := v8.self.callRa hcp11 frd_at_46 frd_at_4a (cb := P + 0x1309E)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hPe 0x1309E (by decide))
  have r9 := PEnv.reg1 regs9 v8.self.zero
  have hFC : (F + 0xC).toNat = F.toNat + 0xC := by
    rw [BitVec.toNat_add, show (0xC : Word).toNat = 0xC from rfl, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨n10, c10, pc10, mem10, a0_10, K10⟩ := memset_correct n9 (P + 0x1309E) (P + BitVec.ofNat 32 (0x46 + 8))
    (F + 0xC) 0 0x100 (fun i hi => by show n9.mem _ = _; rw [mem9]; exact hcM i hi) (even_at P hPe 0x1309E (by decide))
    pc9 (by rw [r9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), x5])
    (by rw [r9 _ (by decide), k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), x4])
    (by rw [r9 _ (by decide), k8 _ (by decide), k7 _ (by decide), x6]; try rfl)
    (by rw [regs9]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P hPe (0x46 + 8) (by decide)))
    (by rw [hFC]; omega) (sFM.sub (c := 0xC) (l := 0x100) (by decide))
  rw [mem9] at mem10
  obtain ⟨Mo, hMo⟩ : ∃ M, fillBytes P11 (F + 0xC) ((0 : Word).extractLsb' 0 8) 0x100 = M := ⟨_, rfl⟩
  rw [hMo] at mem10
  have bufF : ∀ x, Sep (F + 0xC) 0x100 x 1 → Mo x = P11 x := fun x hx => by rw [← hMo, fillBytes_sep hx (Nat.le_refl _)]
  have hcMo : CodeIn Mo P flashReadCode := fun i hi => by
    rw [bufF _ ((sFC.sub (c := 0xC) (l := 0x100) (by decide)).subR (c := i) (l := 1) (by omega))]; exact hcp11 i hi
  have w10 : St Mo P n10 0x4E (reg n10) := ⟨by rw [pc10], mem10, fun _ => rfl⟩
  obtain ⟨n11, e11, v11⟩ := w10.aluImm hcMo frd_at_4e (off' := 0x50) (by decide)
  have k11 := v11.oldReg w10.zero
  obtain ⟨n12, e12, v12⟩ := v11.self.alu hcMo frd_at_50 (off' := 0x54) (by decide)
  have k12 := v12.oldReg v11.self.zero
  obtain ⟨n13, e13, v13⟩ := v12.self.aluImm hcMo frd_at_54 (off' := 0x58) (by decide)
  have k13 := v13.oldReg v12.self.zero
  obtain ⟨n14, e14, v14⟩ := v13.self.aluImm hcMo frd_at_58 (off' := 0x5C) (by decide)
  have k14 := v14.oldReg v13.self.zero
  have x11 : reg n11 (23 : Fin 32) = BitVec.ofNat 32 0 := by
    rw [v11.newReg (by decide)]; show reg n10 0 + 0x0 = _; rw [w10.zero]; rfl
  have x12 : reg n12 (9 : Fin 32) = out + len := by
    rw [v12.newReg (by decide)]; show reg n11 (19 : Fin 32) + reg n11 (21 : Fin 32) = _
    rw [k11 (19 : Fin 32) (by decide), K10 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide), r9 (19 : Fin 32) (by decide), k8 (19 : Fin 32) (by decide), k7 (19 : Fin 32) (by decide), k6 (19 : Fin 32) (by decide), k5 (19 : Fin 32) (by decide), k4 (19 : Fin 32) (by decide), k3 (19 : Fin 32) (by decide), x2, k11 (21 : Fin 32) (by decide), K10 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide), r9 (21 : Fin 32) (by decide), k8 (21 : Fin 32) (by decide), k7 (21 : Fin 32) (by decide), k6 (21 : Fin 32) (by decide), k5 (21 : Fin 32) (by decide), k4 (21 : Fin 32) (by decide), k3 (21 : Fin 32) (by decide), k2 (21 : Fin 32) (by decide), x1]
  have x13 : reg n13 (24 : Fin 32) = 0xFF := by
    rw [v13.newReg (by decide)]; show reg n12 0 + 0xFF = _; rw [v12.self.zero]; rfl
  have x14 : reg n14 (25 : Fin 32) = F + 0x10C := by
    rw [v14.newReg (by decide)]; show reg n13 sp + 0x10C = _
    rw [k13 sp (by decide), k12 sp (by decide), k11 sp (by decide), K10 sp (by decide) (by decide) (by decide) (by decide) (by decide), r9 sp (by decide), k8 sp (by decide), k7 sp (by decide), k6 sp (by decide), k5 sp (by decide), k4 sp (by decide), k3 sp (by decide), k2 sp (by decide), k1 sp (by decide), r2sp]
  have y18 : reg n14 (18 : Fin 32) = addr := by rw [k14 (18 : Fin 32) (by decide), k13 (18 : Fin 32) (by decide), k12 (18 : Fin 32) (by decide), k11 (18 : Fin 32) (by decide), K10 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide), r9 (18 : Fin 32) (by decide), k8 (18 : Fin 32) (by decide), k7 (18 : Fin 32) (by decide), k6 (18 : Fin 32) (by decide), k5 (18 : Fin 32) (by decide), k4 (18 : Fin 32) (by decide), x3]
  have y19 : reg n14 (19 : Fin 32) = out := by rw [k14 (19 : Fin 32) (by decide), k13 (19 : Fin 32) (by decide), k12 (19 : Fin 32) (by decide), k11 (19 : Fin 32) (by decide), K10 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide), r9 (19 : Fin 32) (by decide), k8 (19 : Fin 32) (by decide), k7 (19 : Fin 32) (by decide), k6 (19 : Fin 32) (by decide), k5 (19 : Fin 32) (by decide), k4 (19 : Fin 32) (by decide), k3 (19 : Fin 32) (by decide), x2]
  have y21 : reg n14 (21 : Fin 32) = len := by rw [k14 (21 : Fin 32) (by decide), k13 (21 : Fin 32) (by decide), k12 (21 : Fin 32) (by decide), k11 (21 : Fin 32) (by decide), K10 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide), r9 (21 : Fin 32) (by decide), k8 (21 : Fin 32) (by decide), k7 (21 : Fin 32) (by decide), k6 (21 : Fin 32) (by decide), k5 (21 : Fin 32) (by decide), k4 (21 : Fin 32) (by decide), k3 (21 : Fin 32) (by decide), k2 (21 : Fin 32) (by decide), x1]
  have y20 : reg n14 (20 : Fin 32) = 0x100 := by rw [k14 (20 : Fin 32) (by decide), k13 (20 : Fin 32) (by decide), k12 (20 : Fin 32) (by decide), k11 (20 : Fin 32) (by decide), K10 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide), r9 (20 : Fin 32) (by decide), x8]
  have y22 : reg n14 (22 : Fin 32) = F + 0xC := by rw [k14 (22 : Fin 32) (by decide), k13 (22 : Fin 32) (by decide), k12 (22 : Fin 32) (by decide), k11 (22 : Fin 32) (by decide), K10 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide), r9 (22 : Fin 32) (by decide), k8 (22 : Fin 32) (by decide), x7]
  have y23 : reg n14 (23 : Fin 32) = BitVec.ofNat 32 0 := by rw [k14 (23 : Fin 32) (by decide), k13 (23 : Fin 32) (by decide), k12 (23 : Fin 32) (by decide), x11]
  have y24 : reg n14 (24 : Fin 32) = 0xFF := by rw [k14 (24 : Fin 32) (by decide), x13]
  have y9 : reg n14 (9 : Fin 32) = out + len := by rw [k14 (9 : Fin 32) (by decide), k13 (9 : Fin 32) (by decide), x12]
  have ysp : reg n14 sp = F := by rw [k14 sp (by decide), k13 sp (by decide), k12 sp (by decide), k11 sp (by decide), K10 sp (by decide) (by decide) (by decide) (by decide) (by decide), r9 sp (by decide), k8 sp (by decide), k7 sp (by decide), k6 sp (by decide), k5 sp (by decide), k4 sp (by decide), k3 sp (by decide), k2 sp (by decide), k1 sp (by decide), r2sp]
  have hfrMo : ∀ x, Sep G (0x150 + R) x 1 → Sep out len.toNat x 1 → Mo x = m.mem x := fun x hx _ => by
    rw [bufF x ((inF x hx).sub (c := 0xC) (l := 0x100) (by decide)), fpro x (inF x hx)]
  have hslMo : ∀ i, i < 0x30 → Mo (F + BitVec.ofNat 32 (0x110 + i)) = P11 (F + BitVec.ofNat 32 (0x110 + i)) :=
    fun i hi => bufF _ (sep_offsets F (c := 0xC) (n := 0x100) (d := 0x110 + i) (k := 1) (.inl (by omega)) (by omega)
      (by omega))
  -- 0x5C `beqz s5`, then the loop
  obtain ⟨nE, ME, dE, cE, uE, s7E, s5E, spE, hdE, hcpE, hfrE, hslE, rkE⟩ : ∃ n' M' d', Steps n14 n' ∧
      St M' P n' 0xE4 (reg n') ∧ reg n' (23 : Fin 32) = BitVec.ofNat 32 d' ∧ reg n' (21 : Fin 32) = len ∧
      reg n' sp = F ∧ d' ≤ len.toNat ∧
      (d' = len.toNat → ∀ i, i < len.toNat → M' (out + BitVec.ofNat 32 i) = flash (addr.toNat + i)) ∧
      (∀ x, Sep G (0x150 + R) x 1 → Sep out len.toNat x 1 → M' x = m.mem x) ∧
      (∀ i, i < 0x30 → M' (F + BitVec.ofNat 32 (0x110 + i)) = P11 (F + BitVec.ofNat 32 (0x110 + i))) ∧
      ∀ q, romKeep q = true → q ≠ (8 : Fin 32) → q ≠ (23 : Fin 32) → q ≠ (26 : Fin 32) → reg n' q = reg n14 q := by
    by_cases hl0 : len.toNat = 0
    · obtain ⟨n15, d15, u15⟩ := v14.self.taken hcMo 0xE4 frd_at_5c (by decide) (by
        have hl : len = 0 := BitVec.eq_of_toNat_eq (by rw [hl0]; rfl)
        simp only [branchTaken, y21, v14.self.zero]; rw [hl]; decide)
      exact ⟨n15, Mo, 0, .single d15, u15.self, by rw [u15.regs, y23], by rw [u15.regs, y21],
        by rw [u15.regs, ysp], Nat.zero_le _, fun _ i hi => absurd hi (by omega), hfrMo, hslMo,
        fun q _ _ _ _ => u15.regs q⟩
    · obtain ⟨n15, d15, u15⟩ := v14.self.notTaken hcMo 0x60 frd_at_5c (by decide) (by
        simp only [branchTaken, y21, v14.self.zero]
        exact beq_toNat (by rw [zero_toNat]; exact hl0))
      obtain ⟨n', M', d', c', rest⟩ := frd_outer hROM (Mp := P11) (addr := addr) env len.toNat 0 n15 Mo
        (by omega) (by omega) u15.self (by rw [u15.regs, y18]) (by rw [u15.regs, y19]) (by rw [u15.regs, y21])
        (by rw [u15.regs, y20]) (by rw [u15.regs, y22, hF]) (by rw [u15.regs, y23]) (by rw [u15.regs, y24])
        (by rw [u15.regs, x14, hF]) (by rw [u15.regs, y9]) (by rw [u15.regs, ysp, hF])
        (fun i hi => absurd hi (Nat.not_lt_zero _)) hfrMo (by rw [hF]; exact hslMo)
      rw [hF] at rest
      obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, rk⟩ := rest
      exact ⟨n', M', d', .cons d15 c', r1, r2, r3, r4, r5, r6, r7, r8,
        fun q hq h8 h23 h26 => by rw [rk q hq h8 h23 h26, u15.regs]⟩
  -- the result
  have hcE : CodeIn ME P flashReadCode := fun i hi => by
    rw [hfrE _ (env.sGC.subR (c := i) (l := 1) (by omega)) (env.sOC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  obtain ⟨f1, g1, w1⟩ := uE.alu hcE frd_at_e4 (off' := 0xE8) (by decide)
  obtain ⟨f2, g2, w2⟩ := w1.self.aluImm hcE frd_at_e8 (off' := 0xEC) (by decide)
  have hdE32 : dE < 2 ^ 32 := by have := len.isLt; omega
  have ra0 : (reg f2 a0 = 1 ∧ dE = len.toNat) ∨ reg f2 a0 = 0 := by
    have v : reg f2 a0 = (if (BitVec.ofNat 32 dE).ult len then (1 : Word) else 0) ^^^ 0x1 := by
      rw [w2.newReg (by decide)]; show reg f1 a0 ^^^ 0x1 = _
      rw [w1.newReg (by decide)]; show (if (reg nE (23 : Fin 32)).ult (reg nE (21 : Fin 32)) then _ else _) ^^^ _ = _
      rw [s7E, s5E]
    have hu : (BitVec.ofNat 32 dE).ult len = decide (dE < len.toNat) := by
      rw [← ult_lit hdE32 len.isLt, ofNat_toNat_self]
    rw [v, hu]
    by_cases hlt : dE < len.toNat
    · rw [decide_eq_true hlt]; exact .inr rfl
    · rw [decide_eq_false hlt]; exact .inl ⟨rfl, by omega⟩
  have kw2 := w2.oldReg w1.self.zero
  have kw1 := w1.oldReg uE.zero
  obtain ⟨f3, g3, w3⟩ := w2.self.aluImm hcE frd_at_ec (off' := 0xEE) (by decide)
  have kw3 := w3.oldReg w2.self.zero
  have a1_3 : reg f3 a1 = F + 0x100 := by
    rw [w3.newReg (by decide)]; show reg f2 sp + 0x100 = _; rw [kw2 _ (by decide), kw1 _ (by decide), spE]
  have rdOf : ∀ o, 0x110 ≤ o → o + 4 ≤ 0x140 →
      memLoad32 ME (F + BitVec.ofNat 32 o) = memLoad32 P11 (F + BitVec.ofNat 32 o) := fun o h1 h2 =>
    memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, show o + j = 0x110 + (o - 0x110 + j) by omega]; exact hslE _ (by omega)
  have a1_0' : reg f3 a1 = F + 0x100 := by
    exact a1_3
  obtain ⟨h0, dl0, l0⟩ := w3.self.lwE hcE frd_at_ee (off' := 0xF2) (by decide)
    (by rw [a1_0', BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m ra)
    (by rw [a1_0', BitVec.add_assoc]; exact (rdOf 0x13C (by decide) (by decide)).trans sv13C)
  have a1_1' : reg h0 a1 = F + 0x100 := by
    rw [l0.oldReg w3.self.zero _ (by decide), a1_0']
  obtain ⟨h1, dl1, l1⟩ := l0.self.lwE hcE frd_at_f2 (off' := 0xF4) (by decide)
    (by rw [a1_1', BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (8 : Fin 32))
    (by rw [a1_1', BitVec.add_assoc]; exact (rdOf 0x138 (by decide) (by decide)).trans sv138)
  have a1_2' : reg h1 a1 = F + 0x100 := by
    rw [l1.oldReg l0.self.zero _ (by decide), a1_1']
  obtain ⟨h2, dl2, l2⟩ := l1.self.lwE hcE frd_at_f4 (off' := 0xF6) (by decide)
    (by rw [a1_2', BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (9 : Fin 32))
    (by rw [a1_2', BitVec.add_assoc]; exact (rdOf 0x134 (by decide) (by decide)).trans sv134)
  have a1_3' : reg h2 a1 = F + 0x100 := by
    rw [l2.oldReg l1.self.zero _ (by decide), a1_2']
  obtain ⟨h3, dl3, l3⟩ := l2.self.lwE hcE frd_at_f6 (off' := 0xFA) (by decide)
    (by rw [a1_3', BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (18 : Fin 32))
    (by rw [a1_3', BitVec.add_assoc]; exact (rdOf 0x130 (by decide) (by decide)).trans sv130)
  have a1_4' : reg h3 a1 = F + 0x100 := by
    rw [l3.oldReg l2.self.zero _ (by decide), a1_3']
  obtain ⟨h4, dl4, l4⟩ := l3.self.lwE hcE frd_at_fa (off' := 0xFE) (by decide)
    (by rw [a1_4', BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (19 : Fin 32))
    (by rw [a1_4', BitVec.add_assoc]; exact (rdOf 0x12C (by decide) (by decide)).trans sv12C)
  have a1_5' : reg h4 a1 = F + 0x100 := by
    rw [l4.oldReg l3.self.zero _ (by decide), a1_4']
  obtain ⟨h5, dl5, l5⟩ := l4.self.lwE hcE frd_at_fe (off' := 0x102) (by decide)
    (by rw [a1_5', BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (20 : Fin 32))
    (by rw [a1_5', BitVec.add_assoc]; exact (rdOf 0x128 (by decide) (by decide)).trans sv128)
  have a1_6' : reg h5 a1 = F + 0x100 := by
    rw [l5.oldReg l4.self.zero _ (by decide), a1_5']
  obtain ⟨h6, dl6, l6⟩ := l5.self.lwE hcE frd_at_102 (off' := 0x106) (by decide)
    (by rw [a1_6', BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (21 : Fin 32))
    (by rw [a1_6', BitVec.add_assoc]; exact (rdOf 0x124 (by decide) (by decide)).trans sv124)
  have a1_7' : reg h6 a1 = F + 0x100 := by
    rw [l6.oldReg l5.self.zero _ (by decide), a1_6']
  obtain ⟨h7, dl7, l7⟩ := l6.self.lwE hcE frd_at_106 (off' := 0x10A) (by decide)
    (by rw [a1_7', BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (22 : Fin 32))
    (by rw [a1_7', BitVec.add_assoc]; exact (rdOf 0x120 (by decide) (by decide)).trans sv120)
  have a1_8' : reg h7 a1 = F + 0x100 := by
    rw [l7.oldReg l6.self.zero _ (by decide), a1_7']
  obtain ⟨h8, dl8, l8⟩ := l7.self.lwE hcE frd_at_10a (off' := 0x10E) (by decide)
    (by rw [a1_8', BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (23 : Fin 32))
    (by rw [a1_8', BitVec.add_assoc]; exact (rdOf 0x11C (by decide) (by decide)).trans sv11C)
  have a1_9' : reg h8 a1 = F + 0x100 := by
    rw [l8.oldReg l7.self.zero _ (by decide), a1_8']
  obtain ⟨h9, dl9, l9⟩ := l8.self.lwE hcE frd_at_10e (off' := 0x112) (by decide)
    (by rw [a1_9', BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (24 : Fin 32))
    (by rw [a1_9', BitVec.add_assoc]; exact (rdOf 0x118 (by decide) (by decide)).trans sv118)
  have a1_10' : reg h9 a1 = F + 0x100 := by
    rw [l9.oldReg l8.self.zero _ (by decide), a1_9']
  obtain ⟨h10, dl10, l10⟩ := l9.self.lwE hcE frd_at_112 (off' := 0x116) (by decide)
    (by rw [a1_10', BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (25 : Fin 32))
    (by rw [a1_10', BitVec.add_assoc]; exact (rdOf 0x114 (by decide) (by decide)).trans sv114)
  have a1_11' : reg h10 a1 = F + 0x100 := by
    rw [l10.oldReg l9.self.zero _ (by decide), a1_10']
  obtain ⟨h11, dl11, l11⟩ := l10.self.lwE hcE frd_at_116 (off' := 0x11A) (by decide)
    (by rw [a1_11', BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (26 : Fin 32))
    (by rw [a1_11', BitVec.add_assoc]; exact (rdOf 0x110 (by decide) (by decide)).trans sv110)
  obtain ⟨f4, g4, w4⟩ := l11.self.aluImm hcE frd_at_11a (off' := 0x11C) (by decide)
  obtain ⟨f5, g5, pc5, mem5, regs5⟩ := w4.self.jalr hcE frd_at_11c
  have fin0 : reg h11 ra = reg m ra := by rw [l11.oldReg l10.self.zero _ (by decide), l10.oldReg l9.self.zero _ (by decide), l9.oldReg l8.self.zero _ (by decide), l8.oldReg l7.self.zero _ (by decide), l7.oldReg l6.self.zero _ (by decide), l6.oldReg l5.self.zero _ (by decide), l5.oldReg l4.self.zero _ (by decide), l4.oldReg l3.self.zero _ (by decide), l3.oldReg l2.self.zero _ (by decide), l2.oldReg l1.self.zero _ (by decide), l1.oldReg l0.self.zero _ (by decide), l0.newReg (by decide)]
  have fin1 : reg h11 (8 : Fin 32) = reg m (8 : Fin 32) := by rw [l11.oldReg l10.self.zero _ (by decide), l10.oldReg l9.self.zero _ (by decide), l9.oldReg l8.self.zero _ (by decide), l8.oldReg l7.self.zero _ (by decide), l7.oldReg l6.self.zero _ (by decide), l6.oldReg l5.self.zero _ (by decide), l5.oldReg l4.self.zero _ (by decide), l4.oldReg l3.self.zero _ (by decide), l3.oldReg l2.self.zero _ (by decide), l2.oldReg l1.self.zero _ (by decide), l1.newReg (by decide)]
  have fin2 : reg h11 (9 : Fin 32) = reg m (9 : Fin 32) := by rw [l11.oldReg l10.self.zero _ (by decide), l10.oldReg l9.self.zero _ (by decide), l9.oldReg l8.self.zero _ (by decide), l8.oldReg l7.self.zero _ (by decide), l7.oldReg l6.self.zero _ (by decide), l6.oldReg l5.self.zero _ (by decide), l5.oldReg l4.self.zero _ (by decide), l4.oldReg l3.self.zero _ (by decide), l3.oldReg l2.self.zero _ (by decide), l2.newReg (by decide)]
  have fin3 : reg h11 (18 : Fin 32) = reg m (18 : Fin 32) := by rw [l11.oldReg l10.self.zero _ (by decide), l10.oldReg l9.self.zero _ (by decide), l9.oldReg l8.self.zero _ (by decide), l8.oldReg l7.self.zero _ (by decide), l7.oldReg l6.self.zero _ (by decide), l6.oldReg l5.self.zero _ (by decide), l5.oldReg l4.self.zero _ (by decide), l4.oldReg l3.self.zero _ (by decide), l3.newReg (by decide)]
  have fin4 : reg h11 (19 : Fin 32) = reg m (19 : Fin 32) := by rw [l11.oldReg l10.self.zero _ (by decide), l10.oldReg l9.self.zero _ (by decide), l9.oldReg l8.self.zero _ (by decide), l8.oldReg l7.self.zero _ (by decide), l7.oldReg l6.self.zero _ (by decide), l6.oldReg l5.self.zero _ (by decide), l5.oldReg l4.self.zero _ (by decide), l4.newReg (by decide)]
  have fin5 : reg h11 (20 : Fin 32) = reg m (20 : Fin 32) := by rw [l11.oldReg l10.self.zero _ (by decide), l10.oldReg l9.self.zero _ (by decide), l9.oldReg l8.self.zero _ (by decide), l8.oldReg l7.self.zero _ (by decide), l7.oldReg l6.self.zero _ (by decide), l6.oldReg l5.self.zero _ (by decide), l5.newReg (by decide)]
  have fin6 : reg h11 (21 : Fin 32) = reg m (21 : Fin 32) := by rw [l11.oldReg l10.self.zero _ (by decide), l10.oldReg l9.self.zero _ (by decide), l9.oldReg l8.self.zero _ (by decide), l8.oldReg l7.self.zero _ (by decide), l7.oldReg l6.self.zero _ (by decide), l6.newReg (by decide)]
  have fin7 : reg h11 (22 : Fin 32) = reg m (22 : Fin 32) := by rw [l11.oldReg l10.self.zero _ (by decide), l10.oldReg l9.self.zero _ (by decide), l9.oldReg l8.self.zero _ (by decide), l8.oldReg l7.self.zero _ (by decide), l7.newReg (by decide)]
  have fin8 : reg h11 (23 : Fin 32) = reg m (23 : Fin 32) := by rw [l11.oldReg l10.self.zero _ (by decide), l10.oldReg l9.self.zero _ (by decide), l9.oldReg l8.self.zero _ (by decide), l8.newReg (by decide)]
  have fin9 : reg h11 (24 : Fin 32) = reg m (24 : Fin 32) := by rw [l11.oldReg l10.self.zero _ (by decide), l10.oldReg l9.self.zero _ (by decide), l9.newReg (by decide)]
  have fin10 : reg h11 (25 : Fin 32) = reg m (25 : Fin 32) := by rw [l11.oldReg l10.self.zero _ (by decide), l10.newReg (by decide)]
  have fin11 : reg h11 (26 : Fin 32) = reg m (26 : Fin 32) := by rw [l11.newReg (by decide)]
  have sp_h : reg h11 sp = F := by rw [l11.oldReg l10.self.zero _ (by decide), l10.oldReg l9.self.zero _ (by decide), l9.oldReg l8.self.zero _ (by decide), l8.oldReg l7.self.zero _ (by decide), l7.oldReg l6.self.zero _ (by decide), l6.oldReg l5.self.zero _ (by decide), l5.oldReg l4.self.zero _ (by decide), l4.oldReg l3.self.zero _ (by decide), l3.oldReg l2.self.zero _ (by decide), l2.oldReg l1.self.zero _ (by decide), l1.oldReg l0.self.zero _ (by decide), l0.oldReg w3.self.zero _ (by decide), kw3 _ (by decide), kw2 _ (by decide), kw1 _ (by decide), spE]
  have a0_h : reg h11 a0 = reg f2 a0 := by
    rw [l11.oldReg l10.self.zero _ (by decide), l10.oldReg l9.self.zero _ (by decide), l9.oldReg l8.self.zero _ (by decide), l8.oldReg l7.self.zero _ (by decide), l7.oldReg l6.self.zero _ (by decide), l6.oldReg l5.self.zero _ (by decide), l5.oldReg l4.self.zero _ (by decide), l4.oldReg l3.self.zero _ (by decide), l3.oldReg l2.self.zero _ (by decide), l2.oldReg l1.self.zero _ (by decide), l1.oldReg l0.self.zero _ (by decide), l0.oldReg w3.self.zero _ (by decide), kw3 _ (by decide)]
  have pass : ∀ q : Fin 32, q = (3 : Fin 32) ∨ q = (4 : Fin 32) ∨ q = (27 : Fin 32) → reg h11 q = reg m q := by
    intro q hq
    have hk : romKeep q = true := by rcases hq with rfl | rfl | rfl <;> decide
    have n8 : q ≠ (8 : Fin 32) := by rcases hq with rfl | rfl | rfl <;> decide
    have n23 : q ≠ (23 : Fin 32) := by rcases hq with rfl | rfl | rfl <;> decide
    have n26 : q ≠ (26 : Fin 32) := by rcases hq with rfl | rfl | rfl <;> decide
    have nl : ∀ r : Fin 32, r.val ∈ [1, 2, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 25, 26] →
        q ≠ r := by
      intro r hr e; subst e; rcases hq with rfl | rfl | rfl <;> exact absurd hr (by decide)
    rw [l11.oldReg l10.self.zero _ (nl _ (by decide)), l10.oldReg l9.self.zero _ (nl _ (by decide)), l9.oldReg l8.self.zero _ (nl _ (by decide)), l8.oldReg l7.self.zero _ (nl _ (by decide)), l7.oldReg l6.self.zero _ (nl _ (by decide)), l6.oldReg l5.self.zero _ (nl _ (by decide)), l5.oldReg l4.self.zero _ (nl _ (by decide)), l4.oldReg l3.self.zero _ (nl _ (by decide)), l3.oldReg l2.self.zero _ (nl _ (by decide)), l2.oldReg l1.self.zero _ (nl _ (by decide)), l1.oldReg l0.self.zero _ (nl _ (by decide)), l0.oldReg w3.self.zero _ (nl _ (by decide)),
      kw3 _ (nl _ (by decide)), kw2 _ (nl _ (by decide)), kw1 _ (nl _ (by decide)), rkE q hk n8 n23 n26,
      k14 _ (nl _ (by decide)), k13 _ (nl _ (by decide)), k12 _ (nl _ (by decide)), k11 _ (nl _ (by decide)),
      K10 q (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)),
      r9 q (nl _ (by decide)), k8 _ (nl _ (by decide)), k7 _ (nl _ (by decide)), k6 _ (nl _ (by decide)),
      k5 _ (nl _ (by decide)), k4 _ (nl _ (by decide)), k3 _ (nl _ (by decide)), k2 _ (nl _ (by decide)),
      k1 _ (nl _ (by decide)), rk2 q (nl _ (by decide)) (nl _ (by decide))]
  have hmem : ∀ q : Fin 32, romKeep q = true → q = 0 ∨ q = sp ∨ q = (3 : Fin 32) ∨ q = (4 : Fin 32) ∨
      q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨
      q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨ q = (23 : Fin 32) ∨ q = (24 : Fin 32) ∨ q = (25 : Fin 32) ∨
      q = (26 : Fin 32) ∨ q = (27 : Fin 32) := by decide
  have spf : reg f5 sp = G + BitVec.ofNat 32 (0x150 + R) := by
    rw [regs5, w4.newReg (by decide)]; show reg h11 sp + 0x140 = _; rw [sp_h, hspF]
  have kf5 : ∀ q, q ≠ sp → reg f5 q = reg h11 q := fun q hq => by rw [regs5, w4.oldReg l11.self.zero q hq]

  refine ⟨f5, .cons d1 (.cons d2 (.cons dp0 (.cons dp1 (.cons dp2 (.cons dp3 (.cons dp4 (.cons dp5 (.cons dp6 (.cons dp7 (.cons dp8 (.cons dp9 (.cons dp10 (.cons dp11 (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (c9.trans (c10.trans (.cons e11 (.cons e12 (.cons e13 (.cons e14 (cE.trans (.cons g1 (.cons g2 (.cons g3 (.cons dl0 (.cons dl1 (.cons dl2 (.cons dl3 (.cons dl4 (.cons dl5 (.cons dl6 (.cons dl7 (.cons dl8 (.cons dl9 (.cons dl10 (.cons dl11 (.cons g4 (.single g5))))))))))))))))))))))))))))))))))))))))))))), ?_, spf, ?_, ?_, ?_, ?_⟩
  · rw [pc5, w4.oldReg l11.self.zero ra (by decide), add_lit_zero, fin0, hra, hret]
  · intro q hq
    rcases hmem q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [regs5, w4.self.zero, hz]
    · rw [spf, hsp]
    · rw [kf5 _ (by decide), pass _ (.inl rfl)]
    · rw [kf5 _ (by decide), pass _ (.inr (.inl rfl))]
    · rw [kf5 _ (by decide), fin1]
    · rw [kf5 _ (by decide), fin2]
    · rw [kf5 _ (by decide), fin3]
    · rw [kf5 _ (by decide), fin4]
    · rw [kf5 _ (by decide), fin5]
    · rw [kf5 _ (by decide), fin6]
    · rw [kf5 _ (by decide), fin7]
    · rw [kf5 _ (by decide), fin8]
    · rw [kf5 _ (by decide), fin9]
    · rw [kf5 _ (by decide), fin10]
    · rw [kf5 _ (by decide), fin11]
    · rw [kf5 _ (by decide), pass _ (.inr (.inr rfl))]
  · rw [kf5 _ (by decide), a0_h]; rcases ra0 with h | h
    · exact .inr h.1
    · exact .inl h
  · intro h1 i hi
    rw [kf5 _ (by decide), a0_h] at h1
    rcases ra0 with h | h
    · rw [mem5]; exact hcpE h.2 i hi
    · rw [h] at h1; exact absurd h1 (by decide)
  · intro x hx ho; rw [mem5]; exact hfrE x hx ho

end C3.RV32


