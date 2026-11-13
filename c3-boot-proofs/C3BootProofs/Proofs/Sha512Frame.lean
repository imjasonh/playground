import C3BootProofs.Proofs.Sha512Load

/-!
# `compress512`: the frame blocks

The straight-line blocks that move the hash state between `stp`, the frame,
and the registers: the prologue and the setup after it (0x0..0x82), the
outer loop's top (0x82..0x94), the calls' arguments, the round setup
(0x1F0..0x22C), the feed-forward after the rounds (0x376..0x43C), and the
epilogue (0x43E..0x476).
-/

namespace C3.RV32

open C3.Image

/-- The prologue, from 0x0 to 0x38: the frame and the register saves. -/
def s5Pro : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFC70, .aluImm .add a3 sp 0x380, .sw a3 ra 0xC, .sw a3 (8 : Fin 32) 0x8,
   .sw a3 (9 : Fin 32) 0x4, .sw a3 (18 : Fin 32) 0x0, .aluImm .add a3 sp 0x300, .sw a3 (19 : Fin 32) 0x7C,
   .sw a3 (20 : Fin 32) 0x78, .sw a3 (21 : Fin 32) 0x74, .sw a3 (22 : Fin 32) 0x70,
   .sw a3 (23 : Fin 32) 0x6C, .sw a3 (24 : Fin 32) 0x68, .sw a3 (25 : Fin 32) 0x64,
   .sw a3 (26 : Fin 32) 0x60, .sw a3 (27 : Fin 32) 0x5C]

/-- From 0x38 to 0x82: the state into registers and the frame, and the end of
the blocks at `F + 0x10`. -/
def s5Setup : List BInstr :=
  [.alu .add (21 : Fin 32) x0 a1, .aluImm .sll a2 a2 0x7, .lw (23 : Fin 32) a0 0x0, .lw (19 : Fin 32) a0 0x4,
   .lw (22 : Fin 32) a0 0x8, .lw (27 : Fin 32) a0 0xC, .lw (24 : Fin 32) a0 0x10, .lw (26 : Fin 32) a0 0x14,
   .lw (18 : Fin 32) a0 0x18, .lw a1 a0 0x1C, .sw sp a1 0x54, .lw (20 : Fin 32) a0 0x20, .lw a1 a0 0x24,
   .sw sp a1 0x4C, .lw a1 a0 0x28, .sw sp a1 0x50, .lw a1 a0 0x2C, .sw sp a1 0x44, .lw a1 a0 0x30,
   .sw sp a1 0x48, .lw a1 a0 0x34, .sw sp a1 0x3C, .lw a1 a0 0x38, .sw sp a1 0x40, .sw sp a0 0xC,
   .lw a0 a0 0x3C, .sw sp a0 0x38, .alu .add a2 a2 (21 : Fin 32), .sw sp a2 0x10]

/-- The outer loop's top, from 0x82 to 0x88: the buffer's address and the end
of the blocks. -/
def s5Top : List BInstr :=
  [.aluImm .add (25 : Fin 32) sp 0x58, .lw a0 sp 0x10]

/-- From 0x8C to 0x94: the load loop's counter, and the next block's address
at `F + 0x34`. -/
def s5Blk : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x0, .aluImm .add a0 (21 : Fin 32) 0x80, .sw sp a0 0x34]

/-- `memcpy`'s arguments, from 0xF8 to 0x100. -/
def s5Cpy : List BInstr :=
  [.aluImm .add a0 sp 0xD8, .aluImm .add a1 sp 0x58, .aluImm .add a2 x0 0x80]

/-- `memset`'s arguments, from 0x108 to 0x112. -/
def s5Zero : List BInstr :=
  [.aluImm .add a2 x0 0x200, .aluImm .add (8 : Fin 32) sp 0x158, .alu .add a0 x0 (8 : Fin 32),
   .aluImm .add a1 x0 0x0]

/-- The round setup, from 0x1F0 to 0x22C: the state's halves out of the
registers and the frame into the working variables' registers, and the
constants' and the schedule's addresses. -/
def s5Pre : List BInstr :=
  [.aluImm .add (30 : Fin 32) sp 0xD8, .aluImm .add (29 : Fin 32) x0 0x50, .lui (25 : Fin 32) 0x3FCC5000,
   .aluImm .add (25 : Fin 32) (25 : Fin 32) 0xFFFFFFC0, .sw sp (20 : Fin 32) 0x14,
   .alu .add a2 x0 (20 : Fin 32), .lw a3 sp 0x4C, .sw sp (23 : Fin 32) 0x30, .sw sp (19 : Fin 32) 0x1C,
   .alu .add a0 x0 (19 : Fin 32), .lw ra sp 0x40, .lw a6 sp 0x38, .lw (17 : Fin 32) sp 0x48,
   .lw (21 : Fin 32) sp 0x3C, .lw (6 : Fin 32) sp 0x50, .lw (5 : Fin 32) sp 0x44, .sw sp (18 : Fin 32) 0x24,
   .alu .add (19 : Fin 32) x0 (18 : Fin 32), .lw (20 : Fin 32) sp 0x54, .sw sp (24 : Fin 32) 0x28,
   .alu .add (18 : Fin 32) x0 (24 : Fin 32), .sw sp (26 : Fin 32) 0x20, .sw sp (22 : Fin 32) 0x2C,
   .alu .add (28 : Fin 32) x0 (22 : Fin 32), .sw sp (27 : Fin 32) 0x18,
   .alu .add (7 : Fin 32) x0 (27 : Fin 32)]

/-- The feed-forward, from 0x376 to 0x43C: the working variables plus the
state, into the state at `stp` and the frame, and the next block's address. -/
def s5Final : List BInstr :=
  [.lw a0 sp 0x1C, .alu .add (24 : Fin 32) (24 : Fin 32) a0, .lw a0 sp 0x18,
   .alu .add (7 : Fin 32) (7 : Fin 32) a0, .lw (23 : Fin 32) sp 0x30,
   .alu .add (23 : Fin 32) (23 : Fin 32) (31 : Fin 32), .alu .sltu a0 (23 : Fin 32) (31 : Fin 32),
   .lw a1 sp 0x2C, .alu .add a1 a1 (28 : Fin 32), .alu .add a2 (24 : Fin 32) a0,
   .alu .sltu a0 a1 (28 : Fin 32), .alu .add (7 : Fin 32) (7 : Fin 32) a0, .lw (24 : Fin 32) sp 0x28,
   .alu .add (24 : Fin 32) (24 : Fin 32) (18 : Fin 32), .lw a0 sp 0x20,
   .alu .add (26 : Fin 32) (26 : Fin 32) a0, .alu .sltu a0 (24 : Fin 32) (18 : Fin 32),
   .alu .add (26 : Fin 32) (26 : Fin 32) a0, .lw (18 : Fin 32) sp 0x24,
   .alu .add (18 : Fin 32) (18 : Fin 32) (19 : Fin 32), .lw a0 sp 0x54,
   .alu .add (20 : Fin 32) (20 : Fin 32) a0, .alu .sltu a0 (18 : Fin 32) (19 : Fin 32),
   .alu .add (19 : Fin 32) x0 a2, .alu .add a2 (20 : Fin 32) a0, .lw (20 : Fin 32) sp 0x14,
   .alu .add (20 : Fin 32) (20 : Fin 32) (27 : Fin 32), .lw a0 sp 0x4C,
   .alu .add (22 : Fin 32) (22 : Fin 32) a0, .alu .sltu a0 (20 : Fin 32) (27 : Fin 32),
   .alu .add (27 : Fin 32) x0 (7 : Fin 32), .alu .add a3 (22 : Fin 32) a0, .alu .add (22 : Fin 32) x0 a1,
   .lw a1 sp 0x50, .alu .add a1 a1 (6 : Fin 32), .lw a0 sp 0x44, .alu .add (5 : Fin 32) (5 : Fin 32) a0,
   .alu .sltu a0 a1 (6 : Fin 32), .alu .add (5 : Fin 32) (5 : Fin 32) a0, .lw a4 sp 0x48,
   .alu .add a4 a4 (17 : Fin 32), .lw a0 sp 0x3C, .alu .add (21 : Fin 32) (21 : Fin 32) a0,
   .alu .sltu a0 a4 (17 : Fin 32), .alu .add (21 : Fin 32) (21 : Fin 32) a0, .lw a5 sp 0x40,
   .alu .add a5 a5 ra, .lw a0 sp 0x38, .alu .add a6 a6 a0, .alu .sltu a0 a5 ra, .alu .add a6 a6 a0,
   .lw a0 sp 0xC, .sw a0 (23 : Fin 32) 0x0, .sw a0 (19 : Fin 32) 0x4, .sw a0 (22 : Fin 32) 0x8,
   .sw a0 (7 : Fin 32) 0xC, .sw a0 (24 : Fin 32) 0x10, .sw a0 (26 : Fin 32) 0x14, .sw a0 (18 : Fin 32) 0x18,
   .sw sp a2 0x54, .sw a0 a2 0x1C, .sw a0 (20 : Fin 32) 0x20, .sw sp a3 0x4C, .sw a0 a3 0x24, .sw sp a1 0x50,
   .sw a0 a1 0x28, .sw sp (5 : Fin 32) 0x44, .sw a0 (5 : Fin 32) 0x2C, .sw sp a4 0x48, .sw a0 a4 0x30,
   .sw sp (21 : Fin 32) 0x3C, .sw a0 (21 : Fin 32) 0x34, .sw sp a5 0x40, .sw a0 a5 0x38, .sw sp a6 0x38,
   .sw a0 a6 0x3C, .lw (21 : Fin 32) sp 0x34]

/-- The epilogue, from 0x43E to 0x476: the register restores and the frame's
release. -/
def s5Epi : List BInstr :=
  [.aluImm .add a0 sp 0x380, .lw ra a0 0xC, .lw (8 : Fin 32) a0 0x8, .lw (9 : Fin 32) a0 0x4,
   .lw (18 : Fin 32) a0 0x0, .aluImm .add a0 sp 0x300, .lw (19 : Fin 32) a0 0x7C, .lw (20 : Fin 32) a0 0x78,
   .lw (21 : Fin 32) a0 0x74, .lw (22 : Fin 32) a0 0x70, .lw (23 : Fin 32) a0 0x6C,
   .lw (24 : Fin 32) a0 0x68, .lw (25 : Fin 32) a0 0x64, .lw (26 : Fin 32) a0 0x60,
   .lw (27 : Fin 32) a0 0x5C, .aluImm .add sp sp 0x390]

section
set_option maxRecDepth 100000
theorem s5Pro_end : blockEnd sha512CompressCode 0x0 s5Pro = some 0x38 := by decide
theorem s5Setup_end : blockEnd sha512CompressCode 0x38 s5Setup = some 0x82 := by decide
theorem s5Top_end : blockEnd sha512CompressCode 0x82 s5Top = some 0x88 := by decide
theorem s5Blk_end : blockEnd sha512CompressCode 0x8C s5Blk = some 0x94 := by decide
theorem s5Cpy_end : blockEnd sha512CompressCode 0xF8 s5Cpy = some 0x100 := by decide
theorem s5Zero_end : blockEnd sha512CompressCode 0x108 s5Zero = some 0x112 := by decide
theorem s5Pre_end : blockEnd sha512CompressCode 0x1F0 s5Pre = some 0x22C := by decide
theorem s5Final_end : blockEnd sha512CompressCode 0x376 s5Final = some 0x43C := by decide
theorem s5Epi_end : blockEnd sha512CompressCode 0x43E s5Epi = some 0x476 := by decide
end

/-- Memory after the round setup stores the state's halves that leave the
registers into the frame at `F`. -/
def s5PreMem (M : Word → BitVec 8) (F : Word) (f : Fin 32 → Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M
    (F + 0x14) (f 20)) (F + 0x30) (f 23)) (F + 0x1C) (f 19)) (F + 0x24) (f 18)) (F + 0x28) (f 24))
    (F + 0x20) (f 26)) (F + 0x2C) (f 22)) (F + 0x18) (f 27)

def s5PreKeep (q : Fin 32) : Bool :=
  q.val ∉ [0, 1, 5, 6, 7, 10, 12, 13, 16, 17, 18, 19, 20, 21, 25, 28, 29, 30]

theorem s5K_lit : (0x3FCC5000 : Word) + 0xFFFFFFC0 = s5K := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem s5Pre_run {M : Word → BitVec 8} {f : Fin 32 → Word} {F : Word} (hz : f 0 = 0) (hsp : f sp = F) :
    (runBlock s5Pre (M, f)).1 = s5PreMem M F f ∧
    (runBlock s5Pre (M, f)).2 30 = F + 0xD8 ∧ (runBlock s5Pre (M, f)).2 29 = 0x50 ∧
    (runBlock s5Pre (M, f)).2 25 = s5K ∧
    (runBlock s5Pre (M, f)).2 a2 = f 20 ∧ (runBlock s5Pre (M, f)).2 a3 = memLoad32 M (F + 0x4C) ∧
    (runBlock s5Pre (M, f)).2 a0 = f 19 ∧
    (runBlock s5Pre (M, f)).2 ra = memLoad32 M (F + 0x40) ∧ (runBlock s5Pre (M, f)).2 a6 = memLoad32 M (F + 0x38) ∧
    (runBlock s5Pre (M, f)).2 17 = memLoad32 M (F + 0x48) ∧ (runBlock s5Pre (M, f)).2 21 = memLoad32 M (F + 0x3C) ∧
    (runBlock s5Pre (M, f)).2 6 = memLoad32 M (F + 0x50) ∧ (runBlock s5Pre (M, f)).2 5 = memLoad32 M (F + 0x44) ∧
    (runBlock s5Pre (M, f)).2 19 = f 18 ∧ (runBlock s5Pre (M, f)).2 20 = memLoad32 M (F + 0x54) ∧
    (runBlock s5Pre (M, f)).2 18 = f 24 ∧ (runBlock s5Pre (M, f)).2 28 = f 22 ∧
    (runBlock s5Pre (M, f)).2 7 = f 27 ∧
    ∀ q, s5PreKeep q = true → (runBlock s5Pre (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, s5Pre, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 18
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact absurd hq (by decide)
    · simp only [h0, ite_false, pkeep_ne (r := 1) hq rfl, pkeep_ne (r := 5) hq rfl, pkeep_ne (r := 6) hq rfl,
        pkeep_ne (r := 7) hq rfl, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a3) hq rfl,
        pkeep_ne (r := a6) hq rfl, pkeep_ne (r := 17) hq rfl, pkeep_ne (r := 18) hq rfl, pkeep_ne (r := 19) hq rfl,
        pkeep_ne (r := 20) hq rfl, pkeep_ne (r := 21) hq rfl, pkeep_ne (r := 25) hq rfl, pkeep_ne (r := 28) hq rfl,
        pkeep_ne (r := 29) hq rfl, pkeep_ne (r := 30) hq rfl]
  all_goals simp only [hsp, ev_add, zero_lit_add]
  all_goals try simp (disch := decide) only [ls_lit]
  all_goals try rfl

/-- Memory after the feed-forward stores the new state's halves into the
state at `stp`, and the halves the frame keeps into the frame at `F`. -/
def s5FinalMem (M : Word → BitVec 8) (F stp Al Ah Bl Bh Cl Ch Dl Dh El Eh Fl Fh Gl Gh Hl Hh : Word) :
    Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32
  (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32
  (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M
    (stp + 0x0) Al) (stp + 0x4) Ah) (stp + 0x8) Bl) (stp + 0xC) Bh) (stp + 0x10) Cl) (stp + 0x14) Ch)
    (stp + 0x18) Dl) (F + 0x54) Dh) (stp + 0x1C) Dh) (stp + 0x20) El) (F + 0x4C) Eh) (stp + 0x24) Eh)
    (F + 0x50) Fl) (stp + 0x28) Fl) (F + 0x44) Fh) (stp + 0x2C) Fh) (F + 0x48) Gl) (stp + 0x30) Gl)
    (F + 0x3C) Gh) (stp + 0x34) Gh) (F + 0x40) Hl) (stp + 0x38) Hl) (F + 0x38) Hh) (stp + 0x3C) Hh

def s5FinalKeep (q : Fin 32) : Bool :=
  q.val ∉ [0, 5, 7, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 26, 27]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem s5Final_run {M : Word → BitVec 8} {f : Fin 32 → Word} {F stp : Word} (hsp : f sp = F)
    (hst : memLoad32 M (F + 0xC) = stp) (hS : Sep stp 128 F 0x390) :
    (runBlock s5Final (M, f)).1 = s5FinalMem M F stp
      (memLoad32 M (F + 0x30) + f 31)
      (f 24 + memLoad32 M (F + 0x1C) + aluEval .sltu (memLoad32 M (F + 0x30) + f 31) (f 31))
      (memLoad32 M (F + 0x2C) + f 28)
      (f 7 + memLoad32 M (F + 0x18) + aluEval .sltu (memLoad32 M (F + 0x2C) + f 28) (f 28))
      (memLoad32 M (F + 0x28) + f 18)
      (f 26 + memLoad32 M (F + 0x20) + aluEval .sltu (memLoad32 M (F + 0x28) + f 18) (f 18))
      (memLoad32 M (F + 0x24) + f 19)
      (f 20 + memLoad32 M (F + 0x54) + aluEval .sltu (memLoad32 M (F + 0x24) + f 19) (f 19))
      (memLoad32 M (F + 0x14) + f 27)
      (f 22 + memLoad32 M (F + 0x4C) + aluEval .sltu (memLoad32 M (F + 0x14) + f 27) (f 27))
      (memLoad32 M (F + 0x50) + f 6)
      (f 5 + memLoad32 M (F + 0x44) + aluEval .sltu (memLoad32 M (F + 0x50) + f 6) (f 6))
      (memLoad32 M (F + 0x48) + f 17)
      (f 21 + memLoad32 M (F + 0x3C) + aluEval .sltu (memLoad32 M (F + 0x48) + f 17) (f 17))
      (memLoad32 M (F + 0x40) + f ra)
      (f a6 + memLoad32 M (F + 0x38) + aluEval .sltu (memLoad32 M (F + 0x40) + f ra) (f ra)) ∧
    (runBlock s5Final (M, f)).2 23 = memLoad32 M (F + 0x30) + f 31 ∧
    (runBlock s5Final (M, f)).2 19 =
      f 24 + memLoad32 M (F + 0x1C) + aluEval .sltu (memLoad32 M (F + 0x30) + f 31) (f 31) ∧
    (runBlock s5Final (M, f)).2 22 = memLoad32 M (F + 0x2C) + f 28 ∧
    (runBlock s5Final (M, f)).2 27 =
      f 7 + memLoad32 M (F + 0x18) + aluEval .sltu (memLoad32 M (F + 0x2C) + f 28) (f 28) ∧
    (runBlock s5Final (M, f)).2 24 = memLoad32 M (F + 0x28) + f 18 ∧
    (runBlock s5Final (M, f)).2 26 =
      f 26 + memLoad32 M (F + 0x20) + aluEval .sltu (memLoad32 M (F + 0x28) + f 18) (f 18) ∧
    (runBlock s5Final (M, f)).2 18 = memLoad32 M (F + 0x24) + f 19 ∧
    (runBlock s5Final (M, f)).2 20 = memLoad32 M (F + 0x14) + f 27 ∧
    (runBlock s5Final (M, f)).2 21 = memLoad32 M (F + 0x34) ∧
    ∀ q, s5FinalKeep q = true → (runBlock s5Final (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, s5Final, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 10
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact absurd hq (by decide)
    · simp only [h0, ite_false, pkeep_ne (r := 5) hq rfl, pkeep_ne (r := 7) hq rfl, pkeep_ne (r := a0) hq rfl,
        pkeep_ne (r := a1) hq rfl, pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a3) hq rfl, pkeep_ne (r := a4) hq rfl,
        pkeep_ne (r := a5) hq rfl, pkeep_ne (r := a6) hq rfl, pkeep_ne (r := 18) hq rfl, pkeep_ne (r := 19) hq rfl,
        pkeep_ne (r := 20) hq rfl, pkeep_ne (r := 21) hq rfl, pkeep_ne (r := 22) hq rfl, pkeep_ne (r := 23) hq rfl,
        pkeep_ne (r := 24) hq rfl, pkeep_ne (r := 26) hq rfl, pkeep_ne (r := 27) hq rfl]
  all_goals simp only [hsp, ev_add, zero_lit_add]
  all_goals try simp (disch := decide) only [ls_lit]
  all_goals try rw [hst]
  all_goals try simp (disch := decide) only [ls_lit, ls_sep hS]
  all_goals try rfl

/-- Memory after the setup stores the state's halves that live in the frame,
`stp`, and the end of the blocks `e` into the frame at `F`. -/
def s5SetupMem (M : Word → BitVec 8) (F stp e : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32
  (memStore32 M (F + 0x54) (memLoad32 M (stp + 0x1C))) (F + 0x4C) (memLoad32 M (stp + 0x24)))
    (F + 0x50) (memLoad32 M (stp + 0x28))) (F + 0x44) (memLoad32 M (stp + 0x2C)))
    (F + 0x48) (memLoad32 M (stp + 0x30))) (F + 0x3C) (memLoad32 M (stp + 0x34)))
    (F + 0x40) (memLoad32 M (stp + 0x38))) (F + 0xC) stp) (F + 0x38) (memLoad32 M (stp + 0x3C))) (F + 0x10) e

def s5SetupKeep (q : Fin 32) : Bool := q.val ∉ [0, 10, 11, 12, 18, 19, 20, 21, 22, 23, 24, 26, 27]

theorem ev_sll7 (x : Word) : aluEval .sll x 0x7 = x <<< 7 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem s5Setup_run {M : Word → BitVec 8} {f : Fin 32 → Word} {F stp : Word} (hz : f 0 = 0) (hsp : f sp = F)
    (ha0 : f a0 = stp) (hS : Sep F 0x390 stp 128) :
    (runBlock s5Setup (M, f)).1 = s5SetupMem M F stp ((f a2 <<< 7) + f a1) ∧
    (runBlock s5Setup (M, f)).2 21 = f a1 ∧
    (runBlock s5Setup (M, f)).2 23 = memLoad32 M (stp + 0x0) ∧
    (runBlock s5Setup (M, f)).2 19 = memLoad32 M (stp + 0x4) ∧
    (runBlock s5Setup (M, f)).2 22 = memLoad32 M (stp + 0x8) ∧
    (runBlock s5Setup (M, f)).2 27 = memLoad32 M (stp + 0xC) ∧
    (runBlock s5Setup (M, f)).2 24 = memLoad32 M (stp + 0x10) ∧
    (runBlock s5Setup (M, f)).2 26 = memLoad32 M (stp + 0x14) ∧
    (runBlock s5Setup (M, f)).2 18 = memLoad32 M (stp + 0x18) ∧
    (runBlock s5Setup (M, f)).2 20 = memLoad32 M (stp + 0x20) ∧
    ∀ q, s5SetupKeep q = true → (runBlock s5Setup (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, s5Setup, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 10
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact absurd hq (by decide)
    · simp only [h0, ite_false, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl, pkeep_ne (r := a2) hq rfl,
        pkeep_ne (r := 18) hq rfl, pkeep_ne (r := 19) hq rfl, pkeep_ne (r := 20) hq rfl, pkeep_ne (r := 21) hq rfl,
        pkeep_ne (r := 22) hq rfl, pkeep_ne (r := 23) hq rfl, pkeep_ne (r := 24) hq rfl, pkeep_ne (r := 26) hq rfl,
        pkeep_ne (r := 27) hq rfl]
  all_goals simp only [hsp, ha0, hz, ev_add, ev_sll7, zero_lit_add]
  all_goals try simp (disch := decide) only [ls_sep hS]
  all_goals try rfl

/-- The registers the prologue saves, with their offsets from the frame. -/
def s5Ps : List (Fin 32 × Word) :=
  [(ra, 0x38C), (8, 0x388), (9, 0x384), (18, 0x380), (19, 0x37C), (20, 0x378), (21, 0x374), (22, 0x370),
   (23, 0x36C), (24, 0x368), (25, 0x364), (26, 0x360), (27, 0x35C)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem s5Pro_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock s5Pro (M, f)).1 = saveMem M (f sp + 0xFFFFFC70) f s5Ps ∧
    (runBlock s5Pro (M, f)).2 sp = f sp + 0xFFFFFC70 ∧
    ∀ q, q ≠ sp → q ≠ a3 → (runBlock s5Pro (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, s5Pro, upd_app, ↓reduceIte, saveMem, s5Ps]
  refine ⟨?_, rfl, fun q h1 h2 => ?_⟩
  · simp only [ev_add, BitVec.add_assoc, BitVec.reduceAdd]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [hz]; rfl
    · simp only [h0, h1, h2, ite_false]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem s5Epi_run {M : Word → BitVec 8} {f : Fin 32 → Word} {F : Word} (hsp : f sp = F) :
    (runBlock s5Epi (M, f)).1 = M ∧
    (runBlock s5Epi (M, f)).2 sp = F + 0x390 ∧
    (∀ r o, (r, o) ∈ s5Ps → (runBlock s5Epi (M, f)).2 r = memLoad32 M (F + o)) ∧
    ∀ q, q.val ∉ [0, 1, 2, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → (runBlock s5Epi (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, s5Epi, upd_app, ↓reduceIte]
  refine ⟨trivial, by rw [hsp]; rfl, fun r o h => ?_, fun q hq => ?_⟩
  · simp only [s5Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [hsp, ev_add, BitVec.add_assoc, BitVec.reduceAdd]
      rfl
  · have h0 : q.val ≠ 0 := fun e => hq (by simp [e])
    have k : ∀ r : Fin 32, r.val ∈ [0, 1, 2, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ r :=
      fun r hr e => hq (e ▸ hr)
    simp only [h0, k ra (by decide), k sp (by decide), k 8 (by decide), k 9 (by decide), k a0 (by decide),
      k 18 (by decide), k 19 (by decide), k 20 (by decide), k 21 (by decide), k 22 (by decide), k 23 (by decide),
      k 24 (by decide), k 25 (by decide), k 26 (by decide), k 27 (by decide), ite_false]

set_option maxRecDepth 100000 in
theorem s5Pre_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {F base : Word} {len : Nat} (hsp : f sp = F)
    (hF : F.toNat % 4 = 0) (hs : Sep F 0x390 base len) : BlockOk base len s5Pre (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, s5Pre, upd_app, ↓reduceIte, and_true, true_and]
  simp only [hsp]
  simp (disch := decide) only [fr_al hF, frm_sep hs, and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem s5Final_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {F stp base : Word} {len : Nat} (hsp : f sp = F)
    (hst : memLoad32 M (F + 0xC) = stp) (hF : F.toNat % 4 = 0) (hstp : stp.toNat % 4 = 0)
    (hs : Sep F 0x390 base len) (hs' : Sep stp 128 base len) : BlockOk base len s5Final (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, s5Final, upd_app, ↓reduceIte, and_true, true_and]
  simp only [hsp, ev_add, zero_lit_add, hst]
  simp (disch := decide) only [fr_al hF, fr_al hstp, frm_sep hs, frm_sep hs', and_self]

set_option maxRecDepth 100000 in
theorem s5Setup_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {F stp base : Word} {len : Nat} (hsp : f sp = F)
    (ha0 : f a0 = stp) (hF : F.toNat % 4 = 0) (hstp : stp.toNat % 4 = 0) (hs : Sep F 0x390 base len) :
    BlockOk base len s5Setup (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, s5Setup, upd_app, ↓reduceIte, and_true, true_and]
  simp only [hsp, ha0, ev_add, zero_lit_add]
  simp (disch := decide) only [fr_al hF, fr_al hstp, frm_sep hs, and_self]

set_option maxRecDepth 100000 in
theorem s5Pro_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {F base : Word} {len : Nat}
    (hsp : f sp + 0xFFFFFC70 = F) (hF : F.toNat % 4 = 0) (hs : Sep F 0x390 base len) :
    BlockOk base len s5Pro (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, s5Pro, upd_app, ↓reduceIte, and_true, true_and]
  simp only [ev_add, hsp, BitVec.add_assoc, BitVec.reduceAdd]
  simp (disch := decide) only [fr_al hF, frm_sep hs, and_self]

set_option maxRecDepth 100000 in
theorem s5Epi_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {F base : Word} {len : Nat} (hsp : f sp = F)
    (hF : F.toNat % 4 = 0) : BlockOk base len s5Epi (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, s5Epi, upd_app, ↓reduceIte, and_true, true_and]
  simp only [ev_add, hsp, BitVec.add_assoc, BitVec.reduceAdd]
  simp (disch := decide) only [fr_al hF, and_self]

end C3.RV32
