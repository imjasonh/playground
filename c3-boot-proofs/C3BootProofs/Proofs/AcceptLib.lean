import C3BootProofs.Proofs.AcceptSlot
import C3BootProofs.Proofs.P2vLib
import C3BootProofs.Proofs.RomCalls
import C3BootProofs.Proofs.CondNeg12
import C3BootProofs.Image.BootloaderData9

/-!
# `boot_main`'s first closure: the frame, the prologue, and the exits

With the stack's base at `B`, the closure is called with `sp = B + 0x5A70`
and opens its frame at `B + 0x3A50`. The callees' frames go below it, down
to `B`, so `Fr B 0x5A70` describes the whole stack. The prologue saves `ra`
and `s0..s11` at `B + 0x5A3C` to `B + 0x5A70`. The epilogue at 0x184
restores them and returns. A slot that can't be booted reaches 0x16A, which
logs through the ROM's `printf`, writes `None` (0xFF at `result + 0xC`), and
returns.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- The prologue's saves, in order, at the top of the frame. -/
def acSaves (M : Word → BitVec 8) (B : Word) (n : Machine) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32
    (memStore32 (memStore32 (memStore32 (memStore32 M
    (B + BitVec.ofNat 32 0x5A6C) (reg n ra)) (B + BitVec.ofNat 32 0x5A68) (reg n (8 : Fin 32)))
    (B + BitVec.ofNat 32 0x5A64) (reg n (9 : Fin 32))) (B + BitVec.ofNat 32 0x5A60) (reg n (18 : Fin 32)))
    (B + BitVec.ofNat 32 0x5A5C) (reg n (19 : Fin 32))) (B + BitVec.ofNat 32 0x5A58) (reg n (20 : Fin 32)))
    (B + BitVec.ofNat 32 0x5A54) (reg n (21 : Fin 32))) (B + BitVec.ofNat 32 0x5A50) (reg n (22 : Fin 32)))
    (B + BitVec.ofNat 32 0x5A4C) (reg n (23 : Fin 32))) (B + BitVec.ofNat 32 0x5A48) (reg n (24 : Fin 32)))
    (B + BitVec.ofNat 32 0x5A44) (reg n (25 : Fin 32))) (B + BitVec.ofNat 32 0x5A40) (reg n (26 : Fin 32)))
    (B + BitVec.ofNat 32 0x5A3C) (reg n (27 : Fin 32))

theorem acSaves_read {M : Word → BitVec 8} {B : Word} {n : Machine} :
    ∀ k, k < 13 → memLoad32 (acSaves M B n) (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = reg n (savedReg k) := by
  intro k hk
  match k, hk with
  | 0, _ => unfold acSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 1, _ => unfold acSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 2, _ => unfold acSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 3, _ => unfold acSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 4, _ => unfold acSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 5, _ => unfold acSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 6, _ => unfold acSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 7, _ => unfold acSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 8, _ => unfold acSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 9, _ => unfold acSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 10, _ => unfold acSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 11, _ => unfold acSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 12, _ => unfold acSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl

theorem acSaves_out {M : Word → BitVec 8} {B : Word} {n : Machine} {x : Word}
    (h : Sep (B + BitVec.ofNat 32 0x5A3C) 0x34 x 1) : acSaves M B n x = M x := by
  have hs : ∀ c, 0x5A3C ≤ c → c + 4 ≤ 0x5A70 → Sep (B + BitVec.ofNat 32 c) 4 x 1 := fun c h1 h2 => by
    have := h.sub (c := c - 0x5A3C) (l := 4) (by omega)
    rwa [add_ofNat_assoc, show 0x5A3C + (c - 0x5A3C) = c by omega] at this
  unfold acSaves
  simp (disch := first | decide | exact hs _ (by decide) (by decide)) only [memStore32_get_sep]

/-- From the entry to the slot check at 0x32. -/
def acA1 : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFF00, .sw sp ra 0xFC, .sw sp (8 : Fin 32) 0xF8, .sw sp (9 : Fin 32) 0xF4,
   .sw sp (18 : Fin 32) 0xF0, .sw sp (19 : Fin 32) 0xEC, .sw sp (20 : Fin 32) 0xE8, .sw sp (21 : Fin 32) 0xE4,
   .sw sp (22 : Fin 32) 0xE0, .sw sp (23 : Fin 32) 0xDC, .sw sp (24 : Fin 32) 0xD8, .sw sp (25 : Fin 32) 0xD4,
   .sw sp (26 : Fin 32) 0xD0, .sw sp (27 : Fin 32) 0xCC, .lui a4 0x2000, .aluImm .add a4 a4 0xFFFFFF20,
   .alu .sub sp sp a4, .alu .add (8 : Fin 32) x0 a3, .alu .add (21 : Fin 32) x0 a2,
   .alu .add (26 : Fin 32) x0 a1, .alu .add (19 : Fin 32) x0 a0, .lui (24 : Fin 32) 0x210000]

set_option maxRecDepth 100000 in
theorem acA1_end : blockEnd bootMainClosure0Code 0 acA1 = some 0x32 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The prologue**, from the entry to 0x32: save `ra` and `s0..s11`, open
the frame at `B + 0x3A50`, keep the result in `s3`, `efuse_level` in `s10`,
the buffers in `s5`, and the slot in `s0`, and set `s8` to slot B's base. -/
theorem ac_pro {M : Word → BitVec 8} {n : Machine} {B : Word} (C : CodeIn M AC bootMainClosure0Code)
    (F : Fr B 0x5A70) (s : St M AC n 0 (reg n)) (rsp : reg n sp = B + 0x5A70) :
    ∃ n', Steps n n' ∧ St (acSaves M B n) AC n' 0x32 (reg n') ∧
      reg n' sp = B + 0x3A50 ∧ reg n' (19 : Fin 32) = reg n a0 ∧ reg n' (26 : Fin 32) = reg n a1 ∧
      reg n' (21 : Fin 32) = reg n a2 ∧ reg n' (8 : Fin 32) = reg n a3 ∧ reg n' (24 : Fin 32) = 0x210000 ∧
      reg n' a3 = reg n a3 ∧ ∀ q, q.val ∈ [3, 4] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hA : aluEval .add (B + 0x5A70) 0xFFFFFF00 = B + BitVec.ofNat 32 0x5970 := by
    show B + 0x5A70 + 0xFFFFFF00 = B + BitVec.ofNat 32 0x5970
    rw [BitVec.add_assoc]; rfl
  have alB : ∀ (k : Word), 0x5970 + k.toNat + 4 ≤ 0x5A70 → (0x5970 + k.toNat) % 4 = 0 →
      (B + BitVec.ofNat 32 0x5970 + k).toNat % 4 = 0 := fun k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  have sepB : ∀ (k : Word), 0x5970 + k.toNat + 4 ≤ 0x5A70 →
      Sep (B + BitVec.ofNat 32 0x5970 + k) 4 AC bootMainClosure0Code.length := fun k h1 => by
    rw [frame_lit k (by omega)]; exact F.sepHi (by omega) (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block acA1 C acA1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acA1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp, hA]
    exact ⟨⟨alB 0xFC (by decide) (by decide), sepB 0xFC (by decide)⟩,
      ⟨alB 0xF8 (by decide) (by decide), sepB 0xF8 (by decide)⟩,
      ⟨alB 0xF4 (by decide) (by decide), sepB 0xF4 (by decide)⟩,
      ⟨alB 0xF0 (by decide) (by decide), sepB 0xF0 (by decide)⟩,
      ⟨alB 0xEC (by decide) (by decide), sepB 0xEC (by decide)⟩,
      ⟨alB 0xE8 (by decide) (by decide), sepB 0xE8 (by decide)⟩,
      ⟨alB 0xE4 (by decide) (by decide), sepB 0xE4 (by decide)⟩,
      ⟨alB 0xE0 (by decide) (by decide), sepB 0xE0 (by decide)⟩,
      ⟨alB 0xDC (by decide) (by decide), sepB 0xDC (by decide)⟩,
      ⟨alB 0xD8 (by decide) (by decide), sepB 0xD8 (by decide)⟩,
      ⟨alB 0xD4 (by decide) (by decide), sepB 0xD4 (by decide)⟩,
      ⟨alB 0xD0 (by decide) (by decide), sepB 0xD0 (by decide)⟩,
      ⟨alB 0xCC (by decide) (by decide), sepB 0xCC (by decide)⟩⟩)
  have m1 : n1.mem = acSaves M B n := by
    rw [u1.mem]; simp only [runBlock, BInstr.run, acA1]; simp +decide only [upd, ↓reduceIte]
    rw [rsp, hA]
    simp (disch := decide) only [frame_lit, BitVec.reduceToNat, Nat.reduceAdd]
    unfold acSaves
    rfl
  have g : ∀ q, reg n1 q = (runBlock acA1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have z : ∀ x : Word, (0 : Word) + x = x := fun x => BitVec.zero_add x
  refine ⟨n1, c1, ⟨u1.pc, m1, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [g]; simp +decide only [runBlock, BInstr.run, acA1, upd, ↓reduceIte]; rw [rsp, hA]
    show B + BitVec.ofNat 32 0x5970 - (0x2000 + 0xFFFFFF20) = B + 0x3A50
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  · rw [g]; simp +decide only [runBlock, BInstr.run, acA1, upd, ↓reduceIte, aluEval, z]
  · rw [g]; simp +decide only [runBlock, BInstr.run, acA1, upd, ↓reduceIte, aluEval, z]
  · rw [g]; simp +decide only [runBlock, BInstr.run, acA1, upd, ↓reduceIte, aluEval, z]
  · rw [g]; simp +decide only [runBlock, BInstr.run, acA1, upd, ↓reduceIte, aluEval, z]
  · rw [g]; simp +decide only [runBlock, BInstr.run, acA1, upd, ↓reduceIte]
  · rw [g, runBlock_reg _ _ _ a3 hz (by decide)]
  · rw [g, runBlock_reg _ _ _ q hz (by simp only [acA1]; revert hq; revert q; decide)]

/-- From 0x184 to the return: close the frame and restore `ra` and
`s0..s11`. -/
def acE : List BInstr :=
  [.lui a0 0x2000, .aluImm .add a0 a0 0xFFFFFF20, .alu .add sp sp a0, .lw ra sp 0xFC,
   .lw (8 : Fin 32) sp 0xF8, .lw (9 : Fin 32) sp 0xF4, .lw (18 : Fin 32) sp 0xF0, .lw (19 : Fin 32) sp 0xEC,
   .lw (20 : Fin 32) sp 0xE8, .lw (21 : Fin 32) sp 0xE4, .lw (22 : Fin 32) sp 0xE0, .lw (23 : Fin 32) sp 0xDC,
   .lw (24 : Fin 32) sp 0xD8, .lw (25 : Fin 32) sp 0xD4, .lw (26 : Fin 32) sp 0xD0, .lw (27 : Fin 32) sp 0xCC,
   .aluImm .add sp sp 0x100]

set_option maxRecDepth 100000 in
theorem acE_end : blockEnd bootMainClosure0Code 0x184 acE = some 0x1A8 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The return**, from 0x184: restore `ra` and `s0..s11` from the top of
the frame, close it, and return. -/
theorem ac_ret {M : Word → BitVec 8} {n : Machine} {B : Word} {v : Nat → Word}
    (C : CodeIn M AC bootMainClosure0Code) (F : Fr B 0x5A70) (s : St M AC n 0x184 (reg n))
    (rsp : reg n sp = B + 0x3A50)
    (hS : ∀ k, k < 13 → memLoad32 M (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0) :
    ∃ n', Steps n n' ∧ n'.pc = v 0 ∧ n'.mem = M ∧ reg n' sp = B + 0x5A70 ∧
      (∀ k, k < 13 → reg n' (savedReg k) = v k) ∧
      reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hA : aluEval .add (B + 0x3A50) (aluEval .add 0x2000 0xFFFFFF20) = B + BitVec.ofNat 32 0x5970 := by
    show B + 0x3A50 + (0x2000 + 0xFFFFFF20) = B + BitVec.ofNat 32 0x5970
    rw [BitVec.add_assoc]; rfl
  have alB : ∀ (k : Word), 0x5970 + k.toNat + 4 ≤ 0x5A70 → (0x5970 + k.toNat) % 4 = 0 →
      (B + BitVec.ofNat 32 0x5970 + k).toNat % 4 = 0 := fun k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  obtain ⟨n1, c1, u1⟩ := s.block acE C acE_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acE]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp, hA]
    exact ⟨alB 0xFC (by decide) (by decide), alB 0xF8 (by decide) (by decide), alB 0xF4 (by decide) (by decide),
      alB 0xF0 (by decide) (by decide), alB 0xEC (by decide) (by decide), alB 0xE8 (by decide) (by decide),
      alB 0xE4 (by decide) (by decide), alB 0xE0 (by decide) (by decide), alB 0xDC (by decide) (by decide),
      alB 0xD8 (by decide) (by decide), alB 0xD4 (by decide) (by decide), alB 0xD0 (by decide) (by decide),
      alB 0xCC (by decide) (by decide)⟩)
  have m1 : (runBlock acE (M, reg n)).1 = M := rfl
  obtain ⟨n2, st2, pc2, mem2, regs2⟩ := u1.jalr (by rw [m1]; exact C) ac_at_1a8
  have ld : ∀ k, k < 13 → ∀ c : Word, c.toNat = 0xFC - 4 * k →
      memLoad32 M (B + BitVec.ofNat 32 0x5970 + c) = v k := fun k hk c hc => by
    rw [frame_lit _ (by omega), hc, show 0x5970 + (0xFC - 4 * k) = 0x5A6C - 4 * k by omega]; exact hS k hk
  have ra1 : (runBlock acE (M, reg n)).2 ra = v 0 := by
    simp +decide only [runBlock, BInstr.run, acE, upd, ↓reduceIte]
    rw [rsp, hA]; exact ld 0 (by decide) _ (by decide)
  refine ⟨n2, c1.trans (.single st2), ?_, mem2.trans m1, ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [pc2, ra1]; exact (congrArg (· &&& ~~~1) (BitVec.add_zero _)).trans hret
  · rw [regs2]; simp +decide only [runBlock, BInstr.run, acE, upd, ↓reduceIte]; rw [rsp, hA]
    show B + BitVec.ofNat 32 0x5970 + 0x100 = B + 0x5A70
    rw [BitVec.add_assoc]; rfl
  · rw [regs2]
    match k, hk with
    | 0, _ => simp +decide only [runBlock, BInstr.run, acE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 0 (by decide) _ (by decide)
    | 1, _ => simp +decide only [runBlock, BInstr.run, acE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 1 (by decide) _ (by decide)
    | 2, _ => simp +decide only [runBlock, BInstr.run, acE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 2 (by decide) _ (by decide)
    | 3, _ => simp +decide only [runBlock, BInstr.run, acE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 3 (by decide) _ (by decide)
    | 4, _ => simp +decide only [runBlock, BInstr.run, acE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 4 (by decide) _ (by decide)
    | 5, _ => simp +decide only [runBlock, BInstr.run, acE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 5 (by decide) _ (by decide)
    | 6, _ => simp +decide only [runBlock, BInstr.run, acE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 6 (by decide) _ (by decide)
    | 7, _ => simp +decide only [runBlock, BInstr.run, acE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 7 (by decide) _ (by decide)
    | 8, _ => simp +decide only [runBlock, BInstr.run, acE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 8 (by decide) _ (by decide)
    | 9, _ => simp +decide only [runBlock, BInstr.run, acE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 9 (by decide) _ (by decide)
    | 10, _ => simp +decide only [runBlock, BInstr.run, acE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 10 (by decide) _ (by decide)
    | 11, _ => simp +decide only [runBlock, BInstr.run, acE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 11 (by decide) _ (by decide)
    | 12, _ => simp +decide only [runBlock, BInstr.run, acE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 12 (by decide) _ (by decide)
    | _ + 13, h => exact absurd h (by omega)
  · rw [regs2, runBlock_reg _ _ _ 3 hz (by decide)]
  · rw [regs2, runBlock_reg _ _ _ 4 hz (by decide)]

/-- The closure returned to `v 0`: `sp`, the saved registers, `gp`, and
`tp` are back, and the memory satisfies `P`. -/
def AcRet (B : Word) (v : Nat → Word) (n0 : Machine) (P : (Word → BitVec 8) → Prop) : Prop :=
  ∃ n', Steps n0 n' ∧ n'.pc = v 0 ∧ reg n' sp = B + 0x5A70 ∧ (∀ k, k < 13 → reg n' (savedReg k) = v k) ∧
    reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧ P n'.mem

theorem AcRet.pre {B : Word} {v : Nat → Word} {n0 n1 : Machine} {P : (Word → BitVec 8) → Prop} (h : Steps n0 n1)
    (h3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32)) (h4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32))
    (e : AcRet B v n1 P) : AcRet B v n0 P := by
  obtain ⟨n', s, pc, sp', sv, r3, r4, hP⟩ := e
  exact ⟨n', h.trans s, pc, sp', sv, r3.trans h3, r4.trans h4, hP⟩

/-- From 0x16A to the call of `printf`. -/
def acN1 : List BInstr :=
  [.aluImm .add a1 (8 : Fin 32) 0xA, .lui a0 0x3FCC6000, .aluImm .add a0 a0 0x6C0]

/-- After `printf`: `None`. -/
def acN2 : List BInstr := [.aluImm .add a0 x0 0xFFFFFFFF, .sb (19 : Fin 32) a0 0xC]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The exit for a slot that can't be booted**, from 0x16A: log the slot
through the ROM's `printf`, write `None` (0xFF at `result + 0xC`, with the
result in `s3`), and return. Memory changes only below the frame, at the
ROM's stack, and at `result + 0xC`. -/
theorem ac_none {romBase : Word} {romCode : List Nat} {romStack : Nat}
    (log : RomFn romBase romCode 0x40000040 romStack fun _ => True) (hrs : romStack ≤ 0x3A50)
    {n : Machine} {B : Word} {v : Nat → Word}
    (C : CodeIn n.mem AC bootMainClosure0Code) (CR : CodeIn n.mem romBase romCode) (F : Fr B 0x5A70)
    (s : St n.mem AC n 0x16A (reg n)) (rsp : reg n sp = B + 0x3A50)
    (hS : ∀ k, k < 13 → memLoad32 n.mem (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0)
    (sRC : Sep (reg n (19 : Fin 32) + 0xC) 1 AC bootMainClosure0Code.length)
    (sRS : Sep (reg n (19 : Fin 32) + 0xC) 1 B 0x5A70) :
    AcRet B v n fun M' => M' (reg n (19 : Fin 32) + 0xC) = 0xFF ∧
      ∀ x, Sep x 1 B 0x5A70 → Sep x 1 (reg n (19 : Fin 32) + 0xC) 1 → M' x = n.mem x := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x176) acN1 C (by decide) ⟨trivial, trivial, trivial, trivial⟩
  have M1 : n1.mem = n.mem := u1.mem
  have r1 : ∀ q : Fin 32, q.val ≠ 10 → q.val ≠ 11 → reg n1 q = reg n q := fun q h0 h1 => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acN1]; revert h0 h1; revert q; decide)]
  have t1 : St n.mem AC n1 0x176 (reg n1) := ⟨u1.pc, M1, fun _ => rfl⟩
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := t1.callRa (cb := (0x40000040 : Word)) C ac_at_176 ac_at_17a (by decide) (by decide)
  have k12 : ∀ q : Fin 32, q.val ≠ 1 → q.val ≠ 10 → q.val ≠ 11 → reg n2 q = reg n q := fun q h1 h0 h2 => by
    rw [regs2, updz t1.zero (fun e => h1 (by rw [e]; rfl)), r1 q h0 h2]
  have sp2 : reg n2 sp = B + 0x3A50 := by rw [k12 sp (by decide) (by decide) (by decide)]; exact rsp
  have hspN : (B + 0x3A50 : Word).toNat = B.toNat + 0x3A50 := F.at 0x3A50 (by decide)
  obtain ⟨n3, c3, pc3, keep3, mem3⟩ := log n2 (by rw [mem2]; exact CR) pc2 trivial (by rw [sp2, hspN]; omega)
  have ra2 : reg n2 ra = AC + BitVec.ofNat 32 0x17E := by rw [regs2]; simp +decide only [upd, ↓reduceIte]
  obtain ⟨W, hW⟩ : ∃ W, B + BitVec.ofNat 32 (0x3A50 - romStack) = W := ⟨_, rfl⟩
  have hWn : W.toNat = B.toNat + (0x3A50 - romStack) := by rw [← hW]; exact F.at _ (by omega)
  have eW : reg n2 sp - BitVec.ofNat 32 romStack = W := by
    rw [sp2, ← hW]
    exact BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_sub, hspN, BitVec.toNat_ofNat, F.at _ (by omega), Nat.mod_eq_of_lt (a := romStack) (by omega)]
      omega)
  have wOut : ∀ x, Sep x 1 B 0x5A70 → Sep W romStack x 1 := fun x hx => by
    rw [← hW]; exact hx.symm.sub (c := 0x3A50 - romStack) (l := romStack) (by omega)
  have wHi : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep W romStack x 1 := fun x hx => by
    rw [← hW]; exact F.hiOut (c := 0x3A50 - romStack) (by omega) hx
  have m3 : ∀ x, Sep W romStack x 1 → n3.mem x = n.mem x := fun x hx => by
    rw [mem3 x (by rw [eW]; exact hx), mem2]
  have hAC : 0x40000000 ≤ AC.toNat := by decide
  have hACl : AC.toNat + bootMainClosure0Code.length ≤ 2 ^ 32 := by decide
  have C3 : CodeIn n3.mem AC bootMainClosure0Code := fun i hi => by
    have h2 : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have h := BitVec.toNat_add AC (BitVec.ofNat 32 i)
    rw [h2, Nat.mod_eq_of_lt (by omega)] at h
    rw [m3 _ (wHi _ (by rw [h]; omega))]
    exact C i hi
  have k3 : ∀ q : Fin 32, romKeep q = true → reg n3 q = reg n q := fun q hq => by
    rw [keep3 q hq]; exact k12 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide)
  have r19 : reg n3 (19 : Fin 32) = reg n (19 : Fin 32) := k3 19 (by decide)
  have s3 : St n3.mem AC n3 0x17E (reg n3) :=
    ⟨by rw [pc3, ra2]; exact even_clear _ (by decide), rfl, fun _ => rfl⟩
  obtain ⟨n4, c4, u4⟩ := s3.block (off' := 0x184) acN2 C3 (by decide) (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acN2]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [r19]; exact sRC)
  obtain ⟨M4, hM4⟩ : ∃ M4, (runBlock acN2 (n3.mem, reg n3)).1 = M4 := ⟨_, rfl⟩
  have eM4 : M4 = memStore8 n3.mem (reg n (19 : Fin 32) + 0xC) 0xFF := by
    rw [← hM4]; simp only [runBlock, BInstr.run, acN2]
    rw [updz s3.zero (by decide), upd_same (by decide), r19]
    exact congrArg (memStore8 _ _) (by rw [s3.zero]; decide)
  have r4 : ∀ q : Fin 32, q.val ≠ 10 → reg n4 q = reg n3 q := fun q h0 => by
    rw [u4.regs, runBlock_reg _ _ _ q s3.zero (by simp only [acN2]; revert h0; revert q; decide)]
  have t4 : St M4 AC n4 0x184 (reg n4) := ⟨u4.pc, by rw [u4.mem, hM4], fun _ => rfl⟩
  have C4 : CodeIn M4 AC bootMainClosure0Code := by rw [eM4]; exact C3.store8 sRC
  have keepM : ∀ x, Sep x 1 B 0x5A70 → Sep x 1 (reg n (19 : Fin 32) + 0xC) 1 → M4 x = n.mem x := fun x h1 h2 => by
    rw [eM4, memStore8_ne (fun e => h2 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e])),
      m3 x (wOut x h1)]
  have saveB : ∀ k, k < 13 → ∀ j, j < 4 →
      M4 (B + BitVec.ofNat 32 (0x5A6C - 4 * k) + BitVec.ofNat 32 j) =
        n.mem (B + BitVec.ofNat 32 (0x5A6C - 4 * k) + BitVec.ofNat 32 j) := fun k hk j hj => by
    rw [add_ofNat_assoc]
    have hx : (B + BitVec.ofNat 32 (0x5A6C - 4 * k + j)).toNat = B.toNat + (0x5A6C - 4 * k + j) := F.at _ (by omega)
    have hne : B + BitVec.ofNat 32 (0x5A6C - 4 * k + j) ≠ reg n (19 : Fin 32) + 0xC := fun e => by
      have := sRS 0 (by decide) (0x5A6C - 4 * k + j) (by omega)
      rw [add_ofNat_zero] at this; exact this e.symm
    rw [eM4, memStore8_ne hne, m3 _ (sep_of_le (by rw [hWn, hx]; omega) (by rw [hx]; have := F.hi; omega))]
  have hS4 : ∀ k, k < 13 → memLoad32 M4 (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k := fun k hk => by
    rw [memLoad32_congr (saveB k hk)]; exact hS k hk
  have sp4 : reg n4 sp = B + 0x3A50 := by
    rw [r4 sp (by decide), k3 sp (by decide)]; exact rsp
  obtain ⟨n5, c5, pc5, mem5, sp5, sv5, g5, t5⟩ := ac_ret C4 F t4 sp4 hS4 hret
  have q3 : reg n4 (3 : Fin 32) = reg n (3 : Fin 32) := by rw [r4 3 (by decide), k3 3 (by decide)]
  have q4 : reg n4 (4 : Fin 32) = reg n (4 : Fin 32) := by rw [r4 4 (by decide), k3 4 (by decide)]
  refine ⟨n5, ((c1.trans c2).trans c3).trans (c4.trans c5), pc5, sp5, sv5, g5.trans q3, t5.trans q4, ?_⟩
  rw [mem5]
  refine ⟨by rw [eM4]; simp only [memStore8, ite_true], keepM⟩

/-- What the `None` exit leaves: 0xFF at `r + 0xC`, and the rest of memory
outside the stack as it was in `M0`. -/
abbrev AcNone (B r : Word) (M0 M' : Word → BitVec 8) : Prop :=
  M' (r + 0xC) = 0xFF ∧ ∀ x, Sep x 1 B 0x5A70 → Sep x 1 (r + 0xC) 1 → M' x = M0 x

theorem AcRet.mono {B : Word} {v : Nat → Word} {n0 : Machine} {P Q : (Word → BitVec 8) → Prop}
    (h : ∀ M, P M → Q M) (e : AcRet B v n0 P) : AcRet B v n0 Q := by
  obtain ⟨n', s, pc, sp', sv, r3, r4, hP⟩ := e
  exact ⟨n', s, pc, sp', sv, r3, r4, h _ hP⟩

set_option maxHeartbeats 4000000 in
/-- A call of the ROM's `printf` at offset `o`: it returns to `o + 8`,
keeps the registers the ROM keeps, and writes only its stack, which sits at
the bottom of the closure's frame. -/
theorem ac_log {romBase : Word} {romCode : List Nat} {romStack : Nat}
    (log : RomFn romBase romCode 0x40000040 romStack fun _ => True) (hrs : romStack ≤ 0x3A50)
    {n : Machine} {B imm o' : Word} {o : Nat}
    (C : CodeIn n.mem AC bootMainClosure0Code) (CR : CodeIn n.mem romBase romCode) (F : Fr B 0x5A70)
    (s : St n.mem AC n o (reg n)) (rsp : reg n sp = B + 0x3A50)
    (h1 : fetchRel bootMainClosure0Code o = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (o + 4) = some (.jalr ra ra o', 4))
    (hb : AC + BitVec.ofNat 32 o + imm + o' = 0x40000040)
    (he : (AC + BitVec.ofNat 32 (o + 8)).toNat % 2 = 0) :
    ∃ n', Steps n n' ∧ n'.pc = AC + BitVec.ofNat 32 (o + 8) ∧
      (∀ q, romKeep q = true → reg n' q = reg n q) ∧
      ∀ x, Sep (B + BitVec.ofNat 32 (0x3A50 - romStack)) romStack x 1 → n'.mem x = n.mem x := by
  have hSl := F.lo; have hSh := F.hi
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := s.callRa (cb := (0x40000040 : Word)) C h1 h2 hb (by decide)
  have k2 : ∀ q : Fin 32, q.val ≠ 1 → reg n2 q = reg n q := fun q h => by
    rw [regs2, updz s.zero (fun e => h (by rw [e]; rfl))]
  have sp2 : reg n2 sp = B + 0x3A50 := by rw [k2 sp (by decide)]; exact rsp
  have hspN : (B + 0x3A50 : Word).toNat = B.toNat + 0x3A50 := F.at 0x3A50 (by decide)
  obtain ⟨n3, c3, pc3, keep3, mem3⟩ := log n2 (by rw [mem2]; exact CR) pc2 trivial (by rw [sp2, hspN]; omega)
  have eW : reg n2 sp - BitVec.ofNat 32 romStack = B + BitVec.ofNat 32 (0x3A50 - romStack) := by
    rw [sp2]
    exact BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_sub, hspN, BitVec.toNat_ofNat, F.at _ (by omega), Nat.mod_eq_of_lt (a := romStack) (by omega)]
      omega)
  refine ⟨n3, c2.trans c3, ?_, fun q hq => ?_, fun x hx => ?_⟩
  · rw [pc3, regs2, upd_same (by decide)]; exact even_clear _ he
  · rw [keep3 q hq]; exact k2 q (by revert hq; revert q; decide)
  · rw [mem3 x (by rw [eW]; exact hx), mem2]

set_option maxRecDepth 100000 in
/-- The code survives a write to the ROM's stack. -/
theorem ac_wCode {M M' : Word → BitVec 8} {B : Word} {romStack : Nat} (F : Fr B 0x5A70) (hrs : romStack ≤ 0x3A50)
    (hW : ∀ x, Sep (B + BitVec.ofNat 32 (0x3A50 - romStack)) romStack x 1 → M' x = M x)
    (C : CodeIn M AC bootMainClosure0Code) : CodeIn M' AC bootMainClosure0Code := fun i hi => by
  have hAC : 0x40000000 ≤ AC.toNat := by decide
  have hACl : AC.toNat + bootMainClosure0Code.length ≤ 2 ^ 32 := by decide
  have h2 : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have h := BitVec.toNat_add AC (BitVec.ofNat 32 i)
  rw [h2, Nat.mod_eq_of_lt (by omega)] at h
  rw [hW _ (F.hiOut (c := 0x3A50 - romStack) (by omega) (by rw [h]; omega))]
  exact C i hi

/-- The ROM's code survives a write to the ROM's stack. -/
theorem ac_wRom {M M' : Word → BitVec 8} {B romBase : Word} {romCode : List Nat} {romStack : Nat}
    (hrs : romStack ≤ 0x3A50) (sRB : Sep B 0x5A70 romBase romCode.length)
    (hW : ∀ x, Sep (B + BitVec.ofNat 32 (0x3A50 - romStack)) romStack x 1 → M' x = M x)
    (CR : CodeIn M romBase romCode) : CodeIn M' romBase romCode := fun i hi => by
  rw [hW _ ((sRB.sub (c := 0x3A50 - romStack) (l := romStack) (by omega)).subR (c := i) (l := 1) (by omega))]
  exact CR i hi

/-- The saves survive a write to the ROM's stack. -/
theorem ac_wSaves {M M' : Word → BitVec 8} {B : Word} {romStack : Nat} {v : Nat → Word}
    (F : Fr B 0x5A70) (hrs : romStack ≤ 0x3A50)
    (hW : ∀ x, Sep (B + BitVec.ofNat 32 (0x3A50 - romStack)) romStack x 1 → M' x = M x)
    (hS : ∀ k, k < 13 → memLoad32 M (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k) :
    ∀ k, k < 13 → memLoad32 M' (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k := fun k hk => by
  have hSh := F.hi
  have hb : ∀ j, j < 4 → M' (B + BitVec.ofNat 32 (0x5A6C - 4 * k) + BitVec.ofNat 32 j) =
      M (B + BitVec.ofNat 32 (0x5A6C - 4 * k) + BitVec.ofNat 32 j) := fun j hj => by
    rw [add_ofNat_assoc]
    have hx : (B + BitVec.ofNat 32 (0x5A6C - 4 * k + j)).toNat = B.toNat + (0x5A6C - 4 * k + j) := F.at _ (by omega)
    exact hW _ (sep_of_le (by rw [F.at _ (by omega), hx]; omega) (by rw [hx]; omega))
  rw [memLoad32_congr hb]
  exact hS k hk

/-- From 0x806 to the call of `printf`. -/
def acR1 : List BInstr := [.lui a0 0x3FCC6000, .aluImm .add a0 a0 0x656]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The rejection log**, from 0x806: log the rejection through the ROM's
`printf`, then take the `None` exit. -/
theorem ac_from806 {romBase : Word} {romCode : List Nat} {romStack : Nat}
    (log : RomFn romBase romCode 0x40000040 romStack fun _ => True) (hrs : romStack ≤ 0x3A50)
    {n : Machine} {B : Word} {v : Nat → Word}
    (C : CodeIn n.mem AC bootMainClosure0Code) (CR : CodeIn n.mem romBase romCode)
    (sRB : Sep B 0x5A70 romBase romCode.length) (F : Fr B 0x5A70)
    (s : St n.mem AC n 0x806 (reg n)) (rsp : reg n sp = B + 0x3A50)
    (hS : ∀ k, k < 13 → memLoad32 n.mem (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0)
    (sRC : Sep (reg n (19 : Fin 32) + 0xC) 1 AC bootMainClosure0Code.length)
    (sRS : Sep (reg n (19 : Fin 32) + 0xC) 1 B 0x5A70) :
    AcRet B v n (AcNone B (reg n (19 : Fin 32)) n.mem) := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x80E) acR1 C (by decide) ⟨trivial, trivial, trivial⟩
  have r1 : ∀ q : Fin 32, q.val ≠ 10 → reg n1 q = reg n q := fun q h0 => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acR1]; revert h0; revert q; decide)]
  have M1 : n1.mem = n.mem := u1.mem
  obtain ⟨n2, c2, pc2, k2, m2⟩ :=
    ac_log log hrs (by rw [M1]; exact C) (by rw [M1]; exact CR) F ⟨u1.pc, rfl, fun _ => rfl⟩
      (by rw [r1 sp (by decide)]; exact rsp) ac_at_80e ac_at_812 (by decide) (by decide)
  have W2 : ∀ x, Sep (B + BitVec.ofNat 32 (0x3A50 - romStack)) romStack x 1 → n2.mem x = n.mem x := fun x hx => by
    rw [m2 x hx, M1]
  have t2 : St n2.mem AC n2 0x816 (reg n2) := ⟨pc2, rfl, fun _ => rfl⟩
  have C2 := ac_wCode F hrs W2 C
  obtain ⟨n3, e3, t3⟩ := t2.jump C2 ac_at_816 (off' := 0x16A) (by decide) (by rw [t2.pc]; decide)
  have k3 : ∀ q : Fin 32, romKeep q = true → reg n3 q = reg n q := fun q hq => by
    rw [t3.regs q, k2 q hq, r1 q (by revert hq; revert q; decide)]
  have M3 : n3.mem = n2.mem := t3.mem
  have q19 : reg n3 (19 : Fin 32) = reg n (19 : Fin 32) := k3 19 (by decide)
  have h := ac_none log hrs (by rw [M3]; exact C2) (by rw [M3]; exact ac_wRom hrs sRB W2 CR) F
    ⟨t3.pc, rfl, fun _ => rfl⟩ (by rw [k3 sp (by decide)]; exact rsp)
    (by rw [M3]; exact ac_wSaves F hrs W2 hS) hret (by rw [q19]; exact sRC) (by rw [q19]; exact sRS)
  refine AcRet.pre (c1.trans (c2.trans (.single e3))) (k3 3 (by decide)) (k3 4 (by decide)) (h.mono ?_)
  intro M' ⟨h1, h2⟩
  rw [q19] at h1 h2
  refine ⟨h1, fun x hx hr => ?_⟩
  rw [h2 x hx hr, M3, W2 x (hx.symm.sub (c := 0x3A50 - romStack) (l := romStack) (by omega))]

/-- From 0x166: reload the result and the slot from the frame. -/
def acF1 : List BInstr := [.lw (19 : Fin 32) sp 0x40, .lw (8 : Fin 32) sp 0x3C]

theorem ac_fa {B : Word} (F : Fr B 0x5A70) (k : Word) (h1 : 0x3A50 + k.toNat + 4 ≤ 0x5A70)
    (h2 : (0x3A50 + k.toNat) % 4 = 0) : (B + 0x3A50 + k).toNat % 4 = 0 := by
  have hSa := F.al
  rw [show (B + 0x3A50 : Word) = B + BitVec.ofNat 32 0x3A50 from rfl, frame_lit k (by omega), F.at _ (by omega)]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The exit for a failed read**, from 0x166: reload the result from
`sp + 0x40`, then take the `None` exit. -/
theorem ac_fail {romBase : Word} {romCode : List Nat} {romStack : Nat}
    (log : RomFn romBase romCode 0x40000040 romStack fun _ => True) (hrs : romStack ≤ 0x3A50)
    {n : Machine} {B r : Word} {v : Nat → Word}
    (C : CodeIn n.mem AC bootMainClosure0Code) (CR : CodeIn n.mem romBase romCode) (F : Fr B 0x5A70)
    (s : St n.mem AC n 0x166 (reg n)) (rsp : reg n sp = B + 0x3A50)
    (hS : ∀ k, k < 13 → memLoad32 n.mem (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0)
    (hr : memLoad32 n.mem (B + BitVec.ofNat 32 0x3A90) = r)
    (sRC : Sep (r + 0xC) 1 AC bootMainClosure0Code.length) (sRS : Sep (r + 0xC) 1 B 0x5A70) :
    AcRet B v n (AcNone B r n.mem) := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x16A) acF1 C (by decide) (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acF1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp]; exact ⟨ac_fa F 0x40 (by decide) (by decide), ac_fa F 0x3C (by decide) (by decide)⟩)
  have r1 : ∀ q : Fin 32, q.val ≠ 8 → q.val ≠ 19 → reg n1 q = reg n q := fun q h0 h1 => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acF1]; revert h0 h1; revert q; decide)]
  have q19 : reg n1 (19 : Fin 32) = r := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acF1, upd, ↓reduceIte]
    rw [rsp, show (B + 0x3A50 + 0x40 : Word) = B + BitVec.ofNat 32 0x3A90 by rw [BitVec.add_assoc]; rfl]; exact hr
  have M1 : n1.mem = n.mem := u1.mem
  have h := ac_none log hrs (by rw [M1]; exact C) (by rw [M1]; exact CR) F ⟨u1.pc, rfl, fun _ => rfl⟩
    (by rw [r1 sp (by decide) (by decide)]; exact rsp) (by rw [M1]; exact hS) hret (by rw [q19]; exact sRC)
    (by rw [q19]; exact sRS)
  rw [q19, M1] at h
  exact AcRet.pre c1 (r1 3 (by decide) (by decide)) (r1 4 (by decide) (by decide)) h

/-- From 0x7D6: reload the result and the slot, and compare the rejection code with 0x20. -/
def acJ1 : List BInstr :=
  [.lw (19 : Fin 32) sp 0x40, .lw (8 : Fin 32) sp 0x3C, .aluImm .and a0 (21 : Fin 32) 0xFF, .aluImm .add a1 x0 0x20]

/-- From 0x7E6: load the jump table's entry for the rejection code. -/
def acJ2 : List BInstr :=
  [.aluImm .add a0 a0 0xFFFFFFE0, .aluImm .sll a0 a0 0x2, .lui a1 0x3FCC4000, .aluImm .add a1 a1 0x0,
    .alu .add a0 a0 a1, .lw a0 a0 0x0, .aluImm .add a1 x0 0x100]

/-- From 0x802: a code below 0x20 is its own log argument. -/
def acJ3 : List BInstr := [.aluImm .and a1 (21 : Fin 32) 0xFF]

/-- The jump table's targets, for rejection codes 0x20 to 0x26. -/
def acTgt : List Nat := [0x806, 0x7FC, 0x81E, 0x824, 0x818, 0x82A, 0x830]

theorem ac_k7 {k : Nat} (hk : k < 7) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega

theorem ac_tbl_addr {k : Nat} (hk : k < 7) :
    aluEval .add (aluEval .sll (aluEval .add (BitVec.ofNat 32 (0x20 + k)) 0xFFFFFFE0) 2) (aluEval .add 0x3FCC4000 0) + 0 =
      BitVec.ofNat 32 acRejectTableAddress + BitVec.ofNat 32 (4 * k) := by
  rcases ac_k7 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ac_tbl_al {k : Nat} (hk : k < 7) :
    (BitVec.ofNat 32 acRejectTableAddress + BitVec.ofNat 32 (4 * k)).toNat % 4 = 0 := by
  rcases ac_k7 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ac_tbl_load {M : Word → BitVec 8} (T : CodeIn M (BitVec.ofNat 32 acRejectTableAddress) acRejectTableData)
    {k : Nat} (hk : k < 7) :
    memLoad32 M (BitVec.ofNat 32 acRejectTableAddress + BitVec.ofNat 32 (4 * k)) =
      AC + BitVec.ofNat 32 (acTgt.getD k 0) := by
  rw [u2_data_word T (by decide) k (by simp only [acRejectTableData, List.length]; omega)]
  rcases ac_k7 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 4000000 in
/-- A jump-table target other than 0x806: set the log argument, then jump to 0x806. -/
theorem ac_tgt {romBase : Word} {romCode : List Nat} {romStack : Nat}
    (log : RomFn romBase romCode 0x40000040 romStack fun _ => True) (hrs : romStack ≤ 0x3A50)
    {n : Machine} {B : Word} {v : Nat → Word}
    (C : CodeIn n.mem AC bootMainClosure0Code) (CR : CodeIn n.mem romBase romCode)
    (sRB : Sep B 0x5A70 romBase romCode.length) (F : Fr B 0x5A70) {t t4 : Nat} {imm o : Word}
    (s : St n.mem AC n t (reg n)) (hbe : blockEnd bootMainClosure0Code t [.aluImm .add a1 x0 imm] = some t4)
    (hj : fetchRel bootMainClosure0Code t4 = some (.jal x0 o, 2))
    (hn : BitVec.ofNat 32 t4 + o = BitVec.ofNat 32 0x806) (rsp : reg n sp = B + 0x3A50)
    (hS : ∀ k, k < 13 → memLoad32 n.mem (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0)
    (sRC : Sep (reg n (19 : Fin 32) + 0xC) 1 AC bootMainClosure0Code.length)
    (sRS : Sep (reg n (19 : Fin 32) + 0xC) 1 B 0x5A70) :
    AcRet B v n (AcNone B (reg n (19 : Fin 32)) n.mem) := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block _ C hbe ⟨trivial, trivial⟩
  have M1 : n1.mem = n.mem := u1.mem
  have t1 : St n1.mem AC n1 t4 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  obtain ⟨n2, e2, t2⟩ := t1.jump (by rw [M1]; exact C) hj (off' := 0x806) hn
    (by rw [t1.pc, BitVec.add_assoc, hn]; decide)
  have M2 : n2.mem = n.mem := t2.mem.trans M1
  have q : ∀ q : Fin 32, q.val ≠ 11 → reg n2 q = reg n q := fun q h0 => by
    rw [t2.regs, u1.regs, runBlock_reg _ _ _ q hz (by
      simp only [List.filterMap, BInstr.dst, List.mem_cons, List.mem_nil_iff, or_false]
      intro e; exact h0 (by rw [e]; rfl))]
  have h := ac_from806 log hrs (by rw [M2]; exact C) (by rw [M2]; exact CR) sRB F ⟨t2.pc, rfl, fun _ => rfl⟩
    (by rw [q sp (by decide)]; exact rsp) (by rw [M2]; exact hS) hret (by rw [q 19 (by decide)]; exact sRC)
    (by rw [q 19 (by decide)]; exact sRS)
  rw [q 19 (by decide), M2] at h
  exact AcRet.pre (c1.trans (.single e2)) (q 3 (by decide)) (q 4 (by decide)) h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **A rejection**, from 0x7D6 with the rejection code in the low byte of
`s5`: reload the result from `sp + 0x40`, log the code's message, and take
the `None` exit. The jump table has entries for codes 0x20 to 0x26 only. -/
theorem ac_reject {romBase : Word} {romCode : List Nat} {romStack : Nat}
    (log : RomFn romBase romCode 0x40000040 romStack fun _ => True) (hrs : romStack ≤ 0x3A50)
    {n : Machine} {B r : Word} {v : Nat → Word}
    (C : CodeIn n.mem AC bootMainClosure0Code) (CR : CodeIn n.mem romBase romCode)
    (T : CodeIn n.mem (BitVec.ofNat 32 acRejectTableAddress) acRejectTableData)
    (sRB : Sep B 0x5A70 romBase romCode.length) (F : Fr B 0x5A70)
    (s : St n.mem AC n 0x7D6 (reg n)) (rsp : reg n sp = B + 0x3A50)
    (hS : ∀ k, k < 13 → memLoad32 n.mem (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0)
    (hc : (reg n (21 : Fin 32) &&& 0xFF).toNat < 0x27)
    (hr : memLoad32 n.mem (B + BitVec.ofNat 32 0x3A90) = r)
    (sRC : Sep (r + 0xC) 1 AC bootMainClosure0Code.length) (sRS : Sep (r + 0xC) 1 B 0x5A70) :
    AcRet B v n (AcNone B r n.mem) := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x7E2) acJ1 C (by decide) (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acJ1]; simp +decide only [upd, ↓reduceIte, and_true]
    rw [rsp]; exact ⟨ac_fa F 0x40 (by decide) (by decide), ac_fa F 0x3C (by decide) (by decide)⟩)
  have r1 : ∀ q : Fin 32, q.val ≠ 8 → q.val ≠ 19 → q.val ≠ 10 → q.val ≠ 11 → reg n1 q = reg n q :=
    fun q h0 h1 h2 h3 => by
      rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acJ1]; revert h0 h1 h2 h3; revert q; decide)]
  have q19 : reg n1 (19 : Fin 32) = r := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acJ1, upd, ↓reduceIte]
    rw [rsp, show (B + 0x3A50 + 0x40 : Word) = B + BitVec.ofNat 32 0x3A90 by rw [BitVec.add_assoc]; rfl]; exact hr
  have a0v : reg n1 a0 = reg n (21 : Fin 32) &&& 0xFF := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acJ1, upd, ↓reduceIte]; rfl
  have a1v : reg n1 a1 = 0x20 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acJ1, upd, ↓reduceIte]
  have M1 : n1.mem = n.mem := u1.mem
  have t1 : St n1.mem AC n1 0x7E2 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have C1 : CodeIn n1.mem AC bootMainClosure0Code := by rw [M1]; exact C
  generalize hcd : reg n (21 : Fin 32) &&& 0xFF = c at hc a0v
  by_cases hlt : c.toNat < 0x20
  · obtain ⟨n2, e2, t2⟩ := t1.taken C1 0x802 ac_at_7e2 (by decide)
      (by rw [a0v, a1v]; simp only [branchTaken, BitVec.ult, decide_eq_true_eq]; exact hlt)
    obtain ⟨n3, c3, u3⟩ := t2.block (off' := 0x806) acJ3 C1 (by decide) ⟨trivial, trivial⟩
    have M3 : n3.mem = n.mem := u3.mem.trans M1
    have q : ∀ q : Fin 32, q.val ≠ 8 → q.val ≠ 19 → q.val ≠ 10 → q.val ≠ 11 → reg n3 q = reg n q :=
      fun q h0 h1 h2 h3 => by
        rw [u3.regs, runBlock_reg _ _ _ q t2.zero (by simp only [acJ3]; revert h3; revert q; decide),
          r1 q h0 h1 h2 h3]
    have q19' : reg n3 (19 : Fin 32) = r := by
      rw [u3.regs, runBlock_reg _ _ _ _ t2.zero (by decide), q19]
    have h := ac_from806 log hrs (by rw [M3]; exact C) (by rw [M3]; exact CR) sRB F ⟨u3.pc, rfl, fun _ => rfl⟩
      (by rw [q sp (by decide) (by decide) (by decide) (by decide)]; exact rsp) (by rw [M3]; exact hS) hret
      (by rw [q19']; exact sRC) (by rw [q19']; exact sRS)
    rw [q19', M3] at h
    exact AcRet.pre (c1.trans ((Steps.single e2).trans c3)) (q 3 (by decide) (by decide) (by decide) (by decide))
      (q 4 (by decide) (by decide) (by decide) (by decide)) h
  · have hge : 0x20 ≤ c.toNat := by omega
    obtain ⟨n2, e2, t2⟩ := t1.notTaken C1 0x7E6 ac_at_7e2 (by decide)
      (by rw [a0v, a1v]; simp only [branchTaken, BitVec.ult, decide_eq_false_iff_not]; exact hlt)
    have hk : c.toNat - 0x20 < 7 := by omega
    have hck : c = BitVec.ofNat 32 (0x20 + (c.toNat - 0x20)) := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    generalize c.toNat - 0x20 = k at hk hck
    subst hck
    obtain ⟨n3, c3, u3⟩ := t2.block (off' := 0x7FA) acJ2 C1 (by decide) (by
      simp only [BlockOk, BInstr.ok, BInstr.run, acJ2]; simp +decide only [upd, ↓reduceIte, and_true]
      rw [a0v, ac_tbl_addr hk]; exact ⟨trivial, trivial, trivial, trivial, trivial, ac_tbl_al hk⟩)
    have a3 : reg n3 a0 = AC + BitVec.ofNat 32 (acTgt.getD k 0) := by
      rw [u3.regs]; simp +decide only [runBlock, BInstr.run, acJ2, upd, ↓reduceIte]
      rw [a0v, ac_tbl_addr hk, M1]; exact ac_tbl_load T hk
    have q3 : ∀ q : Fin 32, q.val ≠ 8 → q.val ≠ 19 → q.val ≠ 10 → q.val ≠ 11 → reg n3 q = reg n q :=
      fun q h0 h1 h2 h3 => by
        rw [u3.regs, runBlock_reg _ _ _ q t2.zero (by simp only [acJ2]; revert h2 h3; revert q; decide),
          r1 q h0 h1 h2 h3]
    have q19' : reg n3 (19 : Fin 32) = r := by
      rw [u3.regs, runBlock_reg _ _ _ _ t2.zero (by decide), q19]
    have M3 : n3.mem = n.mem := u3.mem.trans M1
    have t3 : St n.mem AC n3 0x7FA (reg n3) := ⟨u3.pc, M3, fun _ => rfl⟩
    obtain ⟨n4, e4, pc4, m4, k4⟩ := t3.jalr C ac_at_7fa
    have M4 : n4.mem = n.mem := m4
    have q4 : ∀ q : Fin 32, q.val ≠ 8 → q.val ≠ 19 → q.val ≠ 10 → q.val ≠ 11 → reg n4 q = reg n q :=
      fun q h0 h1 h2 h3 => by rw [k4, q3 q h0 h1 h2 h3]
    have q19'' : reg n4 (19 : Fin 32) = r := by rw [k4, q19']
    have hpc : n4.pc = AC + BitVec.ofNat 32 (acTgt.getD k 0) := by
      rw [pc4, a3]; rcases ac_k7 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have t4 : St n4.mem AC n4 (acTgt.getD k 0) (reg n4) := ⟨hpc, rfl, fun _ => rfl⟩
    have C4 : CodeIn n4.mem AC bootMainClosure0Code := by rw [M4]; exact C
    have CR4 : CodeIn n4.mem romBase romCode := by rw [M4]; exact CR
    have rsp4 : reg n4 sp = B + 0x3A50 := by rw [q4 sp (by decide) (by decide) (by decide) (by decide)]; exact rsp
    have hS4 : ∀ k, k < 13 → memLoad32 n4.mem (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k := by
      rw [M4]; exact hS
    have sRC4 : Sep (reg n4 (19 : Fin 32) + 0xC) 1 AC bootMainClosure0Code.length := by rw [q19'']; exact sRC
    have sRS4 : Sep (reg n4 (19 : Fin 32) + 0xC) 1 B 0x5A70 := by rw [q19'']; exact sRS
    have h : AcRet B v n4 (AcNone B (reg n4 (19 : Fin 32)) n4.mem) := by
      rcases ac_k7 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac_from806 log hrs C4 CR4 sRB F t4 rsp4 hS4 hret sRC4 sRS4
      · exact ac_tgt log hrs C4 CR4 sRB F t4 (imm := 0x101) (by decide) ac_at_800 (by decide) rsp4 hS4 hret sRC4 sRS4
      · exact ac_tgt log hrs C4 CR4 sRB F t4 (imm := 0x102) (by decide) ac_at_822 (by decide) rsp4 hS4 hret sRC4 sRS4
      · exact ac_tgt log hrs C4 CR4 sRB F t4 (imm := 0x103) (by decide) ac_at_828 (by decide) rsp4 hS4 hret sRC4 sRS4
      · exact ac_tgt log hrs C4 CR4 sRB F t4 (imm := 0x104) (by decide) ac_at_81c (by decide) rsp4 hS4 hret sRC4 sRS4
      · exact ac_tgt log hrs C4 CR4 sRB F t4 (imm := 0x105) (by decide) ac_at_82e (by decide) rsp4 hS4 hret sRC4 sRS4
      · exact ac_tgt log hrs C4 CR4 sRB F t4 (imm := 0x106) (by decide) ac_at_834 (by decide) rsp4 hS4 hret sRC4 sRS4
    rw [q19'', M4] at h
    exact AcRet.pre (c1.trans ((Steps.single e2).trans (c3.trans (.single e4))))
      (q4 3 (by decide) (by decide) (by decide) (by decide)) (q4 4 (by decide) (by decide) (by decide) (by decide)) h

end C3.RV32.Ac
