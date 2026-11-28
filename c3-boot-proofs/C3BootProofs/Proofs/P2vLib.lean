import C3BootProofs.Proofs.P2vAt
import C3BootProofs.Proofs.Pv384A

/-!
# `p256_verify_prehash`: the frame, the prologue, and the return

`c3_crypto::p256_verify_prehash(point, prehash, r, s)` opens a frame of
0x13F0 bytes. With the frame's base at `B + 0x21A0`, the callees' frames go
below it, down to `B - 0x1A0`, and `Fr B 0x3590` describes the whole stack.
The prologue saves `ra` and `s0..s11` at the top of the frame and keeps the
arguments in `s1`, `s3`, `s0`, and `s4`. Every failed check leaves through
0x142, which sets `a0` to 0, and the epilogue at 0x144 restores the saved
registers and returns `a0`.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- What a step of `p256_verify_prehash` and its callees may write: the
stack from `B - 0x1A0` to the caller's `sp`. -/
def P2vR (B : Word) (x : Word) : Prop := Sep (B + 0xFFFFFE60) 0x3730 x 1

/-- `M'` agrees with `M` on the frame, except for the `w` bytes at offset `c`. -/
def P2vKeep (B : Word) (M M' : Word → BitVec 8) (c w : Nat) : Prop :=
  ∀ e, e + 1 ≤ 0x13F0 → (e < c ∨ c + w ≤ e) →
    M' (B + 0x21A0 + BitVec.ofNat 32 e) = M (B + 0x21A0 + BitVec.ofNat 32 e)

/-- The prologue's saves, in order, at the top of the frame. -/
def p2vSaves (M : Word → BitVec 8) (B : Word) (n : Machine) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32
    (memStore32 (memStore32 (memStore32 (memStore32 M
    (B + BitVec.ofNat 32 0x358C) (reg n ra)) (B + BitVec.ofNat 32 0x3588) (reg n (8 : Fin 32)))
    (B + BitVec.ofNat 32 0x3584) (reg n (9 : Fin 32))) (B + BitVec.ofNat 32 0x3580) (reg n (18 : Fin 32)))
    (B + BitVec.ofNat 32 0x357C) (reg n (19 : Fin 32))) (B + BitVec.ofNat 32 0x3578) (reg n (20 : Fin 32)))
    (B + BitVec.ofNat 32 0x3574) (reg n (21 : Fin 32))) (B + BitVec.ofNat 32 0x3570) (reg n (22 : Fin 32)))
    (B + BitVec.ofNat 32 0x356C) (reg n (23 : Fin 32))) (B + BitVec.ofNat 32 0x3568) (reg n (24 : Fin 32)))
    (B + BitVec.ofNat 32 0x3564) (reg n (25 : Fin 32))) (B + BitVec.ofNat 32 0x3560) (reg n (26 : Fin 32)))
    (B + BitVec.ofNat 32 0x355C) (reg n (27 : Fin 32))

theorem p2vSaves_read {M : Word → BitVec 8} {B : Word} {n : Machine} :
    ∀ k, k < 13 → memLoad32 (p2vSaves M B n) (B + BitVec.ofNat 32 (0x358C - 4 * k)) = reg n (savedReg k) := by
  intro k hk
  match k, hk with
  | 0, _ => unfold p2vSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 1, _ => unfold p2vSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 2, _ => unfold p2vSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 3, _ => unfold p2vSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 4, _ => unfold p2vSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 5, _ => unfold p2vSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 6, _ => unfold p2vSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 7, _ => unfold p2vSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 8, _ => unfold p2vSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 9, _ => unfold p2vSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 10, _ => unfold p2vSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 11, _ => unfold p2vSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl
  | 12, _ => unfold p2vSaves; simp (disch := decide) only [ld_st_pv, ite_eq_right, ite_eq_left]; rfl

theorem p2vSaves_out {M : Word → BitVec 8} {B : Word} {n : Machine} {x : Word}
    (h : Sep (B + BitVec.ofNat 32 0x355C) 0x34 x 1) : p2vSaves M B n x = M x := by
  have hs : ∀ c, 0x355C ≤ c → c + 4 ≤ 0x3590 → Sep (B + BitVec.ofNat 32 c) 4 x 1 := fun c h1 h2 => by
    have := h.sub (c := c - 0x355C) (l := 4) (by omega)
    rwa [add_ofNat_assoc, show 0x355C + (c - 0x355C) = c by omega] at this
  unfold p2vSaves
  simp (disch := first | decide | exact hs _ (by decide) (by decide)) only [memStore32_get_sep]

/-- From the entry to the first range check at 0x48. -/
def p2vA1 : List BInstr :=
  [.aluImm .add sp sp 0xFFFFF810, .aluImm .add a4 sp 0x780, .sw a4 ra 0x6C, .sw a4 (8 : Fin 32) 0x68,
   .sw a4 (9 : Fin 32) 0x64, .sw a4 (18 : Fin 32) 0x60, .sw a4 (19 : Fin 32) 0x5C, .sw a4 (20 : Fin 32) 0x58,
   .sw a4 (21 : Fin 32) 0x54, .sw a4 (22 : Fin 32) 0x50, .sw a4 (23 : Fin 32) 0x4C, .sw a4 (24 : Fin 32) 0x48,
   .sw a4 (25 : Fin 32) 0x44, .sw a4 (26 : Fin 32) 0x40, .sw a4 (27 : Fin 32) 0x3C,
   .aluImm .add sp sp 0xFFFFF800, .aluImm .add sp sp 0xFFFFFC00, .alu .add (20 : Fin 32) x0 a3,
   .alu .add (8 : Fin 32) x0 a2, .alu .add (19 : Fin 32) x0 a1, .alu .add (9 : Fin 32) x0 a0]

set_option maxRecDepth 100000 in
theorem p2vA1_end : blockEnd p256VerifyPrehashCode 0 p2vA1 = some 0x48 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The prologue**, from the entry to 0x48: save `ra` and `s0..s11`, open
the frame at `B + 0x21A0`, and keep the point in `s1`, the prehash in `s3`,
`r` in `s0`, and `s` in `s4`. -/
theorem p2v_pro {M : Word → BitVec 8} {n : Machine} {B : Word} (C : CodeIn M P2V p256VerifyPrehashCode)
    (F : Fr B 0x3590) (s : St M P2V n 0 (reg n)) (rsp : reg n sp = B + 0x3590) :
    ∃ n', Steps n n' ∧ St (p2vSaves M B n) P2V n' 0x48 (reg n') ∧
      reg n' sp = B + 0x21A0 ∧ reg n' (9 : Fin 32) = reg n a0 ∧ reg n' (19 : Fin 32) = reg n a1 ∧
      reg n' (8 : Fin 32) = reg n a2 ∧ reg n' (20 : Fin 32) = reg n a3 ∧
      ∀ q, q.val ∈ [3, 4] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hA : aluEval .add (B + 0x3590) 0xFFFFF810 = B + BitVec.ofNat 32 0x2DA0 := by
    show B + 0x3590 + 0xFFFFF810 = B + BitVec.ofNat 32 0x2DA0
    rw [BitVec.add_assoc]; rfl
  have hA4 : aluEval .add (B + BitVec.ofNat 32 0x2DA0) 0x780 = B + BitVec.ofNat 32 0x3520 := by
    show B + BitVec.ofNat 32 0x2DA0 + 0x780 = B + BitVec.ofNat 32 0x3520
    rw [BitVec.add_assoc]; rfl
  have hS : aluEval .add (aluEval .add (B + BitVec.ofNat 32 0x2DA0) 0xFFFFF800) 0xFFFFFC00 =
      B + BitVec.ofNat 32 0x21A0 := by
    show B + BitVec.ofNat 32 0x2DA0 + 0xFFFFF800 + 0xFFFFFC00 = B + BitVec.ofNat 32 0x21A0
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have alB : ∀ (c : Nat) (k : Word), c + k.toNat + 4 ≤ 0x3590 → (c + k.toNat) % 4 = 0 →
      (B + BitVec.ofNat 32 c + k).toNat % 4 = 0 := fun c k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  have sepB : ∀ (c : Nat) (k : Word), c + k.toNat + 4 ≤ 0x3590 →
      Sep (B + BitVec.ofNat 32 c + k) 4 P2V p256VerifyPrehashCode.length := fun c k h1 => by
    rw [frame_lit k (by omega)]; exact F.sepHi (by omega) (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block p2vA1 C p2vA1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, p2vA1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp, hA, hA4]
    exact ⟨⟨alB 0x3520 0x6C (by decide) (by decide), sepB 0x3520 0x6C (by decide)⟩,
      ⟨alB 0x3520 0x68 (by decide) (by decide), sepB 0x3520 0x68 (by decide)⟩,
      ⟨alB 0x3520 0x64 (by decide) (by decide), sepB 0x3520 0x64 (by decide)⟩,
      ⟨alB 0x3520 0x60 (by decide) (by decide), sepB 0x3520 0x60 (by decide)⟩,
      ⟨alB 0x3520 0x5C (by decide) (by decide), sepB 0x3520 0x5C (by decide)⟩,
      ⟨alB 0x3520 0x58 (by decide) (by decide), sepB 0x3520 0x58 (by decide)⟩,
      ⟨alB 0x3520 0x54 (by decide) (by decide), sepB 0x3520 0x54 (by decide)⟩,
      ⟨alB 0x3520 0x50 (by decide) (by decide), sepB 0x3520 0x50 (by decide)⟩,
      ⟨alB 0x3520 0x4C (by decide) (by decide), sepB 0x3520 0x4C (by decide)⟩,
      ⟨alB 0x3520 0x48 (by decide) (by decide), sepB 0x3520 0x48 (by decide)⟩,
      ⟨alB 0x3520 0x44 (by decide) (by decide), sepB 0x3520 0x44 (by decide)⟩,
      ⟨alB 0x3520 0x40 (by decide) (by decide), sepB 0x3520 0x40 (by decide)⟩,
      ⟨alB 0x3520 0x3C (by decide) (by decide), sepB 0x3520 0x3C (by decide)⟩⟩)
  have m1 : n1.mem = p2vSaves M B n := by
    rw [u1.mem]; simp only [runBlock, BInstr.run, p2vA1]; simp +decide only [upd, ↓reduceIte]
    rw [rsp, hA, hA4]
    simp (disch := decide) only [frame_lit, BitVec.reduceToNat, Nat.reduceAdd]
    unfold p2vSaves
    rfl
  have g : ∀ q, reg n1 q = (runBlock p2vA1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have z : ∀ x : Word, (0 : Word) + x = x := fun x => BitVec.zero_add x
  refine ⟨n1, c1, ⟨u1.pc, m1, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [g]; simp +decide only [runBlock, BInstr.run, p2vA1, upd, ↓reduceIte]; rw [rsp, hA, hS]; rfl
  · rw [g]; simp +decide only [runBlock, BInstr.run, p2vA1, upd, ↓reduceIte, aluEval, z]
  · rw [g]; simp +decide only [runBlock, BInstr.run, p2vA1, upd, ↓reduceIte, aluEval, z]
  · rw [g]; simp +decide only [runBlock, BInstr.run, p2vA1, upd, ↓reduceIte, aluEval, z]
  · rw [g]; simp +decide only [runBlock, BInstr.run, p2vA1, upd, ↓reduceIte, aluEval, z]
  · rw [g, runBlock_reg _ _ _ q hz (by simp only [p2vA1]; revert hq; revert q; decide)]

/-- From 0x144 to the return: restore `ra` and `s0..s11` and close the frame. -/
def p2vE : List BInstr :=
  [.aluImm .add sp sp 0x7F0, .aluImm .add sp sp 0x410, .aluImm .add a1 sp 0x780, .lw ra a1 0x6C,
   .lw (8 : Fin 32) a1 0x68, .lw (9 : Fin 32) a1 0x64, .lw (18 : Fin 32) a1 0x60, .lw (19 : Fin 32) a1 0x5C,
   .lw (20 : Fin 32) a1 0x58, .lw (21 : Fin 32) a1 0x54, .lw (22 : Fin 32) a1 0x50, .lw (23 : Fin 32) a1 0x4C,
   .lw (24 : Fin 32) a1 0x48, .lw (25 : Fin 32) a1 0x44, .lw (26 : Fin 32) a1 0x40, .lw (27 : Fin 32) a1 0x3C,
   .aluImm .add sp sp 0x7F0]

set_option maxRecDepth 100000 in
theorem p2vE_end : blockEnd p256VerifyPrehashCode 0x144 p2vE = some 0x184 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The return**, from 0x144: restore `ra` and `s0..s11` from the top of
the frame, close it, and return `a0`. -/
theorem p2v_ret {M : Word → BitVec 8} {n : Machine} {B : Word} {v : Nat → Word}
    (C : CodeIn M P2V p256VerifyPrehashCode) (F : Fr B 0x3590) (s : St M P2V n 0x144 (reg n))
    (rsp : reg n sp = B + 0x21A0)
    (hS : ∀ k, k < 13 → memLoad32 M (B + BitVec.ofNat 32 (0x358C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0) :
    ∃ n', Steps n n' ∧ n'.pc = v 0 ∧ n'.mem = M ∧ reg n' sp = B + 0x3590 ∧
      (∀ k, k < 13 → reg n' (savedReg k) = v k) ∧ reg n' a0 = reg n a0 ∧
      reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hA : aluEval .add (aluEval .add (aluEval .add (B + 0x21A0) 0x7F0) 0x410) 0x780 = B + BitVec.ofNat 32 0x3520 := by
    show B + 0x21A0 + 0x7F0 + 0x410 + 0x780 = B + BitVec.ofNat 32 0x3520
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; rfl
  have alB : ∀ (k : Word), 0x3520 + k.toNat + 4 ≤ 0x3590 → (0x3520 + k.toNat) % 4 = 0 →
      (B + BitVec.ofNat 32 0x3520 + k).toNat % 4 = 0 := fun k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  obtain ⟨n1, c1, u1⟩ := s.block p2vE C p2vE_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, p2vE]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp, hA]
    exact ⟨alB 0x6C (by decide) (by decide), alB 0x68 (by decide) (by decide), alB 0x64 (by decide) (by decide),
      alB 0x60 (by decide) (by decide), alB 0x5C (by decide) (by decide), alB 0x58 (by decide) (by decide),
      alB 0x54 (by decide) (by decide), alB 0x50 (by decide) (by decide), alB 0x4C (by decide) (by decide),
      alB 0x48 (by decide) (by decide), alB 0x44 (by decide) (by decide), alB 0x40 (by decide) (by decide),
      alB 0x3C (by decide) (by decide)⟩)
  have m1 : (runBlock p2vE (M, reg n)).1 = M := rfl
  obtain ⟨n2, st2, pc2, mem2, regs2⟩ := u1.jalr (by rw [m1]; exact C) p2v_at_184
  have ld : ∀ k, k < 13 → ∀ c : Word, c.toNat = 0x6C - 4 * k →
      memLoad32 M (B + BitVec.ofNat 32 0x3520 + c) = v k := fun k hk c hc => by
    rw [frame_lit _ (by omega), hc, show 0x3520 + (0x6C - 4 * k) = 0x358C - 4 * k by omega]; exact hS k hk
  have ra1 : (runBlock p2vE (M, reg n)).2 ra = v 0 := by
    simp +decide only [runBlock, BInstr.run, p2vE, upd, ↓reduceIte]
    rw [rsp, hA]; exact ld 0 (by decide) _ (by decide)
  refine ⟨n2, c1.trans (.single st2), ?_, mem2.trans m1, ?_, fun k hk => ?_, ?_, ?_, ?_⟩
  · rw [pc2, ra1]; exact (congrArg (· &&& ~~~1) (BitVec.add_zero _)).trans hret
  · rw [regs2]; simp +decide only [runBlock, BInstr.run, p2vE, upd, ↓reduceIte]; rw [rsp]
    show B + 0x21A0 + 0x7F0 + 0x410 + 0x7F0 = B + 0x3590
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; rfl
  · rw [regs2]
    match k, hk with
    | 0, _ => simp +decide only [runBlock, BInstr.run, p2vE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 0 (by decide) _ (by decide)
    | 1, _ => simp +decide only [runBlock, BInstr.run, p2vE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 1 (by decide) _ (by decide)
    | 2, _ => simp +decide only [runBlock, BInstr.run, p2vE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 2 (by decide) _ (by decide)
    | 3, _ => simp +decide only [runBlock, BInstr.run, p2vE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 3 (by decide) _ (by decide)
    | 4, _ => simp +decide only [runBlock, BInstr.run, p2vE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 4 (by decide) _ (by decide)
    | 5, _ => simp +decide only [runBlock, BInstr.run, p2vE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 5 (by decide) _ (by decide)
    | 6, _ => simp +decide only [runBlock, BInstr.run, p2vE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 6 (by decide) _ (by decide)
    | 7, _ => simp +decide only [runBlock, BInstr.run, p2vE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 7 (by decide) _ (by decide)
    | 8, _ => simp +decide only [runBlock, BInstr.run, p2vE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 8 (by decide) _ (by decide)
    | 9, _ => simp +decide only [runBlock, BInstr.run, p2vE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 9 (by decide) _ (by decide)
    | 10, _ => simp +decide only [runBlock, BInstr.run, p2vE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 10 (by decide) _ (by decide)
    | 11, _ => simp +decide only [runBlock, BInstr.run, p2vE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 11 (by decide) _ (by decide)
    | 12, _ => simp +decide only [runBlock, BInstr.run, p2vE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 12 (by decide) _ (by decide)
    | _ + 13, h => exact absurd h (by omega)
  · rw [regs2, runBlock_reg _ _ _ a0 hz (by decide)]
  · rw [regs2, runBlock_reg _ _ _ 3 hz (by decide)]
  · rw [regs2, runBlock_reg _ _ _ 4 hz (by decide)]

/-- `p256_verify_prehash` returned `a` to `v 0`: `sp`, the saved registers,
`gp`, and `tp` are back, and memory apart from the stack is as it was. -/
def P2vRet (B : Word) (v : Nat → Word) (n0 : Machine) (a : Word) : Prop :=
  ∃ n', Steps n0 n' ∧ n'.pc = v 0 ∧ reg n' sp = B + 0x3590 ∧ (∀ k, k < 13 → reg n' (savedReg k) = v k) ∧
    reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧ reg n' a0 = a ∧
    ∀ x, P2vR B x → n'.mem x = n0.mem x

theorem P2vRet.pre {B a : Word} {v : Nat → Word} {n0 n1 : Machine} (h : Steps n0 n1)
    (h3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32)) (h4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32))
    (hm : ∀ x, P2vR B x → n1.mem x = n0.mem x) (e : P2vRet B v n1 a) : P2vRet B v n0 a := by
  obtain ⟨n', s, pc, sp', sv, r3, r4, ra, m⟩ := e
  exact ⟨n', h.trans s, pc, sp', sv, r3.trans h3, r4.trans h4, ra, fun x hx => (m x hx).trans (hm x hx)⟩

/-- The return through the epilogue at 0x144 keeps `a0`. -/
theorem p2v_retR {B : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x3590)
    (C : CodeIn n.mem P2V p256VerifyPrehashCode) (s : St n.mem P2V n 0x144 (reg n)) (t : Steps n0 n)
    (fR : ∀ x, P2vR B x → n.mem x = n0.mem x)
    (V : ∀ k, k < 13 → memLoad32 n.mem (B + BitVec.ofNat 32 (0x358C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0)
    (rsp : reg n sp = B + 0x21A0) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) : P2vRet B v n0 (reg n a0) := by
  obtain ⟨n', c', pc', mem', sp', sv', a0', g', t'⟩ := p2v_ret C F s rsp V hret
  exact ⟨n', t.trans c', pc', sp', sv', g'.trans r3, t'.trans r4, a0', fun x hx => by rw [mem']; exact fR x hx⟩

/-- **The failing exit**: from 0x142, `p256_verify_prehash` returns 0. -/
theorem p2v_false {B : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x3590)
    (C : CodeIn n.mem P2V p256VerifyPrehashCode) (s : St n.mem P2V n 0x142 (reg n)) (t : Steps n0 n)
    (fR : ∀ x, P2vR B x → n.mem x = n0.mem x)
    (V : ∀ k, k < 13 → memLoad32 n.mem (B + BitVec.ofNat 32 (0x358C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0)
    (rsp : reg n sp = B + 0x21A0) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) : P2vRet B v n0 0 := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x144) [.aluImm .add a0 x0 0x0] C (by decide) ⟨trivial, trivial⟩
  have r1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs]; simp only [runBlock, BInstr.run]; exact updz hz hq
  have a1 : reg n1 a0 = 0 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte, aluEval]; rw [hz]; rfl
  have M1 : n1.mem = n.mem := u1.mem
  have s1 : St n1.mem P2V n1 0x144 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have e := p2v_retR F (by rw [M1]; exact C) s1 (t.trans c1) (fun x hx => by rw [M1]; exact fR x hx)
    (fun k hk => by rw [M1]; exact V k hk) hret (by rw [r1 sp (by decide)]; exact rsp)
    (by rw [r1 3 (by decide)]; exact r3) (by rw [r1 4 (by decide)]; exact r4)
  rwa [a1] at e

end C3.RV32.P2v
