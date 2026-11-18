import C3BootProofs.Proofs.P2Lib
import C3BootProofs.Proofs.Fs256At
import C3BootProofs.Proofs.Rp384

/-!
# `VerifyingKey<NistP256>::from_sec1_bytes`

The P-256 counterpart of `Fs384Main`: 65 bytes, tag 4, then `x` and `y` below
`p` with `y² = x³ + ax + b`. Its length check (`Tag::message_len` must be 65)
leaves the compressed and identity branches unreachable.
-/

namespace C3.RV32.Gs

open C3.Image C3.RV32.Dq C3.RV32.P3 C3.RV32.P2 C3.RV32.Fs

set_option maxRecDepth 20000

/-- `from_sec1_bytes`'s code and its callees'. -/
structure GsCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M GP p256FromSec1Code
  K : P2Code M

theorem GsCode.hi {M M' : Word → BitVec 8} (C : GsCode M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    GsCode M' := ⟨codeHi C.self (by decide) (by decide) h, C.K.hi h⟩

def gsA1 : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFD30, .aluImm .add a2 sp 0x280, .sw a2 ra 0x4C, .sw a2 (8 : Fin 32) 0x48,
   .sw a2 (9 : Fin 32) 0x44, .sw a2 (18 : Fin 32) 0x40, .sw a2 (19 : Fin 32) 0x3C, .sw a2 (20 : Fin 32) 0x38,
   .sw a2 (21 : Fin 32) 0x34, .sw a2 (22 : Fin 32) 0x30, .sw a2 (23 : Fin 32) 0x2C, .sw a2 (24 : Fin 32) 0x28,
   .sw a2 (25 : Fin 32) 0x24, .alu .add (9 : Fin 32) x0 a1, .alu .add (24 : Fin 32) x0 a0]
def gsA2 : List BInstr :=
  [.lbu a0 a1 0x0, .aluImm .add (8 : Fin 32) x0 0xFFFFFFFF, .sw sp (8 : Fin 32) 0xD4, .sb sp a0 0xD8,
   .aluImm .add a0 sp 0x8C, .aluImm .add a1 sp 0xD4]

theorem gsA1_end : blockEnd p256FromSec1Code 0 gsA1 = some 0x32 := by decide
theorem gsA2_end : blockEnd p256FromSec1Code 0x32 gsA2 = some 0x42 := by decide

/-- The prologue's saves of `ra` and `s0..s9`, in order. -/
def gsSaves (M : Word → BitVec 8) (S : Word) (n : Machine) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (S + BitVec.ofNat 32 0x2cc) (reg n ra)) (S + BitVec.ofNat 32 0x2c8) (reg n (8 : Fin 32))) (S + BitVec.ofNat 32 0x2c4) (reg n (9 : Fin 32))) (S + BitVec.ofNat 32 0x2c0) (reg n (18 : Fin 32))) (S + BitVec.ofNat 32 0x2bc) (reg n (19 : Fin 32))) (S + BitVec.ofNat 32 0x2b8) (reg n (20 : Fin 32))) (S + BitVec.ofNat 32 0x2b4) (reg n (21 : Fin 32))) (S + BitVec.ofNat 32 0x2b0) (reg n (22 : Fin 32))) (S + BitVec.ofNat 32 0x2ac) (reg n (23 : Fin 32))) (S + BitVec.ofNat 32 0x2a8) (reg n (24 : Fin 32))) (S + BitVec.ofNat 32 0x2a4) (reg n (25 : Fin 32))

theorem gsSaves_out {M : Word → BitVec 8} {S : Word} {n : Machine} {x : Word}
    (h : Sep (S + BitVec.ofNat 32 0x2A4) 0x2C x 1) : gsSaves M S n x = M x := by
  have hs : ∀ c, 0x2A4 ≤ c → c + 4 ≤ 0x2D0 → Sep (S + BitVec.ofNat 32 c) 4 x 1 := fun c h1 h2 => by
    have := h.sub (c := c - 0x2A4) (l := 4) (by omega)
    rwa [add_ofNat_assoc, show 0x2A4 + (c - 0x2A4) = c by omega] at this
  unfold gsSaves
  rw [memStore32_get_sep (hs 0x2a4 (by decide) (by decide)), memStore32_get_sep (hs 0x2a8 (by decide) (by decide)),
    memStore32_get_sep (hs 0x2ac (by decide) (by decide)), memStore32_get_sep (hs 0x2b0 (by decide) (by decide)),
    memStore32_get_sep (hs 0x2b4 (by decide) (by decide)), memStore32_get_sep (hs 0x2b8 (by decide) (by decide)),
    memStore32_get_sep (hs 0x2bc (by decide) (by decide)), memStore32_get_sep (hs 0x2c0 (by decide) (by decide)),
    memStore32_get_sep (hs 0x2c4 (by decide) (by decide)), memStore32_get_sep (hs 0x2c8 (by decide) (by decide)),
    memStore32_get_sep (hs 0x2cc (by decide) (by decide))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The prologue**, from the entry to the call at 0x48: save `ra` and
`s0..s9`, open the frame at `S`, and store `Ok(b₀)` for the first input byte
`b₀` at `S + 0xD4`. -/
theorem gs_pro {M : Word → BitVec 8} {n : Machine} {S inp out : Word} (C : GsCode M) (F : Fr S 0x2D0)
    (s : St M GP n 0 (reg n)) (rsp : reg n sp = S + 0x2D0) (ra0 : reg n a0 = out) (ra1 : reg n a1 = inp)
    (sI : Sep (S + BitVec.ofNat 32 0x2A4) 0x2C inp 1) :
    ∃ n', Steps n n' ∧
      St (memStore8 (memStore32 (gsSaves M S n) (S + BitVec.ofNat 32 0xD4) 0xFFFFFFFF) (S + BitVec.ofNat 32 0xD8)
        (M inp)) GP n' 0x42 (reg n') ∧
      reg n' sp = S ∧ reg n' (9 : Fin 32) = inp ∧ reg n' (24 : Fin 32) = out ∧ reg n' (8 : Fin 32) = 0xFFFFFFFF ∧
      reg n' a0 = S + BitVec.ofNat 32 0x8C ∧ reg n' a1 = S + BitVec.ofNat 32 0xD4 ∧
      ∀ q, q.val ∈ [3, 4, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hA : aluEval .add (aluEval .add (S + 0x2D0) 0xFFFFFD30) 0x280 = S + BitVec.ofNat 32 0x280 := by
    show S + 0x2D0 + 0xFFFFFD30 + 0x280 = S + BitVec.ofNat 32 0x280
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have hS : aluEval .add (S + 0x2D0) 0xFFFFFD30 = S := by
    show S + 0x2D0 + 0xFFFFFD30 = S
    rw [BitVec.add_assoc]; exact BitVec.add_zero S
  have alB : ∀ (c : Nat) (k : Word), c + k.toNat + 4 ≤ 0x2D0 → (c + k.toNat) % 4 = 0 →
      (S + BitVec.ofNat 32 c + k).toNat % 4 = 0 := fun c k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  have sepB : ∀ (c : Nat) (k : Word), c + k.toNat + 4 ≤ 0x2D0 →
      Sep (S + BitVec.ofNat 32 c + k) 4 GP p256FromSec1Code.length := fun c k h1 => by
    rw [frame_lit k (by omega)]; exact F.sepHi (by omega) (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block gsA1 C.self gsA1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gsA1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp, hA]
    exact ⟨⟨alB 0x280 0x4C (by decide) (by decide), sepB 0x280 0x4C (by decide)⟩,
      ⟨alB 0x280 0x48 (by decide) (by decide), sepB 0x280 0x48 (by decide)⟩,
      ⟨alB 0x280 0x44 (by decide) (by decide), sepB 0x280 0x44 (by decide)⟩,
      ⟨alB 0x280 0x40 (by decide) (by decide), sepB 0x280 0x40 (by decide)⟩,
      ⟨alB 0x280 0x3C (by decide) (by decide), sepB 0x280 0x3C (by decide)⟩,
      ⟨alB 0x280 0x38 (by decide) (by decide), sepB 0x280 0x38 (by decide)⟩,
      ⟨alB 0x280 0x34 (by decide) (by decide), sepB 0x280 0x34 (by decide)⟩,
      ⟨alB 0x280 0x30 (by decide) (by decide), sepB 0x280 0x30 (by decide)⟩,
      ⟨alB 0x280 0x2C (by decide) (by decide), sepB 0x280 0x2C (by decide)⟩,
      ⟨alB 0x280 0x28 (by decide) (by decide), sepB 0x280 0x28 (by decide)⟩,
      ⟨alB 0x280 0x24 (by decide) (by decide), sepB 0x280 0x24 (by decide)⟩⟩)
  have m1 : n1.mem = gsSaves M S n := by
    rw [u1.mem]; simp only [runBlock, BInstr.run, gsA1]; simp +decide only [upd, ↓reduceIte]
    rw [rsp, hA]
    simp (disch := decide) only [frame_lit]
    rfl
  have r1 : ∀ q, reg n1 q = (runBlock gsA1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have sp1 : reg n1 sp = S := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, gsA1, upd, ↓reduceIte]; rw [rsp]; exact hS
  have e19 : reg n1 (9 : Fin 32) = inp := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, gsA1, upd, ↓reduceIte]; rw [ra1]; exact BitVec.zero_add _
  have e124 : reg n1 (24 : Fin 32) = out := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, gsA1, upd, ↓reduceIte]; rw [ra0]; exact BitVec.zero_add _
  have e1a1 : reg n1 a1 = inp := by rw [r1, runBlock_reg _ _ _ a1 hz (by decide)]; exact ra1
  have hb0 : gsSaves M S n inp = M inp := gsSaves_out sI
  have C1 : GsCode (gsSaves M S n) := C.hi fun x hx => gsSaves_out (F.hiOut (by decide) hx)
  have t1 : St (gsSaves M S n) GP n1 0x32 (reg n1) := ⟨u1.pc, m1, fun _ => rfl⟩
  obtain ⟨n2, c2, u2⟩ := t1.block gsA2 C1.self gsA2_end (by
      simp only [BlockOk, BInstr.ok, BInstr.run, gsA2]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
      rw [sp1]
      exact ⟨⟨by show (S + BitVec.ofNat 32 0xD4).toNat % 4 = 0; rw [F.at _ (by decide)]; omega,
        F.sepHi (by decide) (by decide) (by decide)⟩,
        F.sepHi (by decide) (by decide) (by decide)⟩)
  have r2 : ∀ q, reg n2 q = (runBlock gsA2 (gsSaves M S n, reg n1)).2 q := fun q => by rw [u2.regs]
  have m2 : n2.mem = memStore8 (memStore32 (gsSaves M S n) (S + BitVec.ofNat 32 0xD4) 0xFFFFFFFF)
      (S + BitVec.ofNat 32 0xD8) (M inp) := by
    rw [u2.mem]; simp only [runBlock, BInstr.run, gsA2]; simp +decide only [upd, ↓reduceIte]
    rw [sp1, e1a1, show inp + (0 : Word) = inp from BitVec.add_zero inp, hb0, ze_ex]; rfl
  refine ⟨n2, c1.trans c2, ⟨u2.pc, m2, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [r2, runBlock_reg _ _ _ sp t1.zero (by decide)]; exact sp1
  · rw [r2, runBlock_reg _ _ _ 9 t1.zero (by decide)]; exact e19
  · rw [r2, runBlock_reg _ _ _ 24 t1.zero (by decide)]; exact e124
  · rw [r2]; simp +decide only [runBlock, BInstr.run, gsA2, upd, ↓reduceIte]; (try rw [t1.zero]); try rfl
  · rw [r2]; simp +decide only [runBlock, BInstr.run, gsA2, upd, ↓reduceIte]; rw [sp1]; rfl
  · rw [r2]; simp +decide only [runBlock, BInstr.run, gsA2, upd, ↓reduceIte]; rw [sp1]; rfl
  · rw [r2, runBlock_reg _ _ _ q t1.zero (by simp only [gsA2]; revert hq; revert q; decide), r1,
      runBlock_reg _ _ _ q hz (by simp only [gsA1]; revert hq; revert q; decide)]

def gsE : List BInstr :=
  [.sw (24 : Fin 32) a0 0x0, .aluImm .add a0 sp 0x280, .lw ra a0 0x4C, .lw (8 : Fin 32) a0 0x48, .lw (9 : Fin 32) a0 0x44,
   .lw (18 : Fin 32) a0 0x40, .lw (19 : Fin 32) a0 0x3C, .lw (20 : Fin 32) a0 0x38, .lw (21 : Fin 32) a0 0x34,
   .lw (22 : Fin 32) a0 0x30, .lw (23 : Fin 32) a0 0x2C, .lw (24 : Fin 32) a0 0x28,
   .lw (25 : Fin 32) a0 0x24, .aluImm .add sp sp 0x2D0]

theorem gsE_end : blockEnd p256FromSec1Code 0x482 gsE = some 0x4B4 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The epilogue**, from 0x482: store the result word `v` at `out`,
restore `ra` and `s0..s9`, and return. -/
theorem gs_epi {M : Word → BitVec 8} {n : Machine} {S out v : Word} {w : Nat → Word} (C : GsCode M)
    (F : Fr S 0x2D0) (s : St M GP n 0x482 (reg n)) (rsp : reg n sp = S) (r24 : reg n (24 : Fin 32) = out)
    (ra0 : reg n a0 = v) (hoa : out.toNat % 4 = 0) (hoh : out.toNat + 4 ≤ 0x40000000)
    (hos : Sep out 4 (S + BitVec.ofNat 32 0x2A4) 0x2C)
    (hS : ∀ k, k < 11 → memLoad32 M (S + BitVec.ofNat 32 (0x2CC - 4 * k)) = w k) (hret : w 0 &&& ~~~1 = w 0) :
    ∃ n', Steps n n' ∧ n'.pc = w 0 ∧ reg n' sp = S + 0x2D0 ∧ (∀ k, k < 11 → reg n' (savedReg k) = w k) ∧
      n'.mem = memStore32 M out v ∧ ∀ q, q.val ∈ [3, 4, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hA : aluEval .add S 0x280 = S + BitVec.ofNat 32 0x280 := rfl
  have alB : ∀ (c : Nat) (k : Word), c + k.toNat + 4 ≤ 0x2D0 → (c + k.toNat) % 4 = 0 →
      (S + BitVec.ofNat 32 c + k).toNat % 4 = 0 := fun c k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  have o0 : out + (0 : Word) = out := BitVec.add_zero out
  have hoc : Sep out 4 GP p256FromSec1Code.length := by
    have : 0x40000000 ≤ GP.toNat := by decide
    exact sep_of_le (by omega) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block gsE C.self gsE_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gsE]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp, hA, r24, o0]
    exact ⟨⟨hoa, hoc⟩, alB 0x280 0x4C (by decide) (by decide), alB 0x280 0x48 (by decide) (by decide), alB 0x280 0x44 (by decide) (by decide), alB 0x280 0x40 (by decide) (by decide), alB 0x280 0x3C (by decide) (by decide), alB 0x280 0x38 (by decide) (by decide), alB 0x280 0x34 (by decide) (by decide), alB 0x280 0x30 (by decide) (by decide), alB 0x280 0x2C (by decide) (by decide), alB 0x280 0x28 (by decide) (by decide), alB 0x280 0x24 (by decide) (by decide)⟩)
  have m1 : (runBlock gsE (M, reg n)).1 = memStore32 M out v := by
    simp only [runBlock, BInstr.run, gsE]; rw [r24, o0, ra0]
  have ld9 : ∀ d, 0x2A4 ≤ d → d + 4 ≤ 0x2D0 → memLoad32 (memStore32 M (reg n (24 : Fin 32) + 0) (reg n a0))
      (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) := fun d h1 h2 => by
    rw [r24, o0]
    exact memLoad32_store32_sep (by
      have := hos.subR (c := d - 0x2A4) (l := 4) (by omega)
      rwa [add_ofNat_assoc, show 0x2A4 + (d - 0x2A4) = d by omega] at this)
  have C1 : GsCode (runBlock gsE (M, reg n)).1 := by
    rw [m1]; exact C.hi fun x hx => memStore32_get_sep (sep_of_le (by omega) (by have := x.isLt; omega))
  obtain ⟨n2, st2, pc2, mem2, regs2⟩ := u1.jalr C1.self gs_at_4b4
  refine ⟨n2, c1.trans (.single st2), ?_, ?_, ?_, by rw [mem2, m1], fun q hq => ?_⟩
  · rw [pc2]
    simp +decide only [runBlock, BInstr.run, gsE, upd, ↓reduceIte]
    rw [rsp, hA, frame_lit _ (by decide), ld9 _ (by decide) (by decide)]
    exact (congrArg (· &&& ~~~1) (BitVec.add_zero _)).trans (by rw [show (0x280 + (0x4C : Word).toNat) = 0x2CC - 4 * 0 from rfl, hS 0 (by decide)]; exact hret)
  · rw [regs2]; simp +decide only [runBlock, BInstr.run, gsE, upd, ↓reduceIte]; rw [rsp]
    show S + 0x2D0 = S + 0x2D0; rfl
  · intro k hk
    rw [regs2]
    match k, hk with
    | 0, _ =>
      simp +decide only [runBlock, BInstr.run, gsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 0 (by decide)
    | 1, _ =>
      simp +decide only [runBlock, BInstr.run, gsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 1 (by decide)
    | 2, _ =>
      simp +decide only [runBlock, BInstr.run, gsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 2 (by decide)
    | 3, _ =>
      simp +decide only [runBlock, BInstr.run, gsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 3 (by decide)
    | 4, _ =>
      simp +decide only [runBlock, BInstr.run, gsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 4 (by decide)
    | 5, _ =>
      simp +decide only [runBlock, BInstr.run, gsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 5 (by decide)
    | 6, _ =>
      simp +decide only [runBlock, BInstr.run, gsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 6 (by decide)
    | 7, _ =>
      simp +decide only [runBlock, BInstr.run, gsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 7 (by decide)
    | 8, _ =>
      simp +decide only [runBlock, BInstr.run, gsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 8 (by decide)
    | 9, _ =>
      simp +decide only [runBlock, BInstr.run, gsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 9 (by decide)
    | 10, _ =>
      simp +decide only [runBlock, BInstr.run, gsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 10 (by decide)
    | _ + 11, h => exact absurd h (by omega)
  · rw [regs2, runBlock_reg _ _ _ q hz (by simp only [gsE]; revert hq; revert q; decide)]

/-- The memory after the prologue: the saves, and `Ok(b₀)` at `S + 0xD4`. -/
def gsM2 (M : Word → BitVec 8) (S : Word) (n : Machine) (b : BitVec 8) : Word → BitVec 8 :=
  memStore8 (memStore32 (gsSaves M S n) (S + BitVec.ofNat 32 0xD4) 0xFFFFFFFF) (S + BitVec.ofNat 32 0xD8) b

def gsA3 : List BInstr := [.lw a0 sp 0x8C]
theorem gsA3_end : blockEnd p256FromSec1Code 0x4A gsA3 = some 0x4C := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **Reading the tag**, from the entry to 0x4C: the prologue, and
`Tag::from_u8` on the first input byte through `Result::and_then`, whose
`Result<Tag, Error>` is at `S + 0x8C`; `a0` holds its first word. -/
theorem gs_stA {M : Word → BitVec 8} {n : Machine} {S inp out : Word} (C : GsCode M) (F : Fr S 0x2D0)
    (s : St M GP n 0 (reg n)) (rsp : reg n sp = S + 0x2D0) (ra0 : reg n a0 = out) (ra1 : reg n a1 = inp)
    (sI : Sep (S + BitVec.ofNat 32 0x2A4) 0x2C inp 1) :
    ∃ n', Steps n n' ∧
      St (tagFromU8Mem (gsM2 M S n (M inp)) (S + BitVec.ofNat 32 0x8C) ((M inp).zeroExtend 32)) GP n' 0x4C (reg n') ∧
      reg n' a0 = memLoad32 (tagFromU8Mem (gsM2 M S n (M inp)) (S + BitVec.ofNat 32 0x8C) ((M inp).zeroExtend 32))
        (S + BitVec.ofNat 32 0x8C) ∧
      reg n' sp = S ∧ reg n' (9 : Fin 32) = inp ∧ reg n' (24 : Fin 32) = out ∧ reg n' (8 : Fin 32) = 0xFFFFFFFF ∧
      ∀ q, q.val ∈ [3, 4, 26, 27] → reg n' q = reg n q := by
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨n1, c1, u1, sp1, e19, e124, e18, ea0, ea1, k1⟩ := gs_pro C F s rsp ra0 ra1 sI
  replace u1 : St (gsM2 M S n (M inp)) GP n1 0x42 (reg n1) := u1
  have hfr : ∀ x : Word, 0x40000000 ≤ x.toNat → gsM2 M S n (M inp) x = M x := fun x hx => by
    unfold gsM2
    rw [dq_st8 (F.hiOut (by decide) hx), memStore32_get_sep (F.hiOut (by decide) hx),
      gsSaves_out (F.hiOut (by decide) hx)]
  have C1 : GsCode (gsM2 M S n (M inp)) := C.hi hfr
  have hok : memLoad32 (gsM2 M S n (M inp)) (S + BitVec.ofNat 32 0xD4) = 0xFFFFFFFF := by
    unfold gsM2
    rw [memLoad32_store8_sep (sepS S (.inr (by decide)) (by decide) (by decide)), memLoad32_store32_same]
  have hb : gsM2 M S n (M inp) (S + BitVec.ofNat 32 0xD4 + 4) = M inp := by
    unfold gsM2
    rw [show S + BitVec.ofNat 32 0xD4 + 4 = S + BitVec.ofNat 32 0xD8 by rw [BitVec.add_assoc]; rfl]
    exact memStore8_same _ _ _
  obtain ⟨n2, c2, u2, m2, sp2, k2⟩ := c_tat (out := S + BitVec.ofNat 32 0x8C) (rp := S + BitVec.ofNat 32 0xD4)
    (co := 0x8C) (cr := 0xD4) u1 C1.self C1.K.K F gs_at_42 gs_at_46 (by decide) (by decide) sp1 ea0 ea1
    (by decide) (by decide) rfl rfl (by decide) (by decide) (.inl (by decide)) hok
  rw [hb] at m2
  have h2 : ∀ x : Word, 0x40000000 ≤ x.toNat → n2.mem x = gsM2 M S n (M inp) x := fun x hx => by
    rw [m2]; unfold tagFromU8Mem; split
    · rw [memStore32_get_sep (F.hiOut (by decide) hx), dq_st8 (by
        rw [show S + BitVec.ofNat 32 0x8C + 4 = S + BitVec.ofNat 32 0x90 by rw [BitVec.add_assoc]; rfl]
        exact F.hiOut (by decide) hx)]
    · rw [memStore32_get_sep (F.hiOut (by decide) hx)]
  have C2 := C1.hi h2
  obtain ⟨n3, c3, u3⟩ := (⟨u2.pc, m2, fun _ => rfl⟩ : St (tagFromU8Mem (gsM2 M S n (M inp)) (S + BitVec.ofNat 32 0x8C)
      ((M inp).zeroExtend 32)) GP n2 0x4A (reg n2)).block gsA3 (by rw [← m2]; exact C2.self) gsA3_end (by
    simp only [BlockOk, BInstr.ok, gsA3]; simp +decide only [and_true]
    rw [sp2]; show (S + BitVec.ofNat 32 0x8C).toNat % 4 = 0; rw [F.at _ (by decide)]; omega)
  have r3 : ∀ q, q ≠ a0 → reg n3 q = reg n2 q := fun q hq => by
    rw [u3.regs]; simp only [runBlock, BInstr.run, gsA3]; exact updz u2.zero hq
  refine ⟨n3, c1.trans (c2.trans c3), ⟨u3.pc, u3.mem, fun _ => rfl⟩, ?_, by rw [r3 sp (by decide)]; exact sp2,
    by rw [r3 9 (by decide), k2 9 (by decide)]; exact e19, by rw [r3 24 (by decide), k2 24 (by decide)]; exact e124,
    by rw [r3 8 (by decide), k2 8 (by decide)]; exact e18, fun q hq => ?_⟩
  · rw [u3.regs]; simp +decide only [runBlock, BInstr.run, gsA3, upd, ↓reduceIte]; rw [sp2]; rfl
  · rw [r3 q (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide), k1 q hq]

/-- What a return from `from_sec1_bytes` keeps: the return address, `sp`,
the saved and untouched registers, and memory outside the frame and the
68-byte result at `out`. -/
def GsRet (M : Word → BitVec 8) (n : Machine) (S out : Word) (n' : Machine) : Prop :=
  n'.pc = reg n ra ∧ reg n' sp = S + 0x2D0 ∧ (∀ k, k < 11 → reg n' (savedReg k) = reg n (savedReg k)) ∧
    (∀ q : Fin 32, q.val ∈ [3, 4, 26, 27] → reg n' q = reg n q) ∧
    ∀ x, Sep (S + 0xFFFFFE60) 0x470 x 1 → Sep out 0x48 x 1 → n'.mem x = M x

def gsErr : List BInstr := [.aluImm .add a0 x0 0x1]
theorem gsErr_end : blockEnd p256FromSec1Code 0x480 gsErr = some 0x482 := by decide

theorem gsSaves_read {M : Word → BitVec 8} {S : Word} {n : Machine} :
    ∀ k, k < 11 → memLoad32 (gsSaves M S n) (S + BitVec.ofNat 32 (0x2CC - 4 * k)) = reg n (savedReg k) := by
  intro k hk
  match k, hk with
  | 0, _ => unfold gsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 1, _ => unfold gsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 2, _ => unfold gsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 3, _ => unfold gsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 4, _ => unfold gsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 5, _ => unfold gsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 6, _ => unfold gsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 7, _ => unfold gsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 8, _ => unfold gsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 9, _ => unfold gsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 10, _ => unfold gsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | _ + 11, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **Returning an error**, from 0x480: the result word 1 at `out`. -/
theorem gs_err {M Mx : Word → BitVec 8} {n nx : Machine} {S out : Word} (C : GsCode Mx) (F : Fr S 0x2D0)
    (s : St Mx GP nx 0x480 (reg nx)) (rsp : reg nx sp = S) (r24 : reg nx (24 : Fin 32) = out)
    (hoa : out.toNat % 4 = 0) (hO : out.toNat + 0x48 ≤ 0x40000000) (sO : Sep out 0x48 (S + 0xFFFFFE60) 0x470)
    (hS : ∀ k, k < 11 → memLoad32 Mx (S + BitVec.ofNat 32 (0x2CC - 4 * k)) = reg n (savedReg k))
    (hret : reg n ra &&& ~~~1 = reg n ra) (k3 : ∀ q : Fin 32, q.val ∈ [3, 4, 26, 27] → reg nx q = reg n q)
    (hM : ∀ x, Sep (S + 0xFFFFFE60) 0x470 x 1 → Mx x = M x) :
    ∃ n', Steps nx n' ∧ GsRet M n S out n' ∧ memLoad32 n'.mem out = 1 := by
  obtain ⟨n1, c1, u1⟩ := s.block gsErr C.self gsErr_end ⟨trivial, trivial⟩
  have r1 : ∀ q, q ≠ a0 → reg n1 q = reg nx q := fun q hq => by
    rw [u1.regs]; simp only [runBlock, BInstr.run, gsErr]; exact updz s.zero hq
  have hos : Sep out 4 (S + BitVec.ofNat 32 0x2A4) 0x2C := by
    have := (sO.sub (c := 0) (l := 4) (by decide)).subR (c := 0x1A0 + 0x2A4) (l := 0x2C) (by decide)
    rwa [add_ofNat_zero, BitVec.add_assoc,
      show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x2A4) = BitVec.ofNat 32 0x2A4 from rfl] at this
  obtain ⟨n2, c2, pc2, sp2, sv2, m2, k2⟩ := gs_epi (v := 1) C F ⟨u1.pc, u1.mem, fun _ => rfl⟩
    (by rw [r1 sp (by decide)]; exact rsp) (by rw [r1 24 (by decide)]; exact r24)
    (by rw [u1.regs]; simp +decide only [runBlock, BInstr.run, gsErr, upd, ↓reduceIte]; rw [s.zero]; rfl)
    hoa (by omega) hos hS hret
  refine ⟨n2, c1.trans c2, ⟨pc2, sp2, sv2, fun q hq => ?_, fun x hx ho => ?_⟩, by rw [m2]; exact memLoad32_store32_same _ _ _⟩
  · rw [k2 q hq, r1 q (by revert hq; revert q; decide), k3 q hq]
  · rw [m2, memStore32_get_sep ((ho.sub (c := 0) (l := 4) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h)]
    exact hM x hx

/-- The memory after `and_then(Tag::from_u8)`. -/
def gsM3 (M : Word → BitVec 8) (S : Word) (n : Machine) (b : BitVec 8) : Word → BitVec 8 :=
  tagFromU8Mem (gsM2 M S n b) (S + BitVec.ofNat 32 0x8C) (b.zeroExtend 32)

theorem gsM3_keep {M : Word → BitVec 8} {S : Word} {n : Machine} {b : BitVec 8} {x : Word}
    (h : Sep (S + BitVec.ofNat 32 0x8C) 0x50 x 1) : gsM3 M S n b x = gsSaves M S n x := by
  have s1 : Sep (S + BitVec.ofNat 32 0x8C) 4 x 1 := by
    have := h.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have s2 : Sep (S + BitVec.ofNat 32 0x8C + 4) 1 x 1 := by
    have := h.sub (c := 4) (l := 1) (by decide); rwa [show (4 : Word) = BitVec.ofNat 32 4 from rfl]
  have s3 : Sep (S + BitVec.ofNat 32 0xD4) 4 x 1 := by
    have := h.sub (c := 0x48) (l := 4) (by decide); rwa [add_ofNat_assoc] at this
  have s4 : Sep (S + BitVec.ofNat 32 0xD8) 1 x 1 := by
    have := h.sub (c := 0x4C) (l := 1) (by decide); rwa [add_ofNat_assoc] at this
  unfold gsM3 tagFromU8Mem gsM2; split
  · rw [memStore32_get_sep s1, dq_st8 s2, dq_st8 s4, memStore32_get_sep s3]
  · rw [memStore32_get_sep s1, dq_st8 s4, memStore32_get_sep s3]

theorem gsM3_word {M : Word → BitVec 8} {S : Word} {n : Machine} {b : BitVec 8} :
    memLoad32 (gsM3 M S n b) (S + BitVec.ofNat 32 0x8C) = if Sec1TagOk b then 0xFFFFFFFF else 3 := by
  unfold gsM3 tagFromU8Mem
  by_cases h : Sec1TagOk b
  · rw [ite_eq_left (show (b.zeroExtend 32 : Word).toNat ≤ 5 ∧ (b.zeroExtend 32 : Word).toNat ≠ 1 by
      rw [zext8_toNat]; exact h), ite_eq_left h, memLoad32_store32_same]
  · rw [ite_eq_right (show ¬((b.zeroExtend 32 : Word).toNat ≤ 5 ∧ (b.zeroExtend 32 : Word).toNat ≠ 1) by
      rw [zext8_toNat]; exact h), ite_eq_right h, memLoad32_store32_same]

theorem gsM3_tag {M : Word → BitVec 8} {S : Word} {n : Machine} {b : BitVec 8} (h : Sec1TagOk b) :
    gsM3 M S n b (S + BitVec.ofNat 32 0x90) = b := by
  unfold gsM3 tagFromU8Mem
  rw [ite_eq_left (show (b.zeroExtend 32 : Word).toNat ≤ 5 ∧ (b.zeroExtend 32 : Word).toNat ≠ 1 by
      rw [zext8_toNat]; exact h), memStore32_get_sep (sepS S (.inl (by decide)) (by decide) (by decide)),
    show S + BitVec.ofNat 32 0x90 = S + BitVec.ofNat 32 0x8C + 4 by rw [BitVec.add_assoc]; rfl, memStore8_same, ze_ex]

theorem gsM3_saves {M : Word → BitVec 8} {S : Word} {n : Machine} {b : BitVec 8} :
    ∀ k, k < 11 → memLoad32 (gsM3 M S n b) (S + BitVec.ofNat 32 (0x2CC - 4 * k)) = reg n (savedReg k) := fun k hk => by
  rw [← gsSaves_read k hk]
  exact memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]; exact gsM3_keep (sepS S (.inl (by omega)) (by decide) (by omega))

theorem gsM3_out {M : Word → BitVec 8} {S : Word} {n : Machine} {b : BitVec 8} {x : Word}
    (h : Sep (S + BitVec.ofNat 32 0x8C) 0x50 x 1) (h' : Sep (S + BitVec.ofNat 32 0x2A4) 0x2C x 1) :
    gsM3 M S n b x = M x := by rw [gsM3_keep h, gsSaves_out h']

def gsB1 : List BInstr := [.lbu a0 sp 0x90, .aluImm .add a1 x0 0x20]
def gsB2 : List BInstr := [.aluImm .add a0 a0 0xFFFFFFBF]
def gsC1 : List BInstr := [.aluImm .add a1 sp 0x91, .aluImm .add a0 sp 0x160, .aluImm .add a2 x0 0x2F]
theorem gsB1_end : blockEnd p256FromSec1Code 0x64 gsB1 = some 0x6C := by decide
theorem gsB2_end : blockEnd p256FromSec1Code 0x74 gsB2 = some 0x78 := by decide
theorem gsC1_end : blockEnd p256FromSec1Code 0x50 gsC1 = some 0x5A := by decide

theorem tml4_256 (t : BitVec 8) : tagMsgLen (t.zeroExtend 32) 0x20 + 0xFFFFFFBF = 0 ↔ t = 4 := by
  revert t; decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The tag and length checks**, from the entry: a first byte other than 4
returns an error, through `Tag::from_u8`'s error or `message_len`'s; tag 4
reaches 0x7C. -/
theorem gs_front {M : Word → BitVec 8} {n : Machine} {S inp out : Word} (C : GsCode M) (F : Fr S 0x2D0)
    (s : St M GP n 0 (reg n)) (rsp : reg n sp = S + 0x2D0) (ra0 : reg n a0 = out) (ra1 : reg n a1 = inp)
    (sI : Sep inp 0x41 (S + 0xFFFFFE60) 0x470) (hoa : out.toNat % 4 = 0) (hO : out.toNat + 0x48 ≤ 0x40000000)
    (sO : Sep out 0x48 (S + 0xFFFFFE60) 0x470) (hret : reg n ra &&& ~~~1 = reg n ra) :
    (M inp ≠ 4 → ∃ n', Steps n n' ∧ GsRet M n S out n' ∧ memLoad32 n'.mem out = 1) ∧
    (M inp = 4 → ∃ n', Steps n n' ∧ St (gsM3 M S n 4) GP n' 0x7C (reg n') ∧ reg n' sp = S ∧
      reg n' (9 : Fin 32) = inp ∧ reg n' (24 : Fin 32) = out ∧
      ∀ q : Fin 32, q.val ∈ [3, 4, 26, 27] → reg n' q = reg n q) := by
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have sIs : Sep (S + BitVec.ofNat 32 0x2A4) 0x2C inp 1 :=
    (fr_inFrame (N := 0x2D0) (by decide) ((sI.sub (c := 0) (l := 1) (by decide)) |> fun h => by
      rw [add_ofNat_zero] at h; exact h.symm))
  obtain ⟨n1, c1, u1, a1v, sp1, e19, e124, e18, k1⟩ := gs_stA C F s rsp ra0 ra1 sIs
  replace u1 : St (gsM3 M S n (M inp)) GP n1 0x4C (reg n1) := u1
  change reg n1 a0 = memLoad32 (gsM3 M S n (M inp)) (S + BitVec.ofNat 32 0x8C) at a1v
  rw [gsM3_word] at a1v
  have hfr : ∀ x : Word, 0x40000000 ≤ x.toNat → gsM3 M S n (M inp) x = M x := fun x hx =>
    gsM3_out (F.hiOut (by decide) hx) (F.hiOut (by decide) hx)
  have C1 : GsCode (gsM3 M S n (M inp)) := C.hi hfr
  have hM3 : ∀ x, Sep (S + 0xFFFFFE60) 0x470 x 1 → gsM3 M S n (M inp) x = M x := fun x hx =>
    gsM3_out (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx)
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · by_cases hv : Sec1TagOk (M inp)
    · -- a valid tag other than 4: `message_len` isn't 97
      rw [ite_eq_left hv] at a1v
      obtain ⟨n2, d2, u2⟩ := u1.taken C1.self 0x64 gs_at_4c (by decide) (by
        show branchTaken .beq (reg n1 a0) (reg n1 (8 : Fin 32)) = true; rw [a1v, e18]; decide)
      obtain ⟨n3, c3, u3⟩ := u2.block gsB1 C1.self gsB1_end ⟨trivial, trivial, trivial⟩
      have r3 : ∀ q, reg n3 q = (runBlock gsB1 (gsM3 M S n (M inp), reg n1)).2 q := fun q => by rw [u3.regs]
      obtain ⟨n4, c4, u4, a4, k4⟩ := c_tml (t := (M inp).zeroExtend 32) (fe := 0x20)
        (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St (gsM3 M S n (M inp)) GP n3 0x6C (reg n3)) C1.self C1.K.K gs_at_6c gs_at_70
        (by decide) (by decide)
        (by rw [r3]; simp +decide only [runBlock, BInstr.run, gsB1, upd, ↓reduceIte]; rw [sp1]
            show ((gsM3 M S n (M inp)) (S + BitVec.ofNat 32 0x90)).zeroExtend 32 = _; rw [gsM3_tag hv])
        (by rw [r3]; simp +decide only [runBlock, BInstr.run, gsB1, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
      obtain ⟨n5, c5, u5⟩ := u4.block gsB2 C1.self gsB2_end ⟨trivial, trivial⟩
      have r5 : ∀ q, q ≠ a0 → reg n5 q = reg n4 q := fun q hq => by
        rw [u5.regs]; simp only [runBlock, BInstr.run, gsB2]; exact updz u4.zero hq
      obtain ⟨n6, d6, u6⟩ := (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St (gsM3 M S n (M inp)) GP n5 0x78 (reg n5)).taken
        C1.self 0x480 gs_at_78 (by decide) (by
          show branchTaken .bne (reg n5 a0) 0 = true
          rw [u5.regs]; simp +decide only [runBlock, BInstr.run, gsB2, upd, ↓reduceIte]; rw [a4]
          have : aluEval .add (tagMsgLen ((M inp).zeroExtend 32) 0x20) 0xFFFFFFBF ≠ 0 :=
            fun h => hb ((tml4_256 (M inp)).1 h)
          revert this; generalize aluEval .add (tagMsgLen ((M inp).zeroExtend 32) 0x20) 0xFFFFFFBF = z; intro h
          simp only [branchTaken, bne_iff_ne, ne_eq]; exact h)
      have kk : ∀ q, q.val ∈ [3, 4, 26, 27, 2, 24] → reg n5 q = reg n1 q := fun q hq => by
        rw [r5 q (by revert hq; revert q; decide), k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide), r3,
          runBlock_reg _ _ _ q u2.zero (by simp only [gsB1]; revert hq; revert q; decide)]
      obtain ⟨n7, c7, R7, w7⟩ := gs_err (M := M) (n := n) C1 F u6.self (by rw [u6.regs, kk sp (by decide)]; exact sp1)
        (by rw [u6.regs, kk 24 (by decide)]; exact e124) hoa hO sO gsM3_saves hret
        (fun q hq => by rw [u6.regs, kk q (by revert hq; revert q; decide), k1 q hq]) hM3
      exact ⟨n7, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (.cons d6 c7))))), R7, w7⟩
    · -- not a tag: `Tag::from_u8` fails
      rw [ite_eq_right hv] at a1v
      obtain ⟨n2, d2, u2⟩ := u1.notTaken C1.self 0x50 gs_at_4c (by decide) (by
        show branchTaken .beq (reg n1 a0) (reg n1 (8 : Fin 32)) = false; rw [a1v, e18]; decide)
      obtain ⟨n3, c3, u3⟩ := u2.block gsC1 C1.self gsC1_end ⟨trivial, trivial, trivial, trivial⟩
      have r3 : ∀ q, reg n3 q = (runBlock gsC1 (gsM3 M S n (M inp), reg n1)).2 q := fun q => by rw [u3.regs]
      obtain ⟨fA, fW, hFC⟩ := F.mc
      obtain ⟨n4, c4, u4, fr4, k4⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x160) (src := S + BitVec.ofNat 32 0x91)
        (S := S) (N := 0x2F) (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St (gsM3 M S n (M inp)) GP n3 0x5A (reg n3))
        C1.self C1.K.K gs_at_5a gs_at_5e (by decide) (by decide)
        (by rw [r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp1)
        (by rw [r3]; simp +decide only [runBlock, BInstr.run, gsC1, upd, ↓reduceIte]; rw [sp1]; rfl)
        (by rw [r3]; simp +decide only [runBlock, BInstr.run, gsC1, upd, ↓reduceIte]; rw [sp1]; rfl)
        (by rw [r3]; simp +decide only [runBlock, BInstr.run, gsC1, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
        ⟨C1.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
          sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
          by rw [F.at _ (by decide)]; omega⟩
      have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
      have fr4' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x160) 0x2F x 1 →
          n4.mem x = gsM3 M S n (M inp) x := fun x a b => by rw [fr4 x a, copyBytes_sep b (Nat.le_refl _)]
      have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
        sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
      have C4 := C1.hi fun x hx => fr4' x (lo16 x hx) (F.hiOut (by decide) hx)
      obtain ⟨n5, d5, u5⟩ := u4.jump C4.self gs_at_62 (off' := 0x480) (by decide) (by rw [u4.pc]; decide)
      have kk : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 24, 26, 27] → reg n4 q = reg n1 q := fun q hq => by
        rw [k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r3,
          runBlock_reg _ _ _ q u2.zero (by simp only [gsC1]; revert hq; revert q; decide)]
      have below16 : ∀ {x : Word}, Sep (S + 0xFFFFFE60) 0x470 x 1 → Sep (S + 0xFFFFFFF0) 16 x 1 := fun {x} hx => by
        have := hx.sub (c := 0x190) (l := 16) (by decide)
        rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x190 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
      obtain ⟨n7, c7, R7, w7⟩ := gs_err (M := M) (n := n) C4 F u5.self (by rw [u5.regs, kk sp (by decide)]; exact sp1)
        (by rw [u5.regs, kk 24 (by decide)]; exact e124) hoa hO sO
        (fun k hk => by
          rw [← gsM3_saves (M := M) (S := S) (n := n) (b := M inp) k hk]
          exact memLoad32_congr fun j hj => by
            rw [add_ofNat_assoc]
            exact fr4' _ (F.lowB hb16 (by decide) (by omega)) (sepS S (.inl (by omega)) (by decide) (by omega)))
        hret (fun q hq => by rw [u5.regs, kk q (by revert hq; revert q; decide), k1 q hq])
        (fun x hx => by rw [fr4' x (below16 hx) (fr_inFrame (by decide) hx), hM3 x hx])
      exact ⟨n7, c1.trans (.cons d2 (c3.trans (c4.trans (.cons d5 c7)))), R7, w7⟩
  · -- tag 4
    have hv : Sec1TagOk (M inp) := by rw [hb]; decide
    rw [ite_eq_left hv] at a1v
    obtain ⟨n2, d2, u2⟩ := u1.taken C1.self 0x64 gs_at_4c (by decide) (by
      show branchTaken .beq (reg n1 a0) (reg n1 (8 : Fin 32)) = true; rw [a1v, e18]; decide)
    obtain ⟨n3, c3, u3⟩ := u2.block gsB1 C1.self gsB1_end ⟨trivial, trivial, trivial⟩
    have r3 : ∀ q, reg n3 q = (runBlock gsB1 (gsM3 M S n (M inp), reg n1)).2 q := fun q => by rw [u3.regs]
    obtain ⟨n4, c4, u4, a4, k4⟩ := c_tml (t := (M inp).zeroExtend 32) (fe := 0x20)
      (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St (gsM3 M S n (M inp)) GP n3 0x6C (reg n3)) C1.self C1.K.K gs_at_6c gs_at_70
      (by decide) (by decide)
      (by rw [r3]; simp +decide only [runBlock, BInstr.run, gsB1, upd, ↓reduceIte]; rw [sp1]
          show ((gsM3 M S n (M inp)) (S + BitVec.ofNat 32 0x90)).zeroExtend 32 = _; rw [gsM3_tag hv])
      (by rw [r3]; simp +decide only [runBlock, BInstr.run, gsB1, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    obtain ⟨n5, c5, u5⟩ := u4.block gsB2 C1.self gsB2_end ⟨trivial, trivial⟩
    have r5 : ∀ q, q ≠ a0 → reg n5 q = reg n4 q := fun q hq => by
      rw [u5.regs]; simp only [runBlock, BInstr.run, gsB2]; exact updz u4.zero hq
    obtain ⟨n6, d6, u6⟩ := (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St (gsM3 M S n (M inp)) GP n5 0x78 (reg n5)).notTaken
      C1.self 0x7C gs_at_78 (by decide) (by
        show branchTaken .bne (reg n5 a0) 0 = false
        rw [u5.regs]; simp +decide only [runBlock, BInstr.run, gsB2, upd, ↓reduceIte]; rw [a4]
        rw [show aluEval .add (tagMsgLen ((M inp).zeroExtend 32) 0x20) 0xFFFFFFBF = 0 from (tml4_256 (M inp)).2 hb]
        decide)
    have kk : ∀ q, q.val ∈ [3, 4, 26, 27, 2, 9, 24] → reg n5 q = reg n1 q := fun q hq => by
      rw [r5 q (by revert hq; revert q; decide), k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide), r3,
        runBlock_reg _ _ _ q u2.zero (by simp only [gsB1]; revert hq; revert q; decide)]
    rw [hb] at u6
    exact ⟨n6, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (.single d6))))), u6.self,
      by rw [u6.regs, kk sp (by decide)]; exact sp1, by rw [u6.regs, kk 9 (by decide)]; exact e19,
      by rw [u6.regs, kk 24 (by decide)]; exact e124,
      fun q hq => by rw [u6.regs, kk q (by revert hq; revert q; decide), k1 q hq]⟩

theorem xl_or (x y : Word) (k : Nat) : (x ||| y).extractLsb' k 8 = x.extractLsb' k 8 ||| y.extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or]
  cases decide (i < 8) <;> simp

theorem lane_same (b : BitVec 8) (s : Nat) (hs : s + 8 ≤ 32) :
    ((b.zeroExtend 32 : Word) <<< s).extractLsb' s 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_extractLsb', decide_eq_true hi, Bool.true_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    decide_eq_true (show s + i < 32 by omega), decide_eq_false (show ¬ s + i < s by omega), show s + i - s = i by omega,
    decide_eq_true (show i < 32 by omega)]
  simp

theorem lane_diff (b : BitVec 8) (s k : Nat) (h : s + 8 ≤ k ∨ k + 8 ≤ s) :
    ((b.zeroExtend 32 : Word) <<< s).extractLsb' k 8 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h2 : k + i < s
  · simp [h2]
  · rw [BitVec.getLsbD_of_ge b (k + i - s) (by omega)]; simp

theorem lane0_diff (b : BitVec 8) (k : Nat) (h : 8 ≤ k) : (b.zeroExtend 32 : Word).extractLsb' k 8 = 0 := by
  have := lane_diff b 0 k (.inl h); rwa [BitVec.shiftLeft_zero] at this

theorem or8_0 (x : BitVec 8) : x ||| 0 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp

theorem zor8 (x : BitVec 8) : 0 ||| x = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp

theorem sh8 : (8 : Word).toNat % 32 = 8 := rfl

/-- The lanes `lbu`, `slli`, and `or` assemble. -/
theorem lanes :
    (∀ b : BitVec 8, ((b.zeroExtend 32 : Word) <<< 8).extractLsb' 8 8 = b) ∧
    (∀ b : BitVec 8, ((b.zeroExtend 32 : Word) <<< 16).extractLsb' 16 8 = b) ∧
    (∀ b : BitVec 8, ((b.zeroExtend 32 : Word) <<< 24).extractLsb' 24 8 = b) ∧
    (∀ b : BitVec 8, ((b.zeroExtend 32 : Word) <<< 8).extractLsb' 0 8 = 0) ∧
    (∀ b : BitVec 8, ((b.zeroExtend 32 : Word) <<< 8).extractLsb' 16 8 = 0) ∧
    (∀ b : BitVec 8, ((b.zeroExtend 32 : Word) <<< 8).extractLsb' 24 8 = 0) ∧
    (∀ b : BitVec 8, ((b.zeroExtend 32 : Word) <<< 16).extractLsb' 0 8 = 0) ∧
    (∀ b : BitVec 8, ((b.zeroExtend 32 : Word) <<< 16).extractLsb' 8 8 = 0) ∧
    (∀ b : BitVec 8, ((b.zeroExtend 32 : Word) <<< 16).extractLsb' 24 8 = 0) ∧
    (∀ b : BitVec 8, ((b.zeroExtend 32 : Word) <<< 24).extractLsb' 0 8 = 0) ∧
    (∀ b : BitVec 8, ((b.zeroExtend 32 : Word) <<< 24).extractLsb' 8 8 = 0) ∧
    (∀ b : BitVec 8, ((b.zeroExtend 32 : Word) <<< 24).extractLsb' 16 8 = 0) ∧
    (∀ b : BitVec 8, (b.zeroExtend 32 : Word).extractLsb' 8 8 = 0) ∧
    (∀ b : BitVec 8, (b.zeroExtend 32 : Word).extractLsb' 16 8 = 0) ∧
    (∀ b : BitVec 8, (b.zeroExtend 32 : Word).extractLsb' 24 8 = 0) :=
  ⟨fun b => lane_same b 8 (by decide), fun b => lane_same b 16 (by decide), fun b => lane_same b 24 (by decide),
   fun b => lane_diff b 8 0 (by decide), fun b => lane_diff b 8 16 (by decide), fun b => lane_diff b 8 24 (by decide),
   fun b => lane_diff b 16 0 (by decide), fun b => lane_diff b 16 8 (by decide), fun b => lane_diff b 16 24 (by decide),
   fun b => lane_diff b 24 0 (by decide), fun b => lane_diff b 24 8 (by decide), fun b => lane_diff b 24 16 (by decide),
   fun b => lane0_diff b 8 (by decide), fun b => lane0_diff b 16 (by decide), fun b => lane0_diff b 24 (by decide)⟩

/-- The delay loop at 0x86: count `a0` down to 0. -/
theorem gs_delay {M : Word → BitVec 8} (C : GsCode M) :
    ∀ k : Nat, ∀ {n : Machine}, 1 ≤ k → k < 2 ^ 32 → St M GP n 0x86 (reg n) → reg n a0 = BitVec.ofNat 32 k →
      ∃ n', Steps n n' ∧ St M GP n' 0x8A (reg n') ∧ ∀ q, q ≠ a0 → reg n' q = reg n q
  | 0, _, h, _, _, _ => absurd h (by decide)
  | k + 1, n, _, hk, s, ha => by
    obtain ⟨n1, d1, u1⟩ := s.aluImm C.self gs_at_86 (off' := 0x88) (by decide)
    have e1 : aluEval .add (reg n a0) 0xFFFFFFFF = BitVec.ofNat 32 k := by
      rw [ha]; apply BitVec.eq_of_toNat_eq
      show (BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF).toNat = _
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 0xFFFFFFFF from rfl]
      omega
    have k1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q hq => by rw [u1.regs]; exact updz s.zero hq
    by_cases h0 : k = 0
    · subst h0
      obtain ⟨n2, d2, u2⟩ := u1.self.notTaken C.self 0x8A gs_at_88 (by decide) (by
        show branchTaken .bne (reg n1 a0) 0 = false
        rw [u1.regs]; simp +decide only [upd, ↓reduceIte]; rw [e1]; decide)
      exact ⟨n2, .cons d1 (.single d2), u2.self, fun q hq => by rw [u2.regs, k1 q hq]⟩
    · obtain ⟨n2, d2, u2⟩ := u1.self.taken C.self 0x86 gs_at_88 (by decide) (by
        show branchTaken .bne (reg n1 a0) 0 = true
        rw [u1.regs]; simp +decide only [upd, ↓reduceIte]; rw [e1]
        simp only [branchTaken, bne_iff_ne, ne_eq]
        intro h; apply h0
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl, Nat.mod_eq_of_lt (by omega)] at this
        exact this)
      obtain ⟨n3, c3, u3, k3⟩ := gs_delay C k (by omega) (by omega) u2.self (by
        rw [u2.regs, u1.regs]; simp +decide only [upd, ↓reduceIte]; exact e1)
      exact ⟨n3, .cons d1 (.cons d2 c3), u3, fun q hq => by rw [k3 q hq, u2.regs, k1 q hq]⟩

theorem gst32 (M : Word → BitVec 8) (a v : Word) :
    ∀ j, j < 4 → memStore32 M a v (a + BitVec.ofNat 32 j) = v.extractLsb' (8 * j) 8 := by
  have ne : ∀ {j k : Nat}, j ≠ k → j < 4 → k < 4 → a + BitVec.ofNat 32 j ≠ a + BitVec.ofNat 32 k :=
    fun h hj hk => add_ofNat_ne a (by omega) (by omega) h
  intro j hj
  unfold memStore32
  match j, hj with
  | 0, _ =>
    rw [add_ofNat_zero]
    have h : ∀ k, 0 < k → k < 4 → a ≠ a + BitVec.ofNat 32 k := fun k h1 h2 => by
      have := ne (j := 0) (k := k) (by omega) (by omega) h2; rwa [add_ofNat_zero] at this
    rw [memStore8_ne (a := a + 3) (x := a) (h 3 (by decide) (by decide)),
      memStore8_ne (a := a + 2) (x := a) (h 2 (by decide) (by decide)),
      memStore8_ne (a := a + 1) (x := a) (h 1 (by decide) (by decide)), memStore8_same]
  | 1, _ =>
    rw [memStore8_ne (a := a + 3) (ne (j := 1) (k := 3) (by decide) (by decide) (by decide)),
      memStore8_ne (a := a + 2) (ne (j := 1) (k := 2) (by decide) (by decide) (by decide))]
    exact memStore8_same _ _ _
  | 2, _ =>
    rw [memStore8_ne (a := a + 3) (ne (j := 2) (k := 3) (by decide) (by decide) (by decide))]
    exact memStore8_same _ _ _
  | 3, _ => exact memStore8_same _ _ _

/-- Byte `j` of a word assembled from four bytes, low half first. -/
theorem wA_byte (b0 b1 b2 b3 : BitVec 8) :
    (aluEval .or (aluEval .or (aluEval .sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32))
      (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18))).extractLsb' 0 8 = b0 ∧
    (aluEval .or (aluEval .or (aluEval .sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32))
      (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18))).extractLsb' 8 8 = b1 ∧
    (aluEval .or (aluEval .or (aluEval .sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32))
      (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18))).extractLsb' 16 8 = b2 ∧
    (aluEval .or (aluEval .or (aluEval .sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32))
      (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18))).extractLsb' 24 8 = b3 := by
  obtain ⟨l8, l16, l24, d80, d816, d824, d160, d168, d1624, d240, d248, d2416, z8, z16, z24⟩ := lanes
  simp only [aluEval, xl_or, sh8, show (0x10 : Word).toNat % 32 = 16 from rfl,
    show (0x18 : Word).toNat % 32 = 24 from rfl, ze_ex, l8, l16, l24, d80, d816, d824, d160, d168, d1624, d240, d248, d2416,
    z8, z16, z24, or8_0, zor8, and_self]

/-- Byte `j` of a word assembled from four bytes, high half first. -/
theorem wB_byte (b0 b1 b2 b3 : BitVec 8) :
    (aluEval .or (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18))
      (aluEval .or (b0.zeroExtend 32) (aluEval .sll (b1.zeroExtend 32) 8))).extractLsb' 0 8 = b0 ∧
    (aluEval .or (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18))
      (aluEval .or (b0.zeroExtend 32) (aluEval .sll (b1.zeroExtend 32) 8))).extractLsb' 8 8 = b1 ∧
    (aluEval .or (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18))
      (aluEval .or (b0.zeroExtend 32) (aluEval .sll (b1.zeroExtend 32) 8))).extractLsb' 16 8 = b2 ∧
    (aluEval .or (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18))
      (aluEval .or (b0.zeroExtend 32) (aluEval .sll (b1.zeroExtend 32) 8))).extractLsb' 24 8 = b3 := by
  obtain ⟨l8, l16, l24, d80, d816, d824, d160, d168, d1624, d240, d248, d2416, z8, z16, z24⟩ := lanes
  simp only [aluEval, xl_or, sh8, show (0x10 : Word).toNat % 32 = 16 from rfl,
    show (0x18 : Word).toNat % 32 = 24 from rfl, ze_ex, l8, l16, l24, d80, d816, d824, d160, d168, d1624, d240, d248, d2416,
    z8, z16, z24, or8_0, zor8, and_self]

theorem wC_byte (b0 b1 : BitVec 8) :
    (aluEval .or (b0.zeroExtend 32) (aluEval .sll (b1.zeroExtend 32) 8)).extractLsb' 0 8 = b0 ∧
    (aluEval .or (b0.zeroExtend 32) (aluEval .sll (b1.zeroExtend 32) 8)).extractLsb' 8 8 = b1 := by
  obtain ⟨l8, -, -, d80, -, -, -, -, -, -, -, -, z8, -, -⟩ := lanes
  simp only [aluEval, xl_or, sh8, ze_ex, l8, d80, z8, or8_0, zor8, and_self]

theorem wD_byte (b0 b1 : BitVec 8) :
    (aluEval .or (aluEval .sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32)).extractLsb' 0 8 = b0 ∧
    (aluEval .or (aluEval .sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32)).extractLsb' 8 8 = b1 := by
  obtain ⟨l8, -, -, d80, -, -, -, -, -, -, -, -, z8, -, -⟩ := lanes
  simp only [aluEval, xl_or, sh8, ze_ex, l8, d80, z8, or8_0, zor8, and_self]

def gsD0 : List BInstr := [.aluImm .add (18 : Fin 32) sp 0x1C4, .aluImm .add a0 x0 0x41]
def gsD1 : List BInstr :=
  [.lbu a0 (9 : Fin 32) 0x0, .lbu a1 (9 : Fin 32) 0x1, .lbu a2 (9 : Fin 32) 0x2, .lbu (23 : Fin 32) (9 : Fin 32) 0x3,
   .lbu (19 : Fin 32) (9 : Fin 32) 0x4, .lbu (20 : Fin 32) (9 : Fin 32) 0x5, .lbu (21 : Fin 32) (9 : Fin 32) 0x6,
   .lbu (22 : Fin 32) (9 : Fin 32) 0x7, .aluImm .sll a1 a1 0x8, .alu .or a0 a0 a1, .aluImm .add a1 (9 : Fin 32) 0x8]
def gsD2 : List BInstr := [.sb sp a2 0x266, .aluImm .add a0 sp 0x160, .aluImm .add a2 x0 0x2F]
def gsD3 : List BInstr :=
  [.lbu a0 (9 : Fin 32) 0x40, .lbu a1 (9 : Fin 32) 0x3F, .lbu a2 (9 : Fin 32) 0x38, .lbu a3 (9 : Fin 32) 0x37,
   .lbu a4 (9 : Fin 32) 0x39, .lbu a5 (9 : Fin 32) 0x3A, .aluImm .sll a0 a0 0x8, .aluImm .sll a2 a2 0x8,
   .alu .or a6 a0 a1, .lbu a1 (9 : Fin 32) 0x3B, .lbu (8 : Fin 32) (9 : Fin 32) 0x3C, .lbu a0 (9 : Fin 32) 0x3D,
   .lbu (9 : Fin 32) (9 : Fin 32) 0x3E, .aluImm .sll a4 a4 0x10, .aluImm .sll a5 a5 0x18, .alu .or a2 a2 a3,
   .alu .or a4 a4 a5, .alu .or a2 a2 a4, .aluImm .sll (8 : Fin 32) (8 : Fin 32) 0x8, .aluImm .sll a0 a0 0x10,
   .aluImm .sll (9 : Fin 32) (9 : Fin 32) 0x18]
def gsD4 : List BInstr :=
  [.lbu a4 sp 0x266, .alu .or a1 a1 (8 : Fin 32), .alu .or a0 a0 (9 : Fin 32), .alu .or a0 a0 a1, .sw sp a2 0x11C,
   .sw sp a0 0x120]
def gsD5 : List BInstr :=
  [.sb sp a4 0x4, .sb sp (23 : Fin 32) 0x5, .sb sp (19 : Fin 32) 0x6, .sb sp (20 : Fin 32) 0x7,
   .sb sp (21 : Fin 32) 0x8, .sb sp (22 : Fin 32) 0x9, .aluImm .add a0 sp 0xA, .aluImm .add a1 sp 0x160,
   .aluImm .add a2 x0 0x2F]
def gsD6 : List BInstr := [.aluImm .add a0 sp 0x39, .aluImm .add a1 sp 0x11C, .aluImm .add a2 x0 0xA]

theorem gsD0_end : blockEnd p256FromSec1Code 0x7C gsD0 = some 0x84 := by decide
theorem gsD1_end : blockEnd p256FromSec1Code 0x8A gsD1 = some 0xB2 := by decide
theorem gsD2_end : blockEnd p256FromSec1Code 0xB6 gsD2 = some 0xC0 := by decide
theorem gsD3_end : blockEnd p256FromSec1Code 0xC8 gsD3 = some 0x108 := by decide
theorem gsD4_end : blockEnd p256FromSec1Code 0x10C gsD4 = some 0x11E := by decide
theorem gsD5_end : blockEnd p256FromSec1Code 0x126 gsD5 = some 0x148 := by decide
theorem gsD6_end : blockEnd p256FromSec1Code 0x150 gsD6 = some 0x158 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **Copying the input**, from 0x7C to 0x160: after a delay loop, the 65
input bytes land at `S + 2`, through `S + 0x160`, `S + 0x11C`, and
`S + 0x264`. -/
theorem gs_stC {M : Word → BitVec 8} {n : Machine} {S inp : Word} (C : GsCode M) (F : Fr S 0x2D0)
    (s : St M GP n 0x7C (reg n)) (rsp : reg n sp = S) (r9 : reg n (9 : Fin 32) = inp)
    (sI : Sep inp 0x41 (S + 0xFFFFFE60) 0x470) (hI : inp.toNat + 0x41 ≤ 0x40000000) :
    ∃ n', Steps n n' ∧ St n'.mem GP n' 0x160 (reg n') ∧ GsCode n'.mem ∧
      (∀ k, k < 0x41 → n'.mem (S + BitVec.ofNat 32 (2 + k)) = M (inp + BitVec.ofNat 32 k)) ∧
      (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 2) 0x41 x 1 →
        Sep (S + BitVec.ofNat 32 0x11C) 0xA x 1 → Sep (S + BitVec.ofNat 32 0x160) 0x2F x 1 →
        Sep (S + BitVec.ofNat 32 0x264) 3 x 1 → n'.mem x = M x) ∧
      reg n' sp = S ∧ ∀ q : Fin 32, q.val ∈ [3, 4, 24, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨n1, c1, u1⟩ := s.block gsD0 C.self gsD0_end ⟨trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock gsD0 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have v1 : St M GP n1 0x84 (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have a1v : reg n1 a0 = BitVec.ofNat 32 0x41 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, gsD0, upd, ↓reduceIte]; (try rw [hz]); try rfl
  obtain ⟨n2, d2, u2⟩ := v1.notTaken C.self 0x86 gs_at_84 (by decide) (by
    show branchTaken .beq (reg n1 a0) 0 = false; rw [a1v]; decide)
  obtain ⟨n3, c3, u3, k3⟩ := gs_delay C 0x41 (by decide) (by decide) u2.self (by rw [u2.regs]; exact a1v)
  have K3 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 24, 26, 27] → reg n3 q = reg n q := fun q hq => by
    rw [k3 q (by revert hq; revert q; decide), u2.regs, r1, runBlock_reg _ _ _ q hz (by simp only [gsD0]; revert hq; revert q; decide)]
  have sp3 : reg n3 sp = S := by rw [K3 sp (by decide)]; exact rsp
  have i3 : reg n3 (9 : Fin 32) = inp := by rw [K3 9 (by decide)]; exact r9
  -- the first eight bytes, into registers
  obtain ⟨n4, c4, u4⟩ := u3.block gsD1 C.self gsD1_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r4 : ∀ q, reg n4 q = (runBlock gsD1 (M, reg n3)).2 q := fun q => by rw [u4.regs]
  have e23 : reg n4 (23 : Fin 32) = (M (inp + BitVec.ofNat 32 3)).zeroExtend 32 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, gsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e19 : reg n4 (19 : Fin 32) = (M (inp + BitVec.ofNat 32 4)).zeroExtend 32 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, gsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e20 : reg n4 (20 : Fin 32) = (M (inp + BitVec.ofNat 32 5)).zeroExtend 32 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, gsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e21 : reg n4 (21 : Fin 32) = (M (inp + BitVec.ofNat 32 6)).zeroExtend 32 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, gsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e22 : reg n4 (22 : Fin 32) = (M (inp + BitVec.ofNat 32 7)).zeroExtend 32 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, gsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e12 : reg n4 a2 = (M (inp + BitVec.ofNat 32 2)).zeroExtend 32 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, gsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e10 : reg n4 a0 = aluEval .or ((M (inp + BitVec.ofNat 32 0)).zeroExtend 32)
      (aluEval .sll ((M (inp + BitVec.ofNat 32 1)).zeroExtend 32) 0x8) := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, gsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e11 : reg n4 a1 = inp + 8 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, gsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e9 : reg n4 (9 : Fin 32) = inp := by rw [r4, runBlock_reg _ _ _ 9 u3.zero (by decide)]; exact i3
  have sp4 : reg n4 sp = S := by rw [r4, runBlock_reg _ _ _ sp u3.zero (by decide)]; exact sp3
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have iF : ∀ {j l c m : Nat}, j + l ≤ 0x41 → c + m ≤ 0x2D0 → Sep (inp + BitVec.ofNat 32 j) l (S + BitVec.ofNat 32 c) m :=
    fun {j l c m} h1 h2 => by
      have := (sI.sub (c := j) (l := l) (by omega)).subR (c := 0x1A0 + c) (l := m) (by omega)
      rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
        omega] at this
  have iL : ∀ {j l : Nat}, j + l ≤ 0x41 → Sep (inp + BitVec.ofNat 32 j) l (S + 0xFFFFFFF0) 16 := fun {j l} h => by
    have := (sI.sub (c := j) (l := l) (by omega)).subR (c := 0x190) (l := 16) (by decide)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x190 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
  have iT : ∀ j, j ≤ 0x41 → (inp + BitVec.ofNat 32 j).toNat = inp.toNat + j := fun j hj => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have l16b : ∀ d, d + 1 ≤ 0x2D0 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 1 := fun d hd => F.lowB hb16 (by decide) hd
  have sq : ∀ c l d, c + l ≤ 0x2D0 → d + 1 ≤ 0x2D0 → (c + l ≤ d ∨ d + 1 ≤ c) →
      Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 d) 1 := fun c l d h1 h2 h3 => sepS S h3 (by omega) (by omega)
  have kc : ∀ {m m' : Machine}, (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg m' q = reg m q) →
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q :=
    fun h q hq => h q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  obtain ⟨fA, fW, hFC⟩ := F.mc
  -- the first two bytes to `S + 0x264`
  have v4 : St M GP n4 0xB2 (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
  obtain ⟨n5, d5, u5⟩ := v4.sh C.self gs_at_b2 (off' := 0xB6) (by decide) (by
    rw [sp4]; show (S + BitVec.ofNat 32 0x264).toNat % 2 = 0; rw [F.at _ (by decide)]; omega)
  have e265 : S + BitVec.ofNat 32 0x264 + 1 = S + BitVec.ofNat 32 0x265 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨hw0', hw1'⟩ := wC_byte (M (inp + BitVec.ofNat 32 0)) (M (inp + BitVec.ofNat 32 1))
  rw [← e10] at hw0' hw1'
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore8 (memStore8 M (S + BitVec.ofNat 32 0x264) (M (inp + BitVec.ofNat 32 0)))
      (S + BitVec.ofNat 32 0x265) (M (inp + BitVec.ofNat 32 1)) = M1 := ⟨_, rfl⟩
  have v5 : St M1 GP n5 0xB6 (reg n5) := by
    rw [← hM1]; refine ⟨u5.pc, ?_, fun _ => rfl⟩
    rw [u5.mem, sp4, show S + 0x264 = S + BitVec.ofNat 32 0x264 from rfl, e265, hw0', hw1']
  have r5 : ∀ q, reg n5 q = reg n4 q := u5.regs
  have h1 : ∀ x, Sep (S + BitVec.ofNat 32 0x264) 2 x 1 → M1 x = M x := fun x hx => by
    rw [← hM1, dq_st8 ((hx.sub (c := 1) (l := 1) (by decide)) |> fun h => by rwa [add_ofNat_assoc] at h),
      dq_st8 ((hx.sub (c := 0) (l := 1) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h)]
  have C1 := C.hi fun x hx => h1 x (F.hiOut (by decide) hx)
  -- the third byte, and the copy of bytes 8..0x36 to `S + 0x160`
  obtain ⟨n6, c6, u6⟩ := v5.block gsD2 C1.self gsD2_end (by
    simp only [BlockOk, BInstr.ok, gsD2]; simp +decide only [and_true]
    rw [r5, sp4]; exact F.sepHi (by decide) (by decide) (by decide))
  have r6 : ∀ q, reg n6 q = (runBlock gsD2 (M1, reg n5)).2 q := fun q => by rw [u6.regs]
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore8 M1 (S + BitVec.ofNat 32 0x266) (M (inp + BitVec.ofNat 32 2)) = M2 := ⟨_, rfl⟩
  have m6 : n6.mem = M2 := by
    rw [u6.mem, ← hM2]; simp +decide only [runBlock, BInstr.run, gsD2, upd, ↓reduceIte]
    rw [r5, r5, sp4, e12, ze_ex]; rfl
  have h2 : ∀ x, Sep (S + BitVec.ofNat 32 0x266) 1 x 1 → M2 x = M1 x := fun x hx => by rw [← hM2]; exact dq_st8 hx
  have C2 := C1.hi fun x hx => h2 x (F.hiOut (by decide) hx)
  have sp6 : reg n6 sp = S := by rw [r6, runBlock_reg _ _ _ sp v5.zero (by decide), r5]; exact sp4
  obtain ⟨n7, c7, u7, fr7, k7⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x160) (src := inp + BitVec.ofNat 32 8) (S := S)
    (N := 0x2F) (⟨u6.pc, m6, fun _ => rfl⟩ : St M2 GP n6 0xC0 (reg n6)) C2.self C2.K.K gs_at_c0 gs_at_c4 (by decide) (by decide)
    sp6 (by rw [r6]; simp +decide only [runBlock, BInstr.run, gsD2, upd, ↓reduceIte]; rw [r5, sp4]; rfl)
    (by rw [r6, runBlock_reg _ _ _ a1 v5.zero (by decide), r5]; exact e11)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, gsD2, upd, ↓reduceIte]; (try rw [v5.zero]); try rfl)
    ⟨C2.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), iL (by decide),
      (iF (by decide) (by decide)).symm, fA, fW, by rw [F.at _ (by decide)]; omega, by rw [iT _ (by decide)]; omega⟩
  have fr7' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x160) 0x2F x 1 → n7.mem x = M2 x :=
    fun x a b => by rw [fr7 x a, copyBytes_sep b (Nat.le_refl _)]
  have C7 := C2.hi fun x hx => fr7' x (lo16 x hx) (F.hiOut (by decide) hx)
  have k7' := kc k7
  have sp7 : reg n7 sp = S := by rw [k7' sp (by decide)]; exact sp6
  have K7 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 19, 20, 21, 22, 23, 24, 26, 27] → reg n7 q = reg n4 q := fun q hq => by
    rw [k7' q (by revert hq; revert q; decide), r6, runBlock_reg _ _ _ q v5.zero (by simp only [gsD2]; revert hq; revert q; decide), r5]
  have m2I : ∀ j, j < 0x41 → M2 (inp + BitVec.ofNat 32 j) = M (inp + BitVec.ofNat 32 j) := fun j hj => by
    rw [h2 _ ((iF (by omega) (by decide)).symm), h1 _ ((iF (by omega) (by decide)).symm)]
  have n7I : ∀ j, j < 0x41 → n7.mem (inp + BitVec.ofNat 32 j) = M (inp + BitVec.ofNat 32 j) := fun j hj => by
    rw [fr7' _ ((iL (by omega)).symm) ((iF (by omega) (by decide)).symm), m2I j hj]
  -- bytes 0x37..0x40, into registers
  obtain ⟨n8, c8, u8⟩ := u7.block gsD3 C7.self gsD3_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
     trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r8 : ∀ q, reg n8 q = (runBlock gsD3 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
  have i7 : reg n7 (9 : Fin 32) = inp := by rw [K7 9 (by decide)]; exact e9
  have e8a6 : reg n8 a6 = aluEval .or (aluEval .sll ((M (inp + BitVec.ofNat 32 0x40)).zeroExtend 32) 0x8)
      ((M (inp + BitVec.ofNat 32 0x3F)).zeroExtend 32) := by
    rw [r8, ← n7I _ (by decide), ← n7I _ (by decide)]
    simp +decide only [runBlock, BInstr.run, gsD3, upd, ↓reduceIte]; rw [i7]; rfl
  have e8a2 : reg n8 a2 = aluEval .or (aluEval .or (aluEval .sll ((M (inp + BitVec.ofNat 32 0x38)).zeroExtend 32) 8)
      ((M (inp + BitVec.ofNat 32 0x37)).zeroExtend 32)) (aluEval .or (aluEval .sll ((M (inp + BitVec.ofNat 32 0x39)).zeroExtend 32) 0x10)
      (aluEval .sll ((M (inp + BitVec.ofNat 32 0x3A)).zeroExtend 32) 0x18)) := by
    rw [r8, ← n7I _ (by decide), ← n7I _ (by decide), ← n7I _ (by decide), ← n7I _ (by decide)]
    simp +decide only [runBlock, BInstr.run, gsD3, upd, ↓reduceIte]; rw [i7]; rfl
  have e8a1 : reg n8 a1 = (M (inp + BitVec.ofNat 32 0x3B)).zeroExtend 32 := by
    rw [r8, ← n7I _ (by decide)]; simp +decide only [runBlock, BInstr.run, gsD3, upd, ↓reduceIte]; rw [i7]; rfl
  have e8s0 : reg n8 (8 : Fin 32) = aluEval .sll ((M (inp + BitVec.ofNat 32 0x3C)).zeroExtend 32) 8 := by
    rw [r8, ← n7I _ (by decide)]; simp +decide only [runBlock, BInstr.run, gsD3, upd, ↓reduceIte]; rw [i7]; rfl
  have e8a0 : reg n8 a0 = aluEval .sll ((M (inp + BitVec.ofNat 32 0x3D)).zeroExtend 32) 0x10 := by
    rw [r8, ← n7I _ (by decide)]; simp +decide only [runBlock, BInstr.run, gsD3, upd, ↓reduceIte]; rw [i7]; rfl
  have e8s1 : reg n8 (9 : Fin 32) = aluEval .sll ((M (inp + BitVec.ofNat 32 0x3E)).zeroExtend 32) 0x18 := by
    rw [r8, ← n7I _ (by decide)]; simp +decide only [runBlock, BInstr.run, gsD3, upd, ↓reduceIte]; rw [i7]; rfl
  have sp8 : reg n8 sp = S := by rw [r8, runBlock_reg _ _ _ sp u7.zero (by decide)]; exact sp7
  have K8 : ∀ q : Fin 32, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 26, 27] → reg n8 q = reg n4 q := fun q hq => by
    rw [r8, runBlock_reg _ _ _ q u7.zero (by simp only [gsD3]; revert hq; revert q; decide), K7 q (by revert hq; revert q; decide)]
  -- the first two bytes back from `S + 0x264`
  have v8 : St n7.mem GP n8 0x108 (reg n8) := ⟨u8.pc, u8.mem, fun _ => rfl⟩
  obtain ⟨n9, d9, u9⟩ := v8.lh C7.self gs_at_108 (off' := 0x10C) (by decide) (by
    rw [sp8]; show (S + BitVec.ofNat 32 0x264).toNat % 2 = 0; rw [F.at _ (by decide)]; omega)
  have r9' : ∀ q, q ≠ a3 → reg n9 q = reg n8 q := fun q hq => by rw [u9.regs]; exact updz v8.zero hq
  have a9 : reg n9 a3 = (n7.mem (S + BitVec.ofNat 32 0x265) ++ n7.mem (S + BitVec.ofNat 32 0x264)).signExtend 32 := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]; rw [sp8, show S + 0x264 = S + BitVec.ofNat 32 0x264 from rfl, e265]
  -- bytes 0x37..0x3E to `S + 0x11C`
  have v9 : St n7.mem GP n9 0x10C (reg n9) := u9.self
  obtain ⟨n10, c10, u10⟩ := v9.block gsD4 C7.self gsD4_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gsD4]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [r9' sp (by decide), sp8]
    exact ⟨⟨by show (S + BitVec.ofNat 32 0x11C).toNat % 4 = 0; rw [F.at _ (by decide)]; omega,
        F.sepHi (by decide) (by decide) (by decide)⟩,
      ⟨by show (S + BitVec.ofNat 32 0x120).toNat % 4 = 0; rw [F.at _ (by decide)]; omega,
        F.sepHi (by decide) (by decide) (by decide)⟩⟩)
  have r10 : ∀ q, reg n10 q = (runBlock gsD4 (n7.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  obtain ⟨W1, hW1⟩ : ∃ W1, aluEval .or (aluEval .or (aluEval .sll ((M (inp + BitVec.ofNat 32 0x38)).zeroExtend 32) 8)
      ((M (inp + BitVec.ofNat 32 0x37)).zeroExtend 32)) (aluEval .or (aluEval .sll ((M (inp + BitVec.ofNat 32 0x39)).zeroExtend 32) 0x10)
      (aluEval .sll ((M (inp + BitVec.ofNat 32 0x3A)).zeroExtend 32) 0x18)) = W1 := ⟨_, rfl⟩
  obtain ⟨W2, hW2⟩ : ∃ W2, aluEval .or (aluEval .or (aluEval .sll ((M (inp + BitVec.ofNat 32 0x3D)).zeroExtend 32) 0x10)
      (aluEval .sll ((M (inp + BitVec.ofNat 32 0x3E)).zeroExtend 32) 0x18)) (aluEval .or ((M (inp + BitVec.ofNat 32 0x3B)).zeroExtend 32)
      (aluEval .sll ((M (inp + BitVec.ofNat 32 0x3C)).zeroExtend 32) 8)) = W2 := ⟨_, rfl⟩
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 (memStore32 n7.mem (S + BitVec.ofNat 32 0x11C) W1) (S + BitVec.ofNat 32 0x120) W2 = M3 :=
    ⟨_, rfl⟩
  have m10 : n10.mem = M3 := by
    rw [u10.mem, ← hM3, ← hW1, ← hW2]; simp only [runBlock, BInstr.run, gsD4]; simp +decide only [upd, ↓reduceIte]
    rw [r9' sp (by decide), r9' a2 (by decide), r9' a0 (by decide), r9' a1 (by decide), r9' 8 (by decide), r9' 9 (by decide),
      sp8, e8a2, e8a0, e8a1, e8s0, e8s1]; rfl
  have h3 : ∀ x, Sep (S + BitVec.ofNat 32 0x11C) 8 x 1 → M3 x = n7.mem x := fun x hx => by
    rw [← hM3, memStore32_get_sep ((hx.sub (c := 4) (l := 4) (by decide)) |> fun h => by rwa [add_ofNat_assoc] at h),
      memStore32_get_sep ((hx.sub (c := 0) (l := 4) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h)]
  have C10 := C7.hi fun x hx => h3 x (F.hiOut (by decide) hx)
  have a4v : reg n10 a4 = (n7.mem (S + BitVec.ofNat 32 0x266)).zeroExtend 32 := by
    rw [r10]; simp +decide only [runBlock, BInstr.run, gsD4, upd, ↓reduceIte]; rw [r9' sp (by decide), sp8]; rfl
  have K10 : ∀ q : Fin 32, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 26, 27] → reg n10 q = reg n4 q := fun q hq => by
    rw [r10, runBlock_reg _ _ _ q v9.zero (by simp only [gsD4]; revert hq; revert q; decide), r9' q (by revert hq; revert q; decide),
      K8 q hq]
  have sp10 : reg n10 sp = S := by rw [r10, runBlock_reg _ _ _ sp v9.zero (by decide), r9' sp (by decide)]; exact sp8
  have a6v : reg n10 a6 = reg n8 a6 := by
    rw [r10, runBlock_reg _ _ _ a6 v9.zero (by decide), r9' a6 (by decide)]
  have a3v : reg n10 a3 = reg n9 a3 := by rw [r10, runBlock_reg _ _ _ a3 v9.zero (by decide)]
  -- bytes 0x3F and 0x40 to `S + 0x124`
  have v10 : St M3 GP n10 0x11E (reg n10) := ⟨u10.pc, m10, fun _ => rfl⟩
  obtain ⟨n11, d11, u11⟩ := v10.sh C10.self gs_at_11e (off' := 0x122) (by decide) (by
    rw [sp10]; show (S + BitVec.ofNat 32 0x124).toNat % 2 = 0; rw [F.at _ (by decide)]; omega)
  obtain ⟨hx0, hx1⟩ := wD_byte (M (inp + BitVec.ofNat 32 0x3F)) (M (inp + BitVec.ofNat 32 0x40))
  rw [← e8a6, ← a6v] at hx0 hx1
  obtain ⟨M4, hM4⟩ : ∃ M4, memStore8 (memStore8 M3 (S + BitVec.ofNat 32 0x124) (M (inp + BitVec.ofNat 32 0x3F)))
      (S + BitVec.ofNat 32 0x125) (M (inp + BitVec.ofNat 32 0x40)) = M4 := ⟨_, rfl⟩
  have v11 : St M4 GP n11 0x122 (reg n11) := by
    rw [← hM4]; refine ⟨u11.pc, ?_, fun _ => rfl⟩
    rw [u11.mem, sp10, show S + 0x124 = S + BitVec.ofNat 32 0x124 from rfl,
      show S + BitVec.ofNat 32 0x124 + 1 = S + BitVec.ofNat 32 0x125 by rw [BitVec.add_assoc]; rfl, hx0, hx1]
  have h4 : ∀ x, Sep (S + BitVec.ofNat 32 0x124) 2 x 1 → M4 x = M3 x := fun x hx => by
    rw [← hM4, dq_st8 ((hx.sub (c := 1) (l := 1) (by decide)) |> fun h => by rwa [add_ofNat_assoc] at h),
      dq_st8 ((hx.sub (c := 0) (l := 1) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h)]
  have C11 := C10.hi fun x hx => h4 x (F.hiOut (by decide) hx)
  have r11 : ∀ q, reg n11 q = reg n10 q := u11.regs
  -- bytes 0 and 1 to `S + 2`
  obtain ⟨n12, d12, u12⟩ := v11.sh C11.self gs_at_122 (off' := 0x126) (by decide) (by
    rw [r11, sp10]; show (S + BitVec.ofNat 32 0x2).toNat % 2 = 0; rw [F.at _ (by decide)]; omega)
  obtain ⟨M5, hM5⟩ : ∃ M5, memStore8 (memStore8 M4 (S + BitVec.ofNat 32 0x2) (n7.mem (S + BitVec.ofNat 32 0x264)))
      (S + BitVec.ofNat 32 0x3) (n7.mem (S + BitVec.ofNat 32 0x265)) = M5 := ⟨_, rfl⟩
  have v12 : St M5 GP n12 0x126 (reg n12) := by
    rw [← hM5]; refine ⟨u12.pc, ?_, fun _ => rfl⟩
    rw [u12.mem, r11, r11, sp10, a3v, a9, signExtend_lo, signExtend_hi,
      show S + 0x2 = S + BitVec.ofNat 32 0x2 from rfl,
      show S + BitVec.ofNat 32 0x2 + 1 = S + BitVec.ofNat 32 0x3 by rw [BitVec.add_assoc]; rfl]
  have h5 : ∀ x, Sep (S + BitVec.ofNat 32 0x2) 2 x 1 → M5 x = M4 x := fun x hx => by
    rw [← hM5, dq_st8 ((hx.sub (c := 1) (l := 1) (by decide)) |> fun h => by rwa [add_ofNat_assoc] at h),
      dq_st8 ((hx.sub (c := 0) (l := 1) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h)]
  have C12 := C11.hi fun x hx => h5 x (F.hiOut (by decide) hx)
  have r12 : ∀ q, reg n12 q = reg n11 q := u12.regs
  -- bytes 2..7
  obtain ⟨n13, c13, u13⟩ := v12.block gsD5 C12.self gsD5_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gsD5]; simp +decide only [and_true]
    rw [r12, r11, sp10]
    exact ⟨F.sepHi (by decide) (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide),
      F.sepHi (by decide) (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide),
      F.sepHi (by decide) (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩)
  have r13 : ∀ q, reg n13 q = (runBlock gsD5 (M5, reg n12)).2 q := fun q => by rw [u13.regs]
  obtain ⟨M6, hM6⟩ : ∃ M6, memStore8 (memStore8 (memStore8 (memStore8 (memStore8 (memStore8 M5
      (S + BitVec.ofNat 32 0x4) (n7.mem (S + BitVec.ofNat 32 0x266))) (S + BitVec.ofNat 32 0x5) (M (inp + BitVec.ofNat 32 3)))
      (S + BitVec.ofNat 32 0x6) (M (inp + BitVec.ofNat 32 4))) (S + BitVec.ofNat 32 0x7) (M (inp + BitVec.ofNat 32 5)))
      (S + BitVec.ofNat 32 0x8) (M (inp + BitVec.ofNat 32 6))) (S + BitVec.ofNat 32 0x9) (M (inp + BitVec.ofNat 32 7)) = M6 :=
    ⟨_, rfl⟩
  have m13 : n13.mem = M6 := by
    rw [u13.mem, ← hM6]; simp +decide only [runBlock, BInstr.run, gsD5, upd, ↓reduceIte]
    rw [r12, r12, r12, r12, r12, r12, r12, r11, r11, r11, r11, r11, r11, r11, sp10, a4v, ze_ex, K10 23 (by decide),
      K10 19 (by decide), K10 20 (by decide), K10 21 (by decide), K10 22 (by decide), e23, e19, e20, e21, e22,
      ze_ex, ze_ex, ze_ex, ze_ex, ze_ex]; rfl
  have h6 : ∀ x, Sep (S + BitVec.ofNat 32 0x4) 6 x 1 → M6 x = M5 x := fun x hx => by
    have sb : ∀ c, c < 6 → Sep (S + BitVec.ofNat 32 (0x4 + c)) 1 x 1 := fun c hc => by
      have := hx.sub (c := c) (l := 1) (by omega); rwa [add_ofNat_assoc] at this
    rw [← hM6, dq_st8 (sb 5 (by decide)), dq_st8 (sb 4 (by decide)), dq_st8 (sb 3 (by decide)), dq_st8 (sb 2 (by decide)),
      dq_st8 (sb 1 (by decide)), dq_st8 (sb 0 (by decide))]
  have C13 := C12.hi fun x hx => h6 x (F.hiOut (by decide) hx)
  have sp13 : reg n13 sp = S := by rw [r13, runBlock_reg _ _ _ sp v12.zero (by decide), r12, r11]; exact sp10
  -- bytes 8..0x36 to `S + 0xA`, and 0x37..0x40 to `S + 0x39`
  obtain ⟨n14, c14, u14, fr14, k14⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0xA) (src := S + BitVec.ofNat 32 0x160)
    (S := S) (N := 0x2F) (⟨u13.pc, m13, fun _ => rfl⟩ : St M6 GP n13 0x148 (reg n13)) C13.self C13.K.K gs_at_148 gs_at_14c
    (by decide) (by decide) sp13
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, gsD5, upd, ↓reduceIte]; rw [r12, r11, sp10]; rfl)
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, gsD5, upd, ↓reduceIte]; rw [r12, r11, sp10]; rfl)
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, gsD5, upd, ↓reduceIte]; (try rw [v12.zero]); try rfl)
    ⟨C13.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inl (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr14' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0xA) 0x2F x 1 → n14.mem x = M6 x :=
    fun x a b => by rw [fr14 x a, copyBytes_sep b (Nat.le_refl _)]
  have C14 := C13.hi fun x hx => fr14' x (lo16 x hx) (F.hiOut (by decide) hx)
  have k14' := kc k14
  have sp14 : reg n14 sp = S := by rw [k14' sp (by decide)]; exact sp13
  obtain ⟨n15, c15, u15⟩ := u14.block gsD6 C14.self gsD6_end ⟨trivial, trivial, trivial, trivial⟩
  have r15 : ∀ q, reg n15 q = (runBlock gsD6 (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
  obtain ⟨n16, c16, u16, fr16, k16⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x39) (src := S + BitVec.ofNat 32 0x11C)
    (S := S) (N := 0xA) (⟨u15.pc, u15.mem, fun _ => rfl⟩ : St n14.mem GP n15 0x158 (reg n15)) C14.self C14.K.K gs_at_158 gs_at_15c
    (by decide) (by decide) (by rw [r15, runBlock_reg _ _ _ sp u14.zero (by decide)]; exact sp14)
    (by rw [r15]; simp +decide only [runBlock, BInstr.run, gsD6, upd, ↓reduceIte]; rw [sp14]; rfl)
    (by rw [r15]; simp +decide only [runBlock, BInstr.run, gsD6, upd, ↓reduceIte]; rw [sp14]; rfl)
    (by rw [r15]; simp +decide only [runBlock, BInstr.run, gsD6, upd, ↓reduceIte]; (try rw [u14.zero]); try rfl)
    ⟨C14.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inl (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr16' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x39) 0xA x 1 → n16.mem x = n14.mem x :=
    fun x a b => by rw [fr16 x a, copyBytes_sep b (Nat.le_refl _)]
  have C16 := C14.hi fun x hx => fr16' x (lo16 x hx) (F.hiOut (by decide) hx)
  have k16' := kc k16
  have KK : ∀ q : Fin 32, q.val ∈ [3, 4, 24, 26, 27] → reg n16 q = reg n q := fun q hq => by
    rw [k16' q (by revert hq; revert q; decide), r15, runBlock_reg _ _ _ q u14.zero (by simp only [gsD6]; revert hq; revert q; decide),
      k14' q (by revert hq; revert q; decide), r13, runBlock_reg _ _ _ q v12.zero (by simp only [gsD5]; revert hq; revert q; decide),
      r12, r11, K10 q (by revert hq; revert q; decide), r4,
      runBlock_reg _ _ _ q u3.zero (by simp only [gsD1]; revert hq; revert q; decide), K3 q (by revert hq; revert q; decide)]
  have sp16 : reg n16 sp = S := by
    rw [k16' sp (by decide), r15, runBlock_reg _ _ _ sp u14.zero (by decide)]; exact sp14
  -- where each byte came from
  have n7_264 : n7.mem (S + BitVec.ofNat 32 0x264) = M (inp + BitVec.ofNat 32 0) := by
    rw [fr7' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inl (by decide))),
      h2 _ (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM1,
      dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x265) 1 (S + BitVec.ofNat 32 0x264) 1),
      memStore8_same]
  have n7_265 : n7.mem (S + BitVec.ofNat 32 0x265) = M (inp + BitVec.ofNat 32 1) := by
    rw [fr7' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inl (by decide))),
      h2 _ (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM1, memStore8_same]
  have n7_266 : n7.mem (S + BitVec.ofNat 32 0x266) = M (inp + BitVec.ofNat 32 2) := by
    rw [fr7' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inl (by decide))), ← hM2, memStore8_same]
  have hM4w : ∀ j, j < 0xA → M4 (S + BitVec.ofNat 32 (0x11C + j)) = M (inp + BitVec.ofNat 32 (0x37 + j)) := fun j hj => by
    have w1 := wA_byte (M (inp + BitVec.ofNat 32 0x37)) (M (inp + BitVec.ofNat 32 0x38)) (M (inp + BitVec.ofNat 32 0x39))
      (M (inp + BitVec.ofNat 32 0x3A))
    have w2 := wB_byte (M (inp + BitVec.ofNat 32 0x3B)) (M (inp + BitVec.ofNat 32 0x3C)) (M (inp + BitVec.ofNat 32 0x3D))
      (M (inp + BitVec.ofNat 32 0x3E))
    rw [hW1] at w1; rw [hW2] at w2
    have lo : ∀ i, i < 4 → M4 (S + BitVec.ofNat 32 (0x11C + i)) = W1.extractLsb' (8 * i) 8 := fun i hi => by
      rw [h4 _ (sq _ _ _ (by decide) (by omega) (.inr (by omega))), ← hM3,
        memStore32_get_sep (sq _ _ _ (by decide) (by omega) (.inr (by omega))), ← add_ofNat_assoc, gst32 _ _ _ _ hi]
    have hi' : ∀ i, i < 4 → M4 (S + BitVec.ofNat 32 (0x120 + i)) = W2.extractLsb' (8 * i) 8 := fun i hi => by
      rw [h4 _ (sq _ _ _ (by decide) (by omega) (.inr (by omega))), ← hM3, ← add_ofNat_assoc, gst32 _ _ _ _ hi]
    match j, hj with
    | 0, _ => rw [lo 0 (by decide)]; exact w1.1
    | 1, _ => rw [lo 1 (by decide)]; exact w1.2.1
    | 2, _ => rw [lo 2 (by decide)]; exact w1.2.2.1
    | 3, _ => rw [lo 3 (by decide)]; exact w1.2.2.2
    | 4, _ => rw [hi' 0 (by decide)]; exact w2.1
    | 5, _ => rw [hi' 1 (by decide)]; exact w2.2.1
    | 6, _ => rw [hi' 2 (by decide)]; exact w2.2.2.1
    | 7, _ => rw [hi' 3 (by decide)]; exact w2.2.2.2
    | 8, _ =>
      rw [← hM4, dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) :
        Sep (S + BitVec.ofNat 32 0x125) 1 (S + BitVec.ofNat 32 0x124) 1)]
      exact memStore8_same _ _ _
    | 9, _ => rw [← hM4]; exact memStore8_same _ _ _
  refine ⟨n16, c1.trans (.cons d2 (c3.trans (c4.trans (.cons d5 (c6.trans (c7.trans (c8.trans (.cons d9 (c10.trans
    (.cons d11 (.cons d12 (c13.trans (c14.trans (c15.trans c16)))))))))))))), u16, C16, fun k hk => ?_,
    fun x h16 h2' h11C h160 h264 => ?_, sp16, KK⟩
  · match k, hk with
    | 0, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x2) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        h6 _ (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM5,
        dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x3) 1 (S + BitVec.ofNat 32 0x2) 1),
        memStore8_same, n7_264]
    | 1, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x3) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        h6 _ (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM5, memStore8_same, n7_265]
    | 2, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x4) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM6]
      rw [dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x9) 1 (S + BitVec.ofNat 32 0x4) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x8) 1 (S + BitVec.ofNat 32 0x4) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x7) 1 (S + BitVec.ofNat 32 0x4) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x6) 1 (S + BitVec.ofNat 32 0x4) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x5) 1 (S + BitVec.ofNat 32 0x4) 1), memStore8_same, n7_266]
    | 3, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x5) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM6]
      rw [dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x9) 1 (S + BitVec.ofNat 32 0x5) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x8) 1 (S + BitVec.ofNat 32 0x5) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x7) 1 (S + BitVec.ofNat 32 0x5) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x6) 1 (S + BitVec.ofNat 32 0x5) 1), memStore8_same]
    | 4, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x6) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM6]
      rw [dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x9) 1 (S + BitVec.ofNat 32 0x6) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x8) 1 (S + BitVec.ofNat 32 0x6) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x7) 1 (S + BitVec.ofNat 32 0x6) 1), memStore8_same]
    | 5, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x7) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM6]
      rw [dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x9) 1 (S + BitVec.ofNat 32 0x7) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x8) 1 (S + BitVec.ofNat 32 0x7) 1), memStore8_same]
    | 6, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x8) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM6]
      rw [dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x9) 1 (S + BitVec.ofNat 32 0x8) 1), memStore8_same]
    | 7, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x9) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM6]
      rw [memStore8_same]
    | k + 8, hk =>
      by_cases hj : k < 0x2F
      · rw [show 2 + (k + 8) = 0xA + k by omega, ← add_ofNat_assoc,
          fr16' _ (by rw [add_ofNat_assoc]; exact l16b _ (by omega))
            (by rw [add_ofNat_assoc]; exact sq _ _ _ (by decide) (by omega) (.inr (by omega))),
          fr14 _ (by rw [add_ofNat_assoc]; exact l16b _ (by omega)), cp_at hj (by decide), add_ofNat_assoc,
          h6 _ (sq _ _ _ (by decide) (by omega) (.inl (by omega))), h5 _ (sq _ _ _ (by decide) (by omega) (.inl (by omega))),
          h4 _ (sq _ _ _ (by decide) (by omega) (.inl (by omega))), h3 _ (sq _ _ _ (by decide) (by omega) (.inl (by omega))),
          ← add_ofNat_assoc, fr7 _ (by rw [add_ofNat_assoc]; exact l16b _ (by omega)), cp_at hj (by decide),
          add_ofNat_assoc, m2I _ (by omega), show 8 + k = k + 8 by omega]
      · rw [show 2 + (k + 8) = 0x39 + (k - 0x2F) by omega, ← add_ofNat_assoc,
          fr16 _ (by rw [add_ofNat_assoc]; exact l16b _ (by omega)), cp_at (by omega) (by decide), add_ofNat_assoc,
          fr14' _ (l16b _ (by omega)) (sq _ _ _ (by decide) (by omega) (.inl (by omega))),
          h6 _ (sq _ _ _ (by decide) (by omega) (.inl (by omega))), h5 _ (sq _ _ _ (by decide) (by omega) (.inl (by omega))),
          hM4w _ (by omega), show 0x37 + (k - 0x2F) = k + 8 by omega]
  · have sub : ∀ {c l : Nat} (b : Word) (L : Nat), Sep b L x 1 → c + l ≤ L → Sep (b + BitVec.ofNat 32 c) l x 1 :=
      fun {c l} b L h hl => h.sub (c := c) (l := l) hl
    rw [fr16' x h16 (by have := sub (c := 0x37) (l := 0xA) _ _ h2' (by decide); rwa [add_ofNat_assoc] at this),
      fr14' x h16 (by have := sub (c := 8) (l := 0x2F) _ _ h2' (by decide); rwa [add_ofNat_assoc] at this),
      h6 x (by have := sub (c := 2) (l := 6) _ _ h2' (by decide); rwa [add_ofNat_assoc] at this),
      h5 x (by have := sub (c := 0) (l := 2) _ _ h2' (by decide); rwa [add_ofNat_zero] at this),
      h4 x (by have := sub (c := 8) (l := 2) _ _ h11C (by decide); rwa [add_ofNat_assoc] at this),
      h3 x (by have := sub (c := 0) (l := 8) _ _ h11C (by decide); rwa [add_ofNat_zero] at this),
      fr7' x h16 h160,
      h2 x (by have := sub (c := 2) (l := 1) _ _ h264 (by decide); rwa [add_ofNat_assoc] at this),
      h1 x (by have := sub (c := 0) (l := 2) _ _ h264 (by decide); rwa [add_ofNat_zero] at this)]
def gsT1 : List BInstr := [.lbu (22 : Fin 32) sp 0x2, .alu .add a0 x0 (22 : Fin 32)]
def gsT2 : List BInstr := [.aluImm .add (19 : Fin 32) sp 0x3, .alu .add a0 x0 (22 : Fin 32)]
def gsT3 : List BInstr := [.aluImm .and (8 : Fin 32) a0 0xFE, .alu .add a0 x0 (22 : Fin 32)]
def gsT4 : List BInstr := [.aluImm .add a1 x0 0x2, .aluImm .and a0 a0 0xFF]
def gsT5 : List BInstr := [.aluImm .add a1 x0 0x5]
theorem gsT1_end : blockEnd p256FromSec1Code 0x160 gsT1 = some 0x166 := by decide
theorem gsT2_end : blockEnd p256FromSec1Code 0x18E gsT2 = some 0x194 := by decide
theorem gsT3_end : blockEnd p256FromSec1Code 0x19C gsT3 = some 0x1A2 := by decide
theorem gsT4_end : blockEnd p256FromSec1Code 0x1AA gsT4 = some 0x1B0 := by decide
theorem gsT5_end : blockEnd p256FromSec1Code 0x1D0 gsT5 = some 0x1D2 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **The tag dispatch**, from 0x160 to the uncompressed branch at 0x312,
for the tag 4 at `S + 0x2`: `is_identity` is false, and `tag` is neither
compressed nor compact. -/
theorem gs_stD {M : Word → BitVec 8} {n : Machine} {S : Word} (C : GsCode M) (F : Fr S 0x2D0)
    (s : St M GP n 0x160 (reg n)) (rsp : reg n sp = S) (ht : M (S + BitVec.ofNat 32 0x2) = 4) :
    ∃ n', Steps n n' ∧ St n'.mem GP n' 0x312 (reg n') ∧ GsCode n'.mem ∧
      (∀ x, Sep (S + 0xFFFFFFB0) 0x50 x 1 → n'.mem x = M x) ∧ reg n' sp = S ∧
      reg n' (19 : Fin 32) = S + BitVec.ofNat 32 0x3 ∧ reg n' (22 : Fin 32) = (4 : BitVec 8).zeroExtend 32 ∧
      ∀ q : Fin 32, q.val ∈ [3, 4, 24, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hbA : (S + 0xFFFFFFB0).toNat = S.toNat - 0x50 := F.below 0x50 (by decide) (by decide)
  have hb4 : (S + 0xFFFFFFC0).toNat = S.toNat - 0x40 := F.below 0x40 (by decide) (by decide)
  have loA : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFB0) 0x50 x 1 := fun x hx =>
    sep_of_le (by rw [hbA]; omega) (by have := x.isLt; omega)
  have sub40 : ∀ {x : Word}, Sep (S + 0xFFFFFFB0) 0x50 x 1 → Sep (S + 0xFFFFFFC0) 0x40 x 1 := fun {x} hx => by
    have := hx.sub (c := 0x10) (l := 0x40) (by decide)
    rwa [show S + 0xFFFFFFB0 + BitVec.ofNat 32 0x10 = S + 0xFFFFFFC0 by rw [BitVec.add_assoc]; rfl] at this
  have ok4 : Sec1TagOk (4 : BitVec 8) := by decide
  obtain ⟨n1, c1, u1⟩ := s.block gsT1 C.self gsT1_end ⟨trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock gsT1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have e22 : reg n1 (22 : Fin 32) = (4 : BitVec 8).zeroExtend 32 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, gsT1, upd, ↓reduceIte]; rw [rsp]
    show (M (S + BitVec.ofNat 32 0x2)).zeroExtend 32 = _; rw [ht]
  obtain ⟨n2, c2, u2, a2, sp2, k2, fr2⟩ := c_isid (t := 4) (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M GP n1 0x166 (reg n1))
    C.self C.K.K F gs_at_166 gs_at_16a (by decide) (by decide) (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gsT1, upd, ↓reduceIte]; rw [← e22, r1]
        simp +decide only [runBlock, BInstr.run, gsT1, upd, ↓reduceIte]; exact BitVec.zero_add _) ok4
  have C2 := C.hi fun x hx => fr2 x (loA x hx)
  obtain ⟨n3, d3, u3⟩ := u2.taken C2.self 0x18E gs_at_16e (by decide) (by
    show branchTaken .beq (reg n2 a0) 0 = true; rw [a2]; decide)
  have K2 : ∀ q : Fin 32, q.val ∈ [3, 4, 24, 26, 27] → reg n3 q = reg n q := fun q hq => by
    rw [u3.regs, k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), r1,
      runBlock_reg _ _ _ q hz (by simp only [gsT1]; revert hq; revert q; decide)]
  have e322 : reg n3 (22 : Fin 32) = (4 : BitVec 8).zeroExtend 32 := by
    rw [u3.regs, k2 22 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact e22
  have sp3 : reg n3 sp = S := by rw [u3.regs]; exact sp2
  obtain ⟨n4, c4, u4⟩ := u3.self.block gsT2 C2.self gsT2_end ⟨trivial, trivial, trivial⟩
  have r4 : ∀ q, reg n4 q = (runBlock gsT2 (n2.mem, reg n3)).2 q := fun q => by rw [u4.regs]
  obtain ⟨n5, c5, u5, a5, sp5, k5, fr5⟩ := c_tag (t := 4) (⟨u4.pc, u4.mem, fun _ => rfl⟩ : St n2.mem GP n4 0x194 (reg n4))
    C2.self C2.K.K F gs_at_194 gs_at_198 (by decide) (by decide)
    (by rw [r4, runBlock_reg _ _ _ sp u3.self.zero (by decide)]; exact sp3)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, gsT2, upd, ↓reduceIte]; rw [e322]; exact BitVec.zero_add _) ok4
  have C5 := C2.hi fun x hx => fr5 x (sub40 (loA x hx))
  obtain ⟨n6, c6, u6⟩ := u5.block gsT3 C5.self gsT3_end ⟨trivial, trivial, trivial⟩
  have r6 : ∀ q, reg n6 q = (runBlock gsT3 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  have K5 : ∀ q : Fin 32, q.val ∈ [3, 4, 22, 24, 26, 27] → reg n5 q = reg n3 q := fun q hq => by
    rw [k5 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), r4,
      runBlock_reg _ _ _ q u3.self.zero (by simp only [gsT2]; revert hq; revert q; decide)]
  obtain ⟨n7, c7, u7, a7, sp7, k7, fr7⟩ := c_tag (t := 4) (⟨u6.pc, u6.mem, fun _ => rfl⟩ : St n5.mem GP n6 0x1A2 (reg n6))
    C5.self C5.K.K F gs_at_1a2 gs_at_1a6 (by decide) (by decide)
    (by rw [r6, runBlock_reg _ _ _ sp u5.zero (by decide)]; exact sp5)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, gsT3, upd, ↓reduceIte]; rw [K5 22 (by decide), e322]
        exact BitVec.zero_add _) ok4
  have C7 := C5.hi fun x hx => fr7 x (sub40 (loA x hx))
  have e78 : reg n7 (8 : Fin 32) = aluEval .and ((4 : BitVec 8).zeroExtend 32) 0xFE := by
    rw [k7 8 (by decide) (by decide) (by decide) (by decide) (by decide), r6]
    simp +decide only [runBlock, BInstr.run, gsT3, upd, ↓reduceIte]; rw [a5]
  obtain ⟨n8, c8, u8⟩ := u7.block gsT4 C7.self gsT4_end ⟨trivial, trivial, trivial⟩
  have r8 : ∀ q, reg n8 q = (runBlock gsT4 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
  obtain ⟨n9, d9, u9⟩ := (⟨u8.pc, u8.mem, fun _ => rfl⟩ : St n7.mem GP n8 0x1B0 (reg n8)).taken C7.self 0x1D0 gs_at_1b0
    (by decide) (by
      show branchTaken .bne (reg n8 (8 : Fin 32)) (reg n8 a1) = true
      rw [r8, r8]; simp +decide only [runBlock, BInstr.run, gsT4, upd, ↓reduceIte]; rw [e78, u7.zero]; decide)
  obtain ⟨n10, c10, u10⟩ := u9.self.block gsT5 C7.self gsT5_end ⟨trivial, trivial⟩
  have r10 : ∀ q, reg n10 q = (runBlock gsT5 (n7.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  obtain ⟨n11, d11, u11⟩ := (⟨u10.pc, u10.mem, fun _ => rfl⟩ : St n7.mem GP n10 0x1D2 (reg n10)).taken C7.self 0x312
    gs_at_1d2 (by decide) (by
      show branchTaken .bne (reg n10 a0) (reg n10 a1) = true
      rw [r10, r10]; simp +decide only [runBlock, BInstr.run, gsT5, upd, ↓reduceIte]; rw [u9.regs, r8]
      simp +decide only [runBlock, BInstr.run, gsT4, upd, ↓reduceIte]; rw [a7, u9.self.zero]; decide)
  have KK : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 19, 22, 24, 26, 27] → reg n11 q = reg n7 q := fun q hq => by
    rw [u11.regs, r10, runBlock_reg _ _ _ q u9.self.zero (by simp only [gsT5]; revert hq; revert q; decide), u9.regs, r8,
      runBlock_reg _ _ _ q u7.zero (by simp only [gsT4]; revert hq; revert q; decide)]
  have K7 : ∀ q : Fin 32, q.val ∈ [3, 4, 19, 22, 24, 26, 27] → reg n7 q = reg n5 q := fun q hq => by
    rw [k7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), r6,
      runBlock_reg _ _ _ q u5.zero (by simp only [gsT3]; revert hq; revert q; decide)]
  refine ⟨n11, c1.trans (c2.trans (.cons d3 (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (.cons d9 (c10.trans
    (.single d11)))))))))), ⟨u11.pc, by rw [u11.mem], fun _ => rfl⟩, by rw [u11.mem]; exact C7,
    fun x hx => by rw [u11.mem, fr7 x (sub40 hx), fr5 x (sub40 hx), fr2 x hx], ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [KK sp (by decide)]; exact sp7
  · rw [KK 19 (by decide), K7 19 (by decide), k5 19 (by decide) (by decide) (by decide) (by decide) (by decide), r4]
    simp +decide only [runBlock, BInstr.run, gsT2, upd, ↓reduceIte]; rw [sp3]; rfl
  · rw [KK 22 (by decide), K7 22 (by decide), K5 22 (by decide)]; exact e322
  · rw [KK q (by revert hq; revert q; decide), K7 q (by revert hq; revert q; decide), K5 q (by revert hq; revert q; decide),
      K2 q (by revert hq; revert q; decide)]

/-- `v` in Montgomery form when it is below `p`, else 0: what `from_repr`
and the select after it leave. -/
def gsMont (v : Nat) : Nat := if v < p256 then v * 2 ^ 256 % p256 else 0

/-- Whether `v` is below `p`, as `from_repr`'s choice. -/
def gsOk (v : Nat) : Word := if v < p256 then 1 else 0

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 600 in
theorem r2_mont2 : dataVal p256ParamsData 0x40 8 * p2RInv % p256 = 2 ^ 256 % p256 := by unfold p256 p2RInv; decide

def gsY1 : List BInstr := [.aluImm .add a1 sp 0x23, .aluImm .add a0 sp 0x160]
def gsY2 : List BInstr := [.aluImm .add a0 sp 0x1E4, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0]
def gsY3 : List BInstr :=
  [.lbu (18 : Fin 32) sp 0x180, .aluImm .add a0 sp 0x244, .aluImm .add a1 sp 0x1E4, .aluImm .add a2 sp 0x160,
   .alu .add a3 x0 (18 : Fin 32)]
def gsX1 : List BInstr := [.aluImm .add a0 sp 0xD4, .alu .add a1 x0 (19 : Fin 32)]
def gsX2 : List BInstr := [.aluImm .add a0 sp 0x204, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0]
def gsX3 : List BInstr :=
  [.lbu (19 : Fin 32) sp 0xF4, .aluImm .add a0 sp 0x284, .aluImm .add a1 sp 0x204, .aluImm .add a2 sp 0xD4,
   .alu .add a3 x0 (19 : Fin 32)]
theorem frp2_val {X x : Nat} (hX : X < p256) (h : X * 2 ^ 256 % p256 = x * dataVal p256ParamsData 0x40 8 % p256) :
    X = x * 2 ^ 256 % p256 := by
  rw [p2_mont hX h]; unfold p2fm
  rw [Nat.mul_assoc, Nat.mul_mod, r2_mont2, ← Nat.mul_mod]

theorem gsY1_end : blockEnd p256FromSec1Code 0x312 gsY1 = some 0x318 := by decide
theorem gsY2_end : blockEnd p256FromSec1Code 0x320 gsY2 = some 0x328 := by decide
theorem gsY3_end : blockEnd p256FromSec1Code 0x330 gsY3 = some 0x33C := by decide
theorem gsX1_end : blockEnd p256FromSec1Code 0x344 gsX1 = some 0x348 := by decide
theorem gsX2_end : blockEnd p256FromSec1Code 0x350 gsX2 = some 0x358 := by decide
theorem gsX3_end : blockEnd p256FromSec1Code 0x360 gsX3 = some 0x36C := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **Decoding `y`**, from 0x312 to 0x344: `from_repr` on the 32 bytes at
`S + 0x23`, then the select of its result or zero into `S + 0x244`; `s2`
holds the choice. -/
theorem gs_decY {M : Word → BitVec 8} {n : Machine} {S : Word} (C : GsCode M) (D : P2Data M) (F : Fr S 0x2D0)
    (s : St M GP n 0x312 (reg n)) (rsp : reg n sp = S) :
    ∃ n', Steps n n' ∧ St n'.mem GP n' 0x344 (reg n') ∧ GsCode n'.mem ∧ P2Data n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x244) 8 = gsMont (beNat (memBytes M (S + BitVec.ofNat 32 0x23) 32)) ∧
      reg n' (18 : Fin 32) = gsOk (beNat (memBytes M (S + BitVec.ofNat 32 0x23) 32)) ∧
      (∀ x, Sep (S + 0xFFFFFEC0) 0x140 x 1 → Sep (S + BitVec.ofNat 32 0x160) 0x21 x 1 →
        Sep (S + BitVec.ofNat 32 0x1E4) 0x20 x 1 → Sep (S + BitVec.ofNat 32 0x244) 0x20 x 1 → n'.mem x = M x) ∧
      reg n' sp = S ∧ ∀ q : Fin 32, q.val ∈ [3, 4, 19, 22, 24, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hbF : (S + 0xFFFFFEC0).toNat = S.toNat - 0x140 := F.below 0x140 (by decide) (by decide)
  have hb50 : (S + 0xFFFFFFB0).toNat = S.toNat - 0x50 := F.below 0x50 (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block gsY1 C.self gsY1_end ⟨trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock gsY1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, ok2, bad2, fr2, sp2, k2⟩ := c2_frp (out := S + BitVec.ofNat 32 0x160)
    (inp := S + BitVec.ofNat 32 0x23) (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M GP n1 0x318 (reg n1)) C.self C.K D F
    gs_at_318 gs_at_31c (by decide) (by decide) (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gsY1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gsY1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (co := 0x160) (by decide) rfl
    ((sep_of_le (by rw [hbF, F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega)).symm)
  have hv2 : accV n2.mem (S + BitVec.ofNat 32 0x160) 8 = gsMont (beNat (memBytes M (S + BitVec.ofNat 32 0x23) 32)) ∧
      n2.mem (S + BitVec.ofNat 32 0x160 + 0x20) = (if beNat (memBytes M (S + BitVec.ofNat 32 0x23) 32) < p256 then 1 else 0) := by
    unfold gsMont
    by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x23) 32) < p256
    · obtain ⟨o1, olt, ocg⟩ := ok2 hx
      rw [ite_eq_left hx, ite_eq_left hx]
      exact ⟨frp2_val olt ocg, o1⟩
    · obtain ⟨o0, a0'⟩ := bad2 (Nat.le_of_not_lt hx)
      rw [ite_eq_right hx, ite_eq_right hx]; exact ⟨a0', o0⟩
  clear ok2 bad2
  have h2hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n2.mem x = M x := fun x hx =>
    fr2 x (sep_of_le (by rw [hbF]; omega) (by have := x.isLt; omega)) (F.hiOut (by decide) hx)
  have C2 := C.hi h2hi
  have D2 : P2Data n2.mem := D.of F fun x hx => fr2 x (hx.sub (c := 0x60) (l := 0x140) (by decide) |> fun h => by
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x60 = S + 0xFFFFFEC0 by rw [BitVec.add_assoc]; rfl] at h) (fr_inFrame (by decide) hx)
  obtain ⟨n3, c3, u3⟩ := u2.block gsY2 C2.self gsY2_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock gsY2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, mem4, k4⟩ := c_memset (dst := S + BitVec.ofNat 32 0x1E4) (b := 0) (N := 32)
    (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem GP n3 0x328 (reg n3)) C2.self C2.K.K gs_at_328 gs_at_32c (by decide) (by decide)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gsY2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gsY2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gsY2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [F.at _ (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  have h4 : ∀ x, Sep (S + BitVec.ofNat 32 0x1E4) 32 x 1 → n4.mem x = n2.mem x := fun x hx => by
    rw [mem4, fillBytes_sep hx (Nat.le_refl _)]
  have C4 := C2.hi fun x hx => h4 x (F.hiOut (by decide) hx)
  have k4' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg n4 q = reg n2 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 hr => by
      rw [k4 q h0 h2 h3 h4 h5 h6 hr, r3, runBlock_reg _ _ _ q u2.zero (by simp only [gsY2]; revert h0 h1 h2; revert q; decide)]
  have sp4 : reg n4 sp = S := by
    rw [k4' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp2
  have a70 : n4.mem (S + BitVec.ofNat 32 0x160 + 0x20) = n2.mem (S + BitVec.ofNat 32 0x160 + 0x20) :=
    h4 _ (sepS S (c := 0x1E4) (n := 32) (d := 0x180) (k := 1) (.inr (by decide)) (by decide) (by decide) |> fun h => by
      rwa [show S + BitVec.ofNat 32 0x180 = S + BitVec.ofNat 32 0x160 + 0x20 from by rw [BitVec.add_assoc]; rfl] at h)
  obtain ⟨n5, c5, u5⟩ := u4.block gsY3 C4.self gsY3_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock gsY3 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have e18 : reg n5 (18 : Fin 32) = (n2.mem (S + BitVec.ofNat 32 0x160 + 0x20)).zeroExtend 32 := by
    rw [r5]; simp +decide only [runBlock, BInstr.run, gsY3, upd, ↓reduceIte]; rw [sp4, ← a70]
    rw [show S + BitVec.ofNat 32 0x160 + 0x20 = S + 0x180 from by rw [BitVec.add_assoc]; rfl]
  have hc01 : (n2.mem (S + BitVec.ofNat 32 0x160 + 0x20)).zeroExtend 32 = (0 : Word) ∨
      (n2.mem (S + BitVec.ofNat 32 0x160 + 0x20)).zeroExtend 32 = (1 : Word) := by
    by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x23) 32) < p256
    · rw [hv2.2, ite_eq_left hx]; exact .inr rfl
    · rw [hv2.2, ite_eq_right hx]; exact .inl rfl
  obtain ⟨n6, c6, u6, vals6, fr6, sp6, k6⟩ := c2_csel (out := S + BitVec.ofNat 32 0x244) (a := S + BitVec.ofNat 32 0x1E4)
    (b := S + BitVec.ofNat 32 0x160) (c := (n2.mem (S + BitVec.ofNat 32 0x160 + 0x20)).zeroExtend 32)
    (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem GP n5 0x33C (reg n5)) C4.self C4.K F gs_at_33c gs_at_340 (by decide) (by decide)
    (by rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gsY3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gsY3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gsY3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gsY3, upd, ↓reduceIte]; rw [sp4]
        show aluEval .add 0 ((n4.mem (S + 0x180)).zeroExtend 32) = _
        rw [show (S + 0x180 : Word) = S + BitVec.ofNat 32 0x160 + 0x20 from by rw [BitVec.add_assoc]; rfl, a70]
        exact BitVec.zero_add _)
    hc01 (co := 0x244) (ca := 0x1E4) (cb := 0x160) (by decide) (by decide) (by decide) rfl rfl rfl (by decide)
  have h6hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n6.mem x = M x := fun x hx => by
    rw [fr6 x (sep_of_le (by rw [hb50]; omega) (by have := x.isLt; omega)) (F.hiOut (c := 0x244) (n := 32) (by decide) hx),
      h4 x (F.hiOut (by decide) hx), h2hi x hx]
  have frame : ∀ x, Sep (S + 0xFFFFFEC0) 0x140 x 1 → Sep (S + BitVec.ofNat 32 0x160) 0x21 x 1 →
      Sep (S + BitVec.ofNat 32 0x1E4) 0x20 x 1 → Sep (S + BitVec.ofNat 32 0x244) 0x20 x 1 → n6.mem x = M x := by
    intro x hF h210 h2D4 h364
    have h50 : Sep (S + 0xFFFFFFB0) 0x50 x 1 := by
      have := hF.sub (c := 0xF0) (l := 0x50) (by decide)
      rwa [show S + 0xFFFFFEC0 + BitVec.ofNat 32 0xF0 = S + 0xFFFFFFB0 by rw [BitVec.add_assoc]; rfl] at this
    rw [fr6 x h50 h364, h4 x h2D4, fr2 x hF h210]
  have D6 : P2Data n6.mem := D.of F fun x hx => frame x (hx.sub (c := 0x60) (l := 0x140) (by decide) |> fun h => by
      rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x60 = S + 0xFFFFFEC0 by rw [BitVec.add_assoc]; rfl] at h) (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx)
  have e618 : reg n6 (18 : Fin 32) = (n2.mem (S + BitVec.ofNat 32 0x160 + 0x20)).zeroExtend 32 := by
    rw [k6 18 (by decide), e18]
  refine ⟨n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))), u6, C.hi h6hi, D6, ?_, ?_, frame, sp6, fun q hq => ?_⟩
  · by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x23) 32) < p256
    · have hc1 : (n2.mem (S + BitVec.ofNat 32 0x160 + 0x20)).zeroExtend 32 = (1 : Word) := by
        rw [hv2.2, ite_eq_left hx]; rfl
      rw [← hv2.1]
      exact accV_congr2 8 fun i hi => by
        rw [vals6 i hi, ite_eq_left hc1]
        exact memLoad32_congr fun q hq => by
          rw [add_ofNat_assoc, add_ofNat_assoc]
          exact h4 _ (sepS S (.inr (by omega)) (by decide) (by omega))
    · have hc0 : (n2.mem (S + BitVec.ofNat 32 0x160 + 0x20)).zeroExtend 32 = (0 : Word) := by
        rw [hv2.2, ite_eq_right hx]; rfl
      unfold gsMont; rw [ite_eq_right hx]
      exact accV_zero 8 fun i hi => by
        rw [vals6 i hi, ite_eq_right (by rw [hc0]; decide), mem4]
        exact fill_word0 (by omega) (by decide)
  · rw [e618, hv2.2]; unfold gsOk
    by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x23) 32) < p256
    · rw [ite_eq_left hx, ite_eq_left hx]; rfl
    · rw [ite_eq_right hx, ite_eq_right hx]; rfl
  · rw [k6 q (by revert hq; revert q; decide), r5, runBlock_reg _ _ _ q u4.zero (by simp only [gsY3]; revert hq; revert q; decide),
      k4' q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide), r1,
      runBlock_reg _ _ _ q hz (by simp only [gsY1]; revert hq; revert q; decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **Decoding `x`**, from 0x344 to 0x374: `from_repr` on the 32 bytes at
`S + 0x3`, then the select of its result or zero into `S + 0x284`; `s3`
holds the choice. -/
theorem gs_decX {M : Word → BitVec 8} {n : Machine} {S : Word} (C : GsCode M) (D : P2Data M) (F : Fr S 0x2D0)
    (s : St M GP n 0x344 (reg n)) (rsp : reg n sp = S) (r19 : reg n (19 : Fin 32) = S + BitVec.ofNat 32 0x3) :
    ∃ n', Steps n n' ∧ St n'.mem GP n' 0x374 (reg n') ∧ GsCode n'.mem ∧ P2Data n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x284) 8 = gsMont (beNat (memBytes M (S + BitVec.ofNat 32 0x3) 32)) ∧
      reg n' (19 : Fin 32) = gsOk (beNat (memBytes M (S + BitVec.ofNat 32 0x3) 32)) ∧
      (∀ x, Sep (S + 0xFFFFFEC0) 0x140 x 1 → Sep (S + BitVec.ofNat 32 0xD4) 0x21 x 1 →
        Sep (S + BitVec.ofNat 32 0x204) 0x20 x 1 → Sep (S + BitVec.ofNat 32 0x284) 0x20 x 1 → n'.mem x = M x) ∧
      reg n' sp = S ∧ ∀ q : Fin 32, q.val ∈ [3, 4, 18, 22, 24, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hbF : (S + 0xFFFFFEC0).toNat = S.toNat - 0x140 := F.below 0x140 (by decide) (by decide)
  have hb50 : (S + 0xFFFFFFB0).toNat = S.toNat - 0x50 := F.below 0x50 (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block gsX1 C.self gsX1_end ⟨trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock gsX1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, ok2, bad2, fr2, sp2, k2⟩ := c2_frp (out := S + BitVec.ofNat 32 0xD4)
    (inp := S + BitVec.ofNat 32 0x3) (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M GP n1 0x348 (reg n1)) C.self C.K D F
    gs_at_348 gs_at_34c (by decide) (by decide) (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gsX1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gsX1, upd, ↓reduceIte]; rw [r19]; exact BitVec.zero_add _)
    (co := 0xD4) (by decide) rfl
    ((sep_of_le (by rw [hbF, F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega)).symm)
  have hv2 : accV n2.mem (S + BitVec.ofNat 32 0xD4) 8 = gsMont (beNat (memBytes M (S + BitVec.ofNat 32 0x3) 32)) ∧
      n2.mem (S + BitVec.ofNat 32 0xD4 + 0x20) = (if beNat (memBytes M (S + BitVec.ofNat 32 0x3) 32) < p256 then 1 else 0) := by
    unfold gsMont
    by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x3) 32) < p256
    · obtain ⟨o1, olt, ocg⟩ := ok2 hx
      rw [ite_eq_left hx, ite_eq_left hx]
      exact ⟨frp2_val olt ocg, o1⟩
    · obtain ⟨o0, a0'⟩ := bad2 (Nat.le_of_not_lt hx)
      rw [ite_eq_right hx, ite_eq_right hx]; exact ⟨a0', o0⟩
  clear ok2 bad2
  have h2hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n2.mem x = M x := fun x hx =>
    fr2 x (sep_of_le (by rw [hbF]; omega) (by have := x.isLt; omega)) (F.hiOut (by decide) hx)
  have C2 := C.hi h2hi
  have D2 : P2Data n2.mem := D.of F fun x hx => fr2 x (hx.sub (c := 0x60) (l := 0x140) (by decide) |> fun h => by
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x60 = S + 0xFFFFFEC0 by rw [BitVec.add_assoc]; rfl] at h) (fr_inFrame (by decide) hx)
  obtain ⟨n3, c3, u3⟩ := u2.block gsX2 C2.self gsX2_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock gsX2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, mem4, k4⟩ := c_memset (dst := S + BitVec.ofNat 32 0x204) (b := 0) (N := 32)
    (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem GP n3 0x358 (reg n3)) C2.self C2.K.K gs_at_358 gs_at_35c (by decide) (by decide)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gsX2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gsX2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gsX2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [F.at _ (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  have h4 : ∀ x, Sep (S + BitVec.ofNat 32 0x204) 32 x 1 → n4.mem x = n2.mem x := fun x hx => by
    rw [mem4, fillBytes_sep hx (Nat.le_refl _)]
  have C4 := C2.hi fun x hx => h4 x (F.hiOut (by decide) hx)
  have k4' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg n4 q = reg n2 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 hr => by
      rw [k4 q h0 h2 h3 h4 h5 h6 hr, r3, runBlock_reg _ _ _ q u2.zero (by simp only [gsX2]; revert h0 h1 h2; revert q; decide)]
  have sp4 : reg n4 sp = S := by
    rw [k4' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp2
  have a70 : n4.mem (S + BitVec.ofNat 32 0xD4 + 0x20) = n2.mem (S + BitVec.ofNat 32 0xD4 + 0x20) :=
    h4 _ (sepS S (c := 0x204) (n := 32) (d := 0xF4) (k := 1) (.inr (by decide)) (by decide) (by decide) |> fun h => by
      rwa [show S + BitVec.ofNat 32 0xF4 = S + BitVec.ofNat 32 0xD4 + 0x20 from by rw [BitVec.add_assoc]; rfl] at h)
  obtain ⟨n5, c5, u5⟩ := u4.block gsX3 C4.self gsX3_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock gsX3 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have e19x : reg n5 (19 : Fin 32) = (n2.mem (S + BitVec.ofNat 32 0xD4 + 0x20)).zeroExtend 32 := by
    rw [r5]; simp +decide only [runBlock, BInstr.run, gsX3, upd, ↓reduceIte]; rw [sp4, ← a70]
    rw [show S + BitVec.ofNat 32 0xD4 + 0x20 = S + 0xF4 from by rw [BitVec.add_assoc]; rfl]
  have hc01 : (n2.mem (S + BitVec.ofNat 32 0xD4 + 0x20)).zeroExtend 32 = (0 : Word) ∨
      (n2.mem (S + BitVec.ofNat 32 0xD4 + 0x20)).zeroExtend 32 = (1 : Word) := by
    by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x3) 32) < p256
    · rw [hv2.2, ite_eq_left hx]; exact .inr rfl
    · rw [hv2.2, ite_eq_right hx]; exact .inl rfl
  obtain ⟨n6, c6, u6, vals6, fr6, sp6, k6⟩ := c2_csel (out := S + BitVec.ofNat 32 0x284) (a := S + BitVec.ofNat 32 0x204)
    (b := S + BitVec.ofNat 32 0xD4) (c := (n2.mem (S + BitVec.ofNat 32 0xD4 + 0x20)).zeroExtend 32)
    (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem GP n5 0x36C (reg n5)) C4.self C4.K F gs_at_36c gs_at_370 (by decide) (by decide)
    (by rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gsX3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gsX3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gsX3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gsX3, upd, ↓reduceIte]; rw [sp4]
        show aluEval .add 0 ((n4.mem (S + 0xF4)).zeroExtend 32) = _
        rw [show (S + 0xF4 : Word) = S + BitVec.ofNat 32 0xD4 + 0x20 from by rw [BitVec.add_assoc]; rfl, a70]
        exact BitVec.zero_add _)
    hc01 (co := 0x284) (ca := 0x204) (cb := 0xD4) (by decide) (by decide) (by decide) rfl rfl rfl (by decide)
  have h6hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n6.mem x = M x := fun x hx => by
    rw [fr6 x (sep_of_le (by rw [hb50]; omega) (by have := x.isLt; omega)) (F.hiOut (c := 0x284) (n := 32) (by decide) hx),
      h4 x (F.hiOut (by decide) hx), h2hi x hx]
  have frame : ∀ x, Sep (S + 0xFFFFFEC0) 0x140 x 1 → Sep (S + BitVec.ofNat 32 0xD4) 0x21 x 1 →
      Sep (S + BitVec.ofNat 32 0x204) 0x20 x 1 → Sep (S + BitVec.ofNat 32 0x284) 0x20 x 1 → n6.mem x = M x := by
    intro x hF h210 h2D4 h364
    have h50 : Sep (S + 0xFFFFFFB0) 0x50 x 1 := by
      have := hF.sub (c := 0xF0) (l := 0x50) (by decide)
      rwa [show S + 0xFFFFFEC0 + BitVec.ofNat 32 0xF0 = S + 0xFFFFFFB0 by rw [BitVec.add_assoc]; rfl] at this
    rw [fr6 x h50 h364, h4 x h2D4, fr2 x hF h210]
  have D6 : P2Data n6.mem := D.of F fun x hx => frame x (hx.sub (c := 0x60) (l := 0x140) (by decide) |> fun h => by
      rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x60 = S + 0xFFFFFEC0 by rw [BitVec.add_assoc]; rfl] at h) (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx)
  have e619 : reg n6 (19 : Fin 32) = (n2.mem (S + BitVec.ofNat 32 0xD4 + 0x20)).zeroExtend 32 := by
    rw [k6 19 (by decide), e19x]
  refine ⟨n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))), u6, C.hi h6hi, D6, ?_, ?_, frame, sp6, fun q hq => ?_⟩
  · by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x3) 32) < p256
    · have hc1 : (n2.mem (S + BitVec.ofNat 32 0xD4 + 0x20)).zeroExtend 32 = (1 : Word) := by
        rw [hv2.2, ite_eq_left hx]; rfl
      rw [← hv2.1]
      exact accV_congr2 8 fun i hi => by
        rw [vals6 i hi, ite_eq_left hc1]
        exact memLoad32_congr fun q hq => by
          rw [add_ofNat_assoc, add_ofNat_assoc]
          exact h4 _ (sepS S (.inr (by omega)) (by decide) (by omega))
    · have hc0 : (n2.mem (S + BitVec.ofNat 32 0xD4 + 0x20)).zeroExtend 32 = (0 : Word) := by
        rw [hv2.2, ite_eq_right hx]; rfl
      unfold gsMont; rw [ite_eq_right hx]
      exact accV_zero 8 fun i hi => by
        rw [vals6 i hi, ite_eq_right (by rw [hc0]; decide), mem4]
        exact fill_word0 (by omega) (by decide)
  · rw [e619, hv2.2]; unfold gsOk
    by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x3) 32) < p256
    · rw [ite_eq_left hx, ite_eq_left hx]; rfl
    · rw [ite_eq_right hx, ite_eq_right hx]; rfl
  · rw [k6 q (by revert hq; revert q; decide), r5, runBlock_reg _ _ _ q u4.zero (by simp only [gsX3]; revert hq; revert q; decide),
      k4' q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide), r1,
      runBlock_reg _ _ _ q hz (by simp only [gsX1]; revert hq; revert q; decide)]

