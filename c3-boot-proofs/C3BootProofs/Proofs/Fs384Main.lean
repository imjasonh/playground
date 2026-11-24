import C3BootProofs.Proofs.P3Lib
import C3BootProofs.Proofs.Fs384At

/-!
# `VerifyingKey<NistP384>::from_sec1_bytes`

The compiled `from_sec1_bytes` takes 97 bytes and checks them as an
uncompressed SEC1 point: tag 4, then `x` and `y` below `p` with
`y² = x³ + ax + b`. Its length check (`Tag::message_len` must be 97) leaves
the compressed and identity branches unreachable.
-/

namespace C3.RV32.Fs

open C3.Image C3.RV32.Dq C3.RV32.P3

set_option maxRecDepth 20000

/-- `from_sec1_bytes`'s code and its callees'. -/
structure FsCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M FP p384FromSec1Code
  K : P3Code M

theorem FsCode.hi {M M' : Word → BitVec 8} (C : FsCode M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    FsCode M' := ⟨codeHi C.self (by decide) (by decide) h, C.K.hi h⟩

def fsA1 : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFBE0, .aluImm .add a2 sp 0x400, .sw a2 ra 0x1C, .sw a2 (8 : Fin 32) 0x18,
   .sw a2 (9 : Fin 32) 0x14, .sw a2 (18 : Fin 32) 0x10, .sw a2 (19 : Fin 32) 0xC, .sw a2 (20 : Fin 32) 0x8,
   .sw a2 (21 : Fin 32) 0x4, .sw a2 (22 : Fin 32) 0x0, .aluImm .add a2 sp 0x380, .sw a2 (23 : Fin 32) 0x7C,
   .sw a2 (24 : Fin 32) 0x78, .sw a2 (25 : Fin 32) 0x74, .alu .add (9 : Fin 32) x0 a1, .alu .add (24 : Fin 32) x0 a0]
def fsA2 : List BInstr :=
  [.lbu a0 a1 0x0, .aluImm .add (8 : Fin 32) x0 0xFFFFFFFF, .sw sp (8 : Fin 32) 0x144, .sb sp a0 0x148,
   .aluImm .add a0 sp 0xDC, .aluImm .add a1 sp 0x144]

theorem fsA1_end : blockEnd p384FromSec1Code 0 fsA1 = some 0x36 := by decide
theorem fsA2_end : blockEnd p384FromSec1Code 0x36 fsA2 = some 0x48 := by decide

/-- The prologue's saves of `ra` and `s0..s9`, in order. -/
def fsSaves (M : Word → BitVec 8) (S : Word) (n : Machine) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (S + BitVec.ofNat 32 0x41c) (reg n ra)) (S + BitVec.ofNat 32 0x418) (reg n (8 : Fin 32))) (S + BitVec.ofNat 32 0x414) (reg n (9 : Fin 32))) (S + BitVec.ofNat 32 0x410) (reg n (18 : Fin 32))) (S + BitVec.ofNat 32 0x40c) (reg n (19 : Fin 32))) (S + BitVec.ofNat 32 0x408) (reg n (20 : Fin 32))) (S + BitVec.ofNat 32 0x404) (reg n (21 : Fin 32))) (S + BitVec.ofNat 32 0x400) (reg n (22 : Fin 32))) (S + BitVec.ofNat 32 0x3fc) (reg n (23 : Fin 32))) (S + BitVec.ofNat 32 0x3f8) (reg n (24 : Fin 32))) (S + BitVec.ofNat 32 0x3f4) (reg n (25 : Fin 32))

theorem fsSaves_out {M : Word → BitVec 8} {S : Word} {n : Machine} {x : Word}
    (h : Sep (S + BitVec.ofNat 32 0x3F4) 0x2C x 1) : fsSaves M S n x = M x := by
  have hs : ∀ c, 0x3F4 ≤ c → c + 4 ≤ 0x420 → Sep (S + BitVec.ofNat 32 c) 4 x 1 := fun c h1 h2 => by
    have := h.sub (c := c - 0x3F4) (l := 4) (by omega)
    rwa [add_ofNat_assoc, show 0x3F4 + (c - 0x3F4) = c by omega] at this
  unfold fsSaves
  rw [memStore32_get_sep (hs 0x3f4 (by decide) (by decide)), memStore32_get_sep (hs 0x3f8 (by decide) (by decide)),
    memStore32_get_sep (hs 0x3fc (by decide) (by decide)), memStore32_get_sep (hs 0x400 (by decide) (by decide)),
    memStore32_get_sep (hs 0x404 (by decide) (by decide)), memStore32_get_sep (hs 0x408 (by decide) (by decide)),
    memStore32_get_sep (hs 0x40c (by decide) (by decide)), memStore32_get_sep (hs 0x410 (by decide) (by decide)),
    memStore32_get_sep (hs 0x414 (by decide) (by decide)), memStore32_get_sep (hs 0x418 (by decide) (by decide)),
    memStore32_get_sep (hs 0x41c (by decide) (by decide))]

theorem ze_ex : ∀ b : BitVec 8, (b.zeroExtend 32).extractLsb' 0 8 = b := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The prologue**, from the entry to the call at 0x48: save `ra` and
`s0..s9`, open the frame at `S`, and store `Ok(b₀)` for the first input byte
`b₀` at `S + 0x144`. -/
theorem fs_pro {M : Word → BitVec 8} {n : Machine} {S inp out : Word} (C : FsCode M) (F : Fr S 0x420)
    (s : St M FP n 0 (reg n)) (rsp : reg n sp = S + 0x420) (ra0 : reg n a0 = out) (ra1 : reg n a1 = inp)
    (sI : Sep (S + BitVec.ofNat 32 0x3F4) 0x2C inp 1) :
    ∃ n', Steps n n' ∧
      St (memStore8 (memStore32 (fsSaves M S n) (S + BitVec.ofNat 32 0x144) 0xFFFFFFFF) (S + BitVec.ofNat 32 0x148)
        (M inp)) FP n' 0x48 (reg n') ∧
      reg n' sp = S ∧ reg n' (9 : Fin 32) = inp ∧ reg n' (24 : Fin 32) = out ∧ reg n' (8 : Fin 32) = 0xFFFFFFFF ∧
      reg n' a0 = S + BitVec.ofNat 32 0xDC ∧ reg n' a1 = S + BitVec.ofNat 32 0x144 ∧
      ∀ q, q.val ∈ [3, 4, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hA : aluEval .add (aluEval .add (S + 0x420) 0xFFFFFBE0) 0x400 = S + BitVec.ofNat 32 0x400 := by
    show S + 0x420 + 0xFFFFFBE0 + 0x400 = S + BitVec.ofNat 32 0x400
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have hB : aluEval .add (aluEval .add (S + 0x420) 0xFFFFFBE0) 0x380 = S + BitVec.ofNat 32 0x380 := by
    show S + 0x420 + 0xFFFFFBE0 + 0x380 = S + BitVec.ofNat 32 0x380
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have hS : aluEval .add (S + 0x420) 0xFFFFFBE0 = S := by
    show S + 0x420 + 0xFFFFFBE0 = S
    rw [BitVec.add_assoc]; exact BitVec.add_zero S
  have alB : ∀ (c : Nat) (k : Word), c + k.toNat + 4 ≤ 0x420 → (c + k.toNat) % 4 = 0 →
      (S + BitVec.ofNat 32 c + k).toNat % 4 = 0 := fun c k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  have sepB : ∀ (c : Nat) (k : Word), c + k.toNat + 4 ≤ 0x420 →
      Sep (S + BitVec.ofNat 32 c + k) 4 FP p384FromSec1Code.length := fun c k h1 => by
    rw [frame_lit k (by omega)]; exact F.sepHi (by omega) (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block fsA1 C.self fsA1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, fsA1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp, hA, hB]
    exact ⟨⟨alB 0x400 0x1C (by decide) (by decide), sepB 0x400 0x1C (by decide)⟩,
      ⟨alB 0x400 0x18 (by decide) (by decide), sepB 0x400 0x18 (by decide)⟩,
      ⟨alB 0x400 0x14 (by decide) (by decide), sepB 0x400 0x14 (by decide)⟩,
      ⟨alB 0x400 0x10 (by decide) (by decide), sepB 0x400 0x10 (by decide)⟩,
      ⟨alB 0x400 0xC (by decide) (by decide), sepB 0x400 0xC (by decide)⟩,
      ⟨alB 0x400 0x8 (by decide) (by decide), sepB 0x400 0x8 (by decide)⟩,
      ⟨alB 0x400 0x4 (by decide) (by decide), sepB 0x400 0x4 (by decide)⟩,
      ⟨alB 0x400 0x0 (by decide) (by decide), sepB 0x400 0x0 (by decide)⟩,
      ⟨alB 0x380 0x7C (by decide) (by decide), sepB 0x380 0x7C (by decide)⟩,
      ⟨alB 0x380 0x78 (by decide) (by decide), sepB 0x380 0x78 (by decide)⟩,
      ⟨alB 0x380 0x74 (by decide) (by decide), sepB 0x380 0x74 (by decide)⟩⟩)
  have m1 : n1.mem = fsSaves M S n := by
    rw [u1.mem]; simp only [runBlock, BInstr.run, fsA1]; simp +decide only [upd, ↓reduceIte]
    rw [rsp, hA, hB]
    simp (disch := decide) only [frame_lit]
    rfl
  have r1 : ∀ q, reg n1 q = (runBlock fsA1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have sp1 : reg n1 sp = S := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, fsA1, upd, ↓reduceIte]; rw [rsp]; exact hS
  have e19 : reg n1 (9 : Fin 32) = inp := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, fsA1, upd, ↓reduceIte]; rw [ra1]; exact BitVec.zero_add _
  have e124 : reg n1 (24 : Fin 32) = out := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, fsA1, upd, ↓reduceIte]; rw [ra0]; exact BitVec.zero_add _
  have e1a1 : reg n1 a1 = inp := by rw [r1, runBlock_reg _ _ _ a1 hz (by decide)]; exact ra1
  have hb0 : fsSaves M S n inp = M inp := fsSaves_out sI
  have C1 : FsCode (fsSaves M S n) := C.hi fun x hx => fsSaves_out (F.hiOut (by decide) hx)
  have t1 : St (fsSaves M S n) FP n1 0x36 (reg n1) := ⟨u1.pc, m1, fun _ => rfl⟩
  obtain ⟨n2, c2, u2⟩ := t1.block fsA2 C1.self fsA2_end (by
      simp only [BlockOk, BInstr.ok, BInstr.run, fsA2]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
      rw [sp1]
      exact ⟨⟨by show (S + BitVec.ofNat 32 0x144).toNat % 4 = 0; rw [F.at _ (by decide)]; omega,
        F.sepHi (by decide) (by decide) (by decide)⟩,
        F.sepHi (by decide) (by decide) (by decide)⟩)
  have r2 : ∀ q, reg n2 q = (runBlock fsA2 (fsSaves M S n, reg n1)).2 q := fun q => by rw [u2.regs]
  have m2 : n2.mem = memStore8 (memStore32 (fsSaves M S n) (S + BitVec.ofNat 32 0x144) 0xFFFFFFFF)
      (S + BitVec.ofNat 32 0x148) (M inp) := by
    rw [u2.mem]; simp only [runBlock, BInstr.run, fsA2]; simp +decide only [upd, ↓reduceIte]
    rw [sp1, e1a1, show inp + (0 : Word) = inp from BitVec.add_zero inp, hb0, ze_ex]; rfl
  refine ⟨n2, c1.trans c2, ⟨u2.pc, m2, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [r2, runBlock_reg _ _ _ sp t1.zero (by decide)]; exact sp1
  · rw [r2, runBlock_reg _ _ _ 9 t1.zero (by decide)]; exact e19
  · rw [r2, runBlock_reg _ _ _ 24 t1.zero (by decide)]; exact e124
  · rw [r2]; simp +decide only [runBlock, BInstr.run, fsA2, upd, ↓reduceIte]; (try rw [t1.zero]); try rfl
  · rw [r2]; simp +decide only [runBlock, BInstr.run, fsA2, upd, ↓reduceIte]; rw [sp1]; rfl
  · rw [r2]; simp +decide only [runBlock, BInstr.run, fsA2, upd, ↓reduceIte]; rw [sp1]; rfl
  · rw [r2, runBlock_reg _ _ _ q t1.zero (by simp only [fsA2]; revert hq; revert q; decide), r1,
      runBlock_reg _ _ _ q hz (by simp only [fsA1]; revert hq; revert q; decide)]

def fsE : List BInstr :=
  [.sw (24 : Fin 32) a0 0x0, .aluImm .add a0 sp 0x400, .lw ra a0 0x1C, .lw (8 : Fin 32) a0 0x18, .lw (9 : Fin 32) a0 0x14,
   .lw (18 : Fin 32) a0 0x10, .lw (19 : Fin 32) a0 0xC, .lw (20 : Fin 32) a0 0x8, .lw (21 : Fin 32) a0 0x4,
   .lw (22 : Fin 32) a0 0x0, .aluImm .add a0 sp 0x380, .lw (23 : Fin 32) a0 0x7C, .lw (24 : Fin 32) a0 0x78,
   .lw (25 : Fin 32) a0 0x74, .aluImm .add sp sp 0x420]

theorem fsE_end : blockEnd p384FromSec1Code 0x44C fsE = some 0x482 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The epilogue**, from 0x44C: store the result word `v` at `out`,
restore `ra` and `s0..s9`, and return. -/
theorem fs_epi {M : Word → BitVec 8} {n : Machine} {S out v : Word} {w : Nat → Word} (C : FsCode M)
    (F : Fr S 0x420) (s : St M FP n 0x44C (reg n)) (rsp : reg n sp = S) (r24 : reg n (24 : Fin 32) = out)
    (ra0 : reg n a0 = v) (hoa : out.toNat % 4 = 0) (hoh : out.toNat + 4 ≤ 0x40000000)
    (hos : Sep out 4 (S + BitVec.ofNat 32 0x3F4) 0x2C)
    (hS : ∀ k, k < 11 → memLoad32 M (S + BitVec.ofNat 32 (0x41C - 4 * k)) = w k) (hret : w 0 &&& ~~~1 = w 0) :
    ∃ n', Steps n n' ∧ n'.pc = w 0 ∧ reg n' sp = S + 0x420 ∧ (∀ k, k < 11 → reg n' (savedReg k) = w k) ∧
      n'.mem = memStore32 M out v ∧ ∀ q, q.val ∈ [3, 4, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hA : aluEval .add S 0x400 = S + BitVec.ofNat 32 0x400 := rfl
  have hB : aluEval .add S 0x380 = S + BitVec.ofNat 32 0x380 := rfl
  have alB : ∀ (c : Nat) (k : Word), c + k.toNat + 4 ≤ 0x420 → (c + k.toNat) % 4 = 0 →
      (S + BitVec.ofNat 32 c + k).toNat % 4 = 0 := fun c k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  have o0 : out + (0 : Word) = out := BitVec.add_zero out
  have hoc : Sep out 4 FP p384FromSec1Code.length := by
    have : 0x40000000 ≤ FP.toNat := by decide
    exact sep_of_le (by omega) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block fsE C.self fsE_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, fsE]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp, hA, hB, r24, o0]
    exact ⟨⟨hoa, hoc⟩, alB 0x400 0x1C (by decide) (by decide), alB 0x400 0x18 (by decide) (by decide),
      alB 0x400 0x14 (by decide) (by decide), alB 0x400 0x10 (by decide) (by decide),
      alB 0x400 0xC (by decide) (by decide), alB 0x400 0x8 (by decide) (by decide),
      alB 0x400 0x4 (by decide) (by decide), alB 0x400 0x0 (by decide) (by decide),
      alB 0x380 0x7C (by decide) (by decide), alB 0x380 0x78 (by decide) (by decide),
      alB 0x380 0x74 (by decide) (by decide)⟩)
  have m1 : (runBlock fsE (M, reg n)).1 = memStore32 M out v := by
    simp only [runBlock, BInstr.run, fsE]; rw [r24, o0, ra0]
  have ld9 : ∀ d, 0x3F4 ≤ d → d + 4 ≤ 0x420 → memLoad32 (memStore32 M (reg n (24 : Fin 32) + 0) (reg n a0))
      (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) := fun d h1 h2 => by
    rw [r24, o0]
    exact memLoad32_store32_sep (by
      have := hos.subR (c := d - 0x3F4) (l := 4) (by omega)
      rwa [add_ofNat_assoc, show 0x3F4 + (d - 0x3F4) = d by omega] at this)
  have C1 : FsCode (runBlock fsE (M, reg n)).1 := by
    rw [m1]; exact C.hi fun x hx => memStore32_get_sep (sep_of_le (by omega) (by have := x.isLt; omega))
  obtain ⟨n2, st2, pc2, mem2, regs2⟩ := u1.jalr C1.self fs_at_482
  refine ⟨n2, c1.trans (.single st2), ?_, ?_, ?_, by rw [mem2, m1], fun q hq => ?_⟩
  · rw [pc2]
    simp +decide only [runBlock, BInstr.run, fsE, upd, ↓reduceIte]
    rw [rsp, hA, frame_lit _ (by decide), ld9 _ (by decide) (by decide)]
    exact (congrArg (· &&& ~~~1) (BitVec.add_zero _)).trans (by rw [show (0x400 + (0x1C : Word).toNat) = 0x41C - 4 * 0 from rfl, hS 0 (by decide)]; exact hret)
  · rw [regs2]; simp +decide only [runBlock, BInstr.run, fsE, upd, ↓reduceIte]; rw [rsp]
    show S + 0x420 = S + 0x420; rfl
  · intro k hk
    rw [regs2]
    match k, hk with
    | 0, _ =>
      simp +decide only [runBlock, BInstr.run, fsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 0 (by decide)
    | 1, _ =>
      simp +decide only [runBlock, BInstr.run, fsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 1 (by decide)
    | 2, _ =>
      simp +decide only [runBlock, BInstr.run, fsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 2 (by decide)
    | 3, _ =>
      simp +decide only [runBlock, BInstr.run, fsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 3 (by decide)
    | 4, _ =>
      simp +decide only [runBlock, BInstr.run, fsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 4 (by decide)
    | 5, _ =>
      simp +decide only [runBlock, BInstr.run, fsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 5 (by decide)
    | 6, _ =>
      simp +decide only [runBlock, BInstr.run, fsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 6 (by decide)
    | 7, _ =>
      simp +decide only [runBlock, BInstr.run, fsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 7 (by decide)
    | 8, _ =>
      simp +decide only [runBlock, BInstr.run, fsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 8 (by decide)
    | 9, _ =>
      simp +decide only [runBlock, BInstr.run, fsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 9 (by decide)
    | 10, _ =>
      simp +decide only [runBlock, BInstr.run, fsE, upd, ↓reduceIte, savedReg]
      rw [rsp]; (try rw [hA]); (try rw [hB]); rw [frame_lit _ (by decide), ld9 _ (by decide) (by decide)]; exact hS 10 (by decide)
    | _ + 11, h => exact absurd h (by omega)
  · rw [regs2, runBlock_reg _ _ _ q hz (by simp only [fsE]; revert hq; revert q; decide)]

/-- The memory after the prologue: the saves, and `Ok(b₀)` at `S + 0x144`. -/
def fsM2 (M : Word → BitVec 8) (S : Word) (n : Machine) (b : BitVec 8) : Word → BitVec 8 :=
  memStore8 (memStore32 (fsSaves M S n) (S + BitVec.ofNat 32 0x144) 0xFFFFFFFF) (S + BitVec.ofNat 32 0x148) b

def fsA3 : List BInstr := [.lw a0 sp 0xDC]
theorem fsA3_end : blockEnd p384FromSec1Code 0x50 fsA3 = some 0x52 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **Reading the tag**, from the entry to 0x52: the prologue, and
`Tag::from_u8` on the first input byte through `Result::and_then`, whose
`Result<Tag, Error>` is at `S + 0xDC`; `a0` holds its first word. -/
theorem fs_stA {M : Word → BitVec 8} {n : Machine} {S inp out : Word} (C : FsCode M) (F : Fr S 0x420)
    (s : St M FP n 0 (reg n)) (rsp : reg n sp = S + 0x420) (ra0 : reg n a0 = out) (ra1 : reg n a1 = inp)
    (sI : Sep (S + BitVec.ofNat 32 0x3F4) 0x2C inp 1) :
    ∃ n', Steps n n' ∧
      St (tagFromU8Mem (fsM2 M S n (M inp)) (S + BitVec.ofNat 32 0xDC) ((M inp).zeroExtend 32)) FP n' 0x52 (reg n') ∧
      reg n' a0 = memLoad32 (tagFromU8Mem (fsM2 M S n (M inp)) (S + BitVec.ofNat 32 0xDC) ((M inp).zeroExtend 32))
        (S + BitVec.ofNat 32 0xDC) ∧
      reg n' sp = S ∧ reg n' (9 : Fin 32) = inp ∧ reg n' (24 : Fin 32) = out ∧ reg n' (8 : Fin 32) = 0xFFFFFFFF ∧
      ∀ q, q.val ∈ [3, 4, 26, 27] → reg n' q = reg n q := by
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨n1, c1, u1, sp1, e19, e124, e18, ea0, ea1, k1⟩ := fs_pro C F s rsp ra0 ra1 sI
  replace u1 : St (fsM2 M S n (M inp)) FP n1 0x48 (reg n1) := u1
  have hfr : ∀ x : Word, 0x40000000 ≤ x.toNat → fsM2 M S n (M inp) x = M x := fun x hx => by
    unfold fsM2
    rw [dq_st8 (F.hiOut (by decide) hx), memStore32_get_sep (F.hiOut (by decide) hx),
      fsSaves_out (F.hiOut (by decide) hx)]
  have C1 : FsCode (fsM2 M S n (M inp)) := C.hi hfr
  have hok : memLoad32 (fsM2 M S n (M inp)) (S + BitVec.ofNat 32 0x144) = 0xFFFFFFFF := by
    unfold fsM2
    rw [memLoad32_store8_sep (sepS S (.inr (by decide)) (by decide) (by decide)), memLoad32_store32_same]
  have hb : fsM2 M S n (M inp) (S + BitVec.ofNat 32 0x144 + 4) = M inp := by
    unfold fsM2
    rw [show S + BitVec.ofNat 32 0x144 + 4 = S + BitVec.ofNat 32 0x148 by rw [BitVec.add_assoc]; rfl]
    exact memStore8_same _ _ _
  obtain ⟨n2, c2, u2, m2, sp2, k2⟩ := c_tat (out := S + BitVec.ofNat 32 0xDC) (rp := S + BitVec.ofNat 32 0x144)
    (co := 0xDC) (cr := 0x144) u1 C1.self C1.K F fs_at_48 fs_at_4c (by decide) (by decide) sp1 ea0 ea1
    (by decide) (by decide) rfl rfl (by decide) (by decide) (.inl (by decide)) hok
  rw [hb] at m2
  have h2 : ∀ x : Word, 0x40000000 ≤ x.toNat → n2.mem x = fsM2 M S n (M inp) x := fun x hx => by
    rw [m2]; unfold tagFromU8Mem; split
    · rw [memStore32_get_sep (F.hiOut (by decide) hx), dq_st8 (by
        rw [show S + BitVec.ofNat 32 0xDC + 4 = S + BitVec.ofNat 32 0xE0 by rw [BitVec.add_assoc]; rfl]
        exact F.hiOut (by decide) hx)]
    · rw [memStore32_get_sep (F.hiOut (by decide) hx)]
  have C2 := C1.hi h2
  obtain ⟨n3, c3, u3⟩ := (⟨u2.pc, m2, fun _ => rfl⟩ : St (tagFromU8Mem (fsM2 M S n (M inp)) (S + BitVec.ofNat 32 0xDC)
      ((M inp).zeroExtend 32)) FP n2 0x50 (reg n2)).block fsA3 (by rw [← m2]; exact C2.self) fsA3_end (by
    simp only [BlockOk, BInstr.ok, fsA3]; simp +decide only [and_true]
    rw [sp2]; show (S + BitVec.ofNat 32 0xDC).toNat % 4 = 0; rw [F.at _ (by decide)]; omega)
  have r3 : ∀ q, q ≠ a0 → reg n3 q = reg n2 q := fun q hq => by
    rw [u3.regs]; simp only [runBlock, BInstr.run, fsA3]; exact updz u2.zero hq
  refine ⟨n3, c1.trans (c2.trans c3), ⟨u3.pc, u3.mem, fun _ => rfl⟩, ?_, by rw [r3 sp (by decide)]; exact sp2,
    by rw [r3 9 (by decide), k2 9 (by decide)]; exact e19, by rw [r3 24 (by decide), k2 24 (by decide)]; exact e124,
    by rw [r3 8 (by decide), k2 8 (by decide)]; exact e18, fun q hq => ?_⟩
  · rw [u3.regs]; simp +decide only [runBlock, BInstr.run, fsA3, upd, ↓reduceIte]; rw [sp2]; rfl
  · rw [r3 q (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide), k1 q hq]

/-- What a return from `from_sec1_bytes` keeps: the return address, `sp`,
the saved and untouched registers, and memory outside the frame and the
68-byte result at `out`. -/
def FsRet (M : Word → BitVec 8) (n : Machine) (S out : Word) (n' : Machine) : Prop :=
  n'.pc = reg n ra ∧ reg n' sp = S + 0x420 ∧ (∀ k, k < 11 → reg n' (savedReg k) = reg n (savedReg k)) ∧
    (∀ q : Fin 32, q.val ∈ [3, 4, 26, 27] → reg n' q = reg n q) ∧
    ∀ x, Sep (S + 0xFFFFFE60) 0x5C0 x 1 → Sep out 0x68 x 1 → n'.mem x = M x

def fsErr : List BInstr := [.aluImm .add a0 x0 0x1]
theorem fsErr_end : blockEnd p384FromSec1Code 0x44A fsErr = some 0x44C := by decide

theorem fr_inFrame {S : Word} {N : Nat} {c l : Nat} {x : Word} (h : c + l ≤ N)
    (hx : Sep (S + 0xFFFFFE60) (N + 0x1A0) x 1) : Sep (S + BitVec.ofNat 32 c) l x 1 := by
  have := hx.sub (c := 0x1A0 + c) (l := l) (by omega)
  rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
    omega] at this


theorem fsSaves_read {M : Word → BitVec 8} {S : Word} {n : Machine} :
    ∀ k, k < 11 → memLoad32 (fsSaves M S n) (S + BitVec.ofNat 32 (0x41C - 4 * k)) = reg n (savedReg k) := by
  intro k hk
  match k, hk with
  | 0, _ => unfold fsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 1, _ => unfold fsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 2, _ => unfold fsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 3, _ => unfold fsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 4, _ => unfold fsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 5, _ => unfold fsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 6, _ => unfold fsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 7, _ => unfold fsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 8, _ => unfold fsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 9, _ => unfold fsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 10, _ => unfold fsSaves; rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | _ + 11, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **Returning an error**, from 0x44A: the result word 1 at `out`. -/
theorem fs_err {M Mx : Word → BitVec 8} {n nx : Machine} {S out : Word} (C : FsCode Mx) (F : Fr S 0x420)
    (s : St Mx FP nx 0x44A (reg nx)) (rsp : reg nx sp = S) (r24 : reg nx (24 : Fin 32) = out)
    (hoa : out.toNat % 4 = 0) (hO : out.toNat + 0x68 ≤ 0x40000000) (sO : Sep out 0x68 (S + 0xFFFFFE60) 0x5C0)
    (hS : ∀ k, k < 11 → memLoad32 Mx (S + BitVec.ofNat 32 (0x41C - 4 * k)) = reg n (savedReg k))
    (hret : reg n ra &&& ~~~1 = reg n ra) (k3 : ∀ q : Fin 32, q.val ∈ [3, 4, 26, 27] → reg nx q = reg n q)
    (hM : ∀ x, Sep (S + 0xFFFFFE60) 0x5C0 x 1 → Mx x = M x) :
    ∃ n', Steps nx n' ∧ FsRet M n S out n' ∧ memLoad32 n'.mem out = 1 := by
  obtain ⟨n1, c1, u1⟩ := s.block fsErr C.self fsErr_end ⟨trivial, trivial⟩
  have r1 : ∀ q, q ≠ a0 → reg n1 q = reg nx q := fun q hq => by
    rw [u1.regs]; simp only [runBlock, BInstr.run, fsErr]; exact updz s.zero hq
  have hos : Sep out 4 (S + BitVec.ofNat 32 0x3F4) 0x2C := by
    have := (sO.sub (c := 0) (l := 4) (by decide)).subR (c := 0x1A0 + 0x3F4) (l := 0x2C) (by decide)
    rwa [add_ofNat_zero, BitVec.add_assoc,
      show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x3F4) = BitVec.ofNat 32 0x3F4 from rfl] at this
  obtain ⟨n2, c2, pc2, sp2, sv2, m2, k2⟩ := fs_epi (v := 1) C F ⟨u1.pc, u1.mem, fun _ => rfl⟩
    (by rw [r1 sp (by decide)]; exact rsp) (by rw [r1 24 (by decide)]; exact r24)
    (by rw [u1.regs]; simp +decide only [runBlock, BInstr.run, fsErr, upd, ↓reduceIte]; rw [s.zero]; rfl)
    hoa (by omega) hos hS hret
  refine ⟨n2, c1.trans c2, ⟨pc2, sp2, sv2, fun q hq => ?_, fun x hx ho => ?_⟩, by rw [m2]; exact memLoad32_store32_same _ _ _⟩
  · rw [k2 q hq, r1 q (by revert hq; revert q; decide), k3 q hq]
  · rw [m2, memStore32_get_sep ((ho.sub (c := 0) (l := 4) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h)]
    exact hM x hx

/-- The memory after `and_then(Tag::from_u8)`. -/
def fsM3 (M : Word → BitVec 8) (S : Word) (n : Machine) (b : BitVec 8) : Word → BitVec 8 :=
  tagFromU8Mem (fsM2 M S n b) (S + BitVec.ofNat 32 0xDC) (b.zeroExtend 32)

theorem zext8_toNat (b : BitVec 8) : (b.zeroExtend 32 : Word).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

theorem zext8_inj {b c : BitVec 8} : (b.zeroExtend 32 : Word) = c.zeroExtend 32 ↔ b = c :=
  ⟨fun h => BitVec.eq_of_toNat_eq (by rw [← zext8_toNat b, ← zext8_toNat c, h]), fun h => by rw [h]⟩

theorem fsM3_keep {M : Word → BitVec 8} {S : Word} {n : Machine} {b : BitVec 8} {x : Word}
    (h : Sep (S + BitVec.ofNat 32 0xDC) 0x70 x 1) : fsM3 M S n b x = fsSaves M S n x := by
  have s1 : Sep (S + BitVec.ofNat 32 0xDC) 4 x 1 := by
    have := h.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have s2 : Sep (S + BitVec.ofNat 32 0xDC + 4) 1 x 1 := by
    have := h.sub (c := 4) (l := 1) (by decide); rwa [show (4 : Word) = BitVec.ofNat 32 4 from rfl]
  have s3 : Sep (S + BitVec.ofNat 32 0x144) 4 x 1 := by
    have := h.sub (c := 0x68) (l := 4) (by decide); rwa [add_ofNat_assoc] at this
  have s4 : Sep (S + BitVec.ofNat 32 0x148) 1 x 1 := by
    have := h.sub (c := 0x6C) (l := 1) (by decide); rwa [add_ofNat_assoc] at this
  unfold fsM3 tagFromU8Mem fsM2; split
  · rw [memStore32_get_sep s1, dq_st8 s2, dq_st8 s4, memStore32_get_sep s3]
  · rw [memStore32_get_sep s1, dq_st8 s4, memStore32_get_sep s3]

theorem fsM3_word {M : Word → BitVec 8} {S : Word} {n : Machine} {b : BitVec 8} :
    memLoad32 (fsM3 M S n b) (S + BitVec.ofNat 32 0xDC) = if Sec1TagOk b then 0xFFFFFFFF else 3 := by
  unfold fsM3 tagFromU8Mem
  by_cases h : Sec1TagOk b
  · rw [ite_eq_left (show (b.zeroExtend 32 : Word).toNat ≤ 5 ∧ (b.zeroExtend 32 : Word).toNat ≠ 1 by
      rw [zext8_toNat]; exact h), ite_eq_left h, memLoad32_store32_same]
  · rw [ite_eq_right (show ¬((b.zeroExtend 32 : Word).toNat ≤ 5 ∧ (b.zeroExtend 32 : Word).toNat ≠ 1) by
      rw [zext8_toNat]; exact h), ite_eq_right h, memLoad32_store32_same]

theorem fsM3_tag {M : Word → BitVec 8} {S : Word} {n : Machine} {b : BitVec 8} (h : Sec1TagOk b) :
    fsM3 M S n b (S + BitVec.ofNat 32 0xE0) = b := by
  unfold fsM3 tagFromU8Mem
  rw [ite_eq_left (show (b.zeroExtend 32 : Word).toNat ≤ 5 ∧ (b.zeroExtend 32 : Word).toNat ≠ 1 by
      rw [zext8_toNat]; exact h), memStore32_get_sep (sepS S (.inl (by decide)) (by decide) (by decide)),
    show S + BitVec.ofNat 32 0xE0 = S + BitVec.ofNat 32 0xDC + 4 by rw [BitVec.add_assoc]; rfl, memStore8_same, ze_ex]

theorem fsM3_saves {M : Word → BitVec 8} {S : Word} {n : Machine} {b : BitVec 8} :
    ∀ k, k < 11 → memLoad32 (fsM3 M S n b) (S + BitVec.ofNat 32 (0x41C - 4 * k)) = reg n (savedReg k) := fun k hk => by
  rw [← fsSaves_read k hk]
  exact memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]; exact fsM3_keep (sepS S (.inl (by omega)) (by decide) (by omega))

theorem fsM3_out {M : Word → BitVec 8} {S : Word} {n : Machine} {b : BitVec 8} {x : Word}
    (h : Sep (S + BitVec.ofNat 32 0xDC) 0x70 x 1) (h' : Sep (S + BitVec.ofNat 32 0x3F4) 0x2C x 1) :
    fsM3 M S n b x = M x := by rw [fsM3_keep h, fsSaves_out h']

def fsB1 : List BInstr := [.lbu a0 sp 0xE0, .aluImm .add a1 x0 0x30]
def fsB2 : List BInstr := [.aluImm .add a0 a0 0xFFFFFF9F]
def fsC1 : List BInstr := [.aluImm .add a1 sp 0xE1, .aluImm .add a0 sp 0x210, .aluImm .add a2 x0 0x2F]
theorem fsB1_end : blockEnd p384FromSec1Code 0x6A fsB1 = some 0x72 := by decide
theorem fsB2_end : blockEnd p384FromSec1Code 0x7A fsB2 = some 0x7E := by decide
theorem fsC1_end : blockEnd p384FromSec1Code 0x56 fsC1 = some 0x60 := by decide

theorem tml_four (t : BitVec 8) : tagMsgLen (t.zeroExtend 32) 0x30 + 0xFFFFFF9F = 0 ↔ t = 4 := by
  revert t; decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The tag and length checks**, from the entry: a first byte other than 4
returns an error, through `Tag::from_u8`'s error or `message_len`'s; tag 4
reaches 0x82. -/
theorem fs_front {M : Word → BitVec 8} {n : Machine} {S inp out : Word} (C : FsCode M) (F : Fr S 0x420)
    (s : St M FP n 0 (reg n)) (rsp : reg n sp = S + 0x420) (ra0 : reg n a0 = out) (ra1 : reg n a1 = inp)
    (sI : Sep inp 0x61 (S + 0xFFFFFE60) 0x5C0) (hoa : out.toNat % 4 = 0) (hO : out.toNat + 0x68 ≤ 0x40000000)
    (sO : Sep out 0x68 (S + 0xFFFFFE60) 0x5C0) (hret : reg n ra &&& ~~~1 = reg n ra) :
    (M inp ≠ 4 → ∃ n', Steps n n' ∧ FsRet M n S out n' ∧ memLoad32 n'.mem out = 1) ∧
    (M inp = 4 → ∃ n', Steps n n' ∧ St (fsM3 M S n 4) FP n' 0x82 (reg n') ∧ reg n' sp = S ∧
      reg n' (9 : Fin 32) = inp ∧ reg n' (24 : Fin 32) = out ∧
      ∀ q : Fin 32, q.val ∈ [3, 4, 26, 27] → reg n' q = reg n q) := by
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have sIs : Sep (S + BitVec.ofNat 32 0x3F4) 0x2C inp 1 :=
    (fr_inFrame (N := 0x420) (by decide) ((sI.sub (c := 0) (l := 1) (by decide)) |> fun h => by
      rw [add_ofNat_zero] at h; exact h.symm))
  obtain ⟨n1, c1, u1, a1v, sp1, e19, e124, e18, k1⟩ := fs_stA C F s rsp ra0 ra1 sIs
  replace u1 : St (fsM3 M S n (M inp)) FP n1 0x52 (reg n1) := u1
  change reg n1 a0 = memLoad32 (fsM3 M S n (M inp)) (S + BitVec.ofNat 32 0xDC) at a1v
  rw [fsM3_word] at a1v
  have hfr : ∀ x : Word, 0x40000000 ≤ x.toNat → fsM3 M S n (M inp) x = M x := fun x hx =>
    fsM3_out (F.hiOut (by decide) hx) (F.hiOut (by decide) hx)
  have C1 : FsCode (fsM3 M S n (M inp)) := C.hi hfr
  have hM3 : ∀ x, Sep (S + 0xFFFFFE60) 0x5C0 x 1 → fsM3 M S n (M inp) x = M x := fun x hx =>
    fsM3_out (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx)
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · by_cases hv : Sec1TagOk (M inp)
    · -- a valid tag other than 4: `message_len` isn't 97
      rw [ite_eq_left hv] at a1v
      obtain ⟨n2, d2, u2⟩ := u1.taken C1.self 0x6A fs_at_52 (by decide) (by
        show branchTaken .beq (reg n1 a0) (reg n1 (8 : Fin 32)) = true; rw [a1v, e18]; decide)
      obtain ⟨n3, c3, u3⟩ := u2.block fsB1 C1.self fsB1_end ⟨trivial, trivial, trivial⟩
      have r3 : ∀ q, reg n3 q = (runBlock fsB1 (fsM3 M S n (M inp), reg n1)).2 q := fun q => by rw [u3.regs]
      obtain ⟨n4, c4, u4, a4, k4⟩ := c_tml (t := (M inp).zeroExtend 32) (fe := 0x30)
        (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St (fsM3 M S n (M inp)) FP n3 0x72 (reg n3)) C1.self C1.K fs_at_72 fs_at_76
        (by decide) (by decide)
        (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsB1, upd, ↓reduceIte]; rw [sp1]
            show ((fsM3 M S n (M inp)) (S + BitVec.ofNat 32 0xE0)).zeroExtend 32 = _; rw [fsM3_tag hv])
        (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsB1, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
      obtain ⟨n5, c5, u5⟩ := u4.block fsB2 C1.self fsB2_end ⟨trivial, trivial⟩
      have r5 : ∀ q, q ≠ a0 → reg n5 q = reg n4 q := fun q hq => by
        rw [u5.regs]; simp only [runBlock, BInstr.run, fsB2]; exact updz u4.zero hq
      obtain ⟨n6, d6, u6⟩ := (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St (fsM3 M S n (M inp)) FP n5 0x7E (reg n5)).taken
        C1.self 0x44A fs_at_7e (by decide) (by
          show branchTaken .bne (reg n5 a0) 0 = true
          rw [u5.regs]; simp +decide only [runBlock, BInstr.run, fsB2, upd, ↓reduceIte]; rw [a4]
          have : aluEval .add (tagMsgLen ((M inp).zeroExtend 32) 0x30) 0xFFFFFF9F ≠ 0 :=
            fun h => hb ((tml_four (M inp)).1 h)
          revert this; generalize aluEval .add (tagMsgLen ((M inp).zeroExtend 32) 0x30) 0xFFFFFF9F = z; intro h
          simp only [branchTaken, bne_iff_ne, ne_eq]; exact h)
      have kk : ∀ q, q.val ∈ [3, 4, 26, 27, 2, 24] → reg n5 q = reg n1 q := fun q hq => by
        rw [r5 q (by revert hq; revert q; decide), k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide), r3,
          runBlock_reg _ _ _ q u2.zero (by simp only [fsB1]; revert hq; revert q; decide)]
      obtain ⟨n7, c7, R7, w7⟩ := fs_err (M := M) (n := n) C1 F u6.self (by rw [u6.regs, kk sp (by decide)]; exact sp1)
        (by rw [u6.regs, kk 24 (by decide)]; exact e124) hoa hO sO fsM3_saves hret
        (fun q hq => by rw [u6.regs, kk q (by revert hq; revert q; decide), k1 q hq]) hM3
      exact ⟨n7, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (.cons d6 c7))))), R7, w7⟩
    · -- not a tag: `Tag::from_u8` fails
      rw [ite_eq_right hv] at a1v
      obtain ⟨n2, d2, u2⟩ := u1.notTaken C1.self 0x56 fs_at_52 (by decide) (by
        show branchTaken .beq (reg n1 a0) (reg n1 (8 : Fin 32)) = false; rw [a1v, e18]; decide)
      obtain ⟨n3, c3, u3⟩ := u2.block fsC1 C1.self fsC1_end ⟨trivial, trivial, trivial, trivial⟩
      have r3 : ∀ q, reg n3 q = (runBlock fsC1 (fsM3 M S n (M inp), reg n1)).2 q := fun q => by rw [u3.regs]
      obtain ⟨fA, fW, hFC⟩ := F.mc
      obtain ⟨n4, c4, u4, fr4, k4⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x210) (src := S + BitVec.ofNat 32 0xE1)
        (S := S) (N := 0x2F) (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St (fsM3 M S n (M inp)) FP n3 0x60 (reg n3))
        C1.self C1.K fs_at_60 fs_at_64 (by decide) (by decide)
        (by rw [r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp1)
        (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsC1, upd, ↓reduceIte]; rw [sp1]; rfl)
        (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsC1, upd, ↓reduceIte]; rw [sp1]; rfl)
        (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsC1, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
        ⟨C1.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
          sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
          by rw [F.at _ (by decide)]; omega⟩
      have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
      have fr4' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x210) 0x2F x 1 →
          n4.mem x = fsM3 M S n (M inp) x := fun x a b => by rw [fr4 x a, copyBytes_sep b (Nat.le_refl _)]
      have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
        sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
      have C4 := C1.hi fun x hx => fr4' x (lo16 x hx) (F.hiOut (by decide) hx)
      obtain ⟨n5, d5, u5⟩ := u4.jump C4.self fs_at_68 (off' := 0x44A) (by decide) (by rw [u4.pc]; decide)
      have kk : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 24, 26, 27] → reg n4 q = reg n1 q := fun q hq => by
        rw [k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
          (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r3,
          runBlock_reg _ _ _ q u2.zero (by simp only [fsC1]; revert hq; revert q; decide)]
      have below16 : ∀ {x : Word}, Sep (S + 0xFFFFFE60) 0x5C0 x 1 → Sep (S + 0xFFFFFFF0) 16 x 1 := fun {x} hx => by
        have := hx.sub (c := 0x190) (l := 16) (by decide)
        rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x190 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
      obtain ⟨n7, c7, R7, w7⟩ := fs_err (M := M) (n := n) C4 F u5.self (by rw [u5.regs, kk sp (by decide)]; exact sp1)
        (by rw [u5.regs, kk 24 (by decide)]; exact e124) hoa hO sO
        (fun k hk => by
          rw [← fsM3_saves (M := M) (S := S) (n := n) (b := M inp) k hk]
          exact memLoad32_congr fun j hj => by
            rw [add_ofNat_assoc]
            exact fr4' _ (F.lowB hb16 (by decide) (by omega)) (sepS S (.inl (by omega)) (by decide) (by omega)))
        hret (fun q hq => by rw [u5.regs, kk q (by revert hq; revert q; decide), k1 q hq])
        (fun x hx => by rw [fr4' x (below16 hx) (fr_inFrame (by decide) hx), hM3 x hx])
      exact ⟨n7, c1.trans (.cons d2 (c3.trans (c4.trans (.cons d5 c7)))), R7, w7⟩
  · -- tag 4
    have hv : Sec1TagOk (M inp) := by rw [hb]; decide
    rw [ite_eq_left hv] at a1v
    obtain ⟨n2, d2, u2⟩ := u1.taken C1.self 0x6A fs_at_52 (by decide) (by
      show branchTaken .beq (reg n1 a0) (reg n1 (8 : Fin 32)) = true; rw [a1v, e18]; decide)
    obtain ⟨n3, c3, u3⟩ := u2.block fsB1 C1.self fsB1_end ⟨trivial, trivial, trivial⟩
    have r3 : ∀ q, reg n3 q = (runBlock fsB1 (fsM3 M S n (M inp), reg n1)).2 q := fun q => by rw [u3.regs]
    obtain ⟨n4, c4, u4, a4, k4⟩ := c_tml (t := (M inp).zeroExtend 32) (fe := 0x30)
      (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St (fsM3 M S n (M inp)) FP n3 0x72 (reg n3)) C1.self C1.K fs_at_72 fs_at_76
      (by decide) (by decide)
      (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsB1, upd, ↓reduceIte]; rw [sp1]
          show ((fsM3 M S n (M inp)) (S + BitVec.ofNat 32 0xE0)).zeroExtend 32 = _; rw [fsM3_tag hv])
      (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsB1, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    obtain ⟨n5, c5, u5⟩ := u4.block fsB2 C1.self fsB2_end ⟨trivial, trivial⟩
    have r5 : ∀ q, q ≠ a0 → reg n5 q = reg n4 q := fun q hq => by
      rw [u5.regs]; simp only [runBlock, BInstr.run, fsB2]; exact updz u4.zero hq
    obtain ⟨n6, d6, u6⟩ := (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St (fsM3 M S n (M inp)) FP n5 0x7E (reg n5)).notTaken
      C1.self 0x82 fs_at_7e (by decide) (by
        show branchTaken .bne (reg n5 a0) 0 = false
        rw [u5.regs]; simp +decide only [runBlock, BInstr.run, fsB2, upd, ↓reduceIte]; rw [a4]
        rw [show aluEval .add (tagMsgLen ((M inp).zeroExtend 32) 0x30) 0xFFFFFF9F = 0 from (tml_four (M inp)).2 hb]
        decide)
    have kk : ∀ q, q.val ∈ [3, 4, 26, 27, 2, 9, 24] → reg n5 q = reg n1 q := fun q hq => by
      rw [r5 q (by revert hq; revert q; decide), k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide), r3,
        runBlock_reg _ _ _ q u2.zero (by simp only [fsB1]; revert hq; revert q; decide)]
    rw [hb] at u6
    exact ⟨n6, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (.single d6))))), u6.self,
      by rw [u6.regs, kk sp (by decide)]; exact sp1, by rw [u6.regs, kk 9 (by decide)]; exact e19,
      by rw [u6.regs, kk 24 (by decide)]; exact e124,
      fun q hq => by rw [u6.regs, kk q (by revert hq; revert q; decide), k1 q hq]⟩

theorem hw0 (b0 b1 : BitVec 8) :
    (((b1.zeroExtend 32 : Word) <<< ((8 : Word).toNat % 32)) ||| b0.zeroExtend 32).extractLsb' 0 8 = b0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  rw [show (8 : Word).toNat % 32 = 8 from rfl, Nat.zero_add, decide_eq_true hi, decide_eq_true (show i < 32 by omega)]
  simp

theorem hw1 (b0 b1 : BitVec 8) :
    (((b1.zeroExtend 32 : Word) <<< ((8 : Word).toNat % 32)) ||| b0.zeroExtend 32).extractLsb' 8 8 = b1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  rw [show (8 : Word).toNat % 32 = 8 from rfl, decide_eq_true hi, decide_eq_true (show 8 + i < 32 by omega),
    decide_eq_false (show ¬ (8 + i < 8) by omega), show 8 + i - 8 = i by omega, decide_eq_true (show i < 32 by omega),
    BitVec.getLsbD_of_ge b0 (8 + i) (by omega)]
  simp

/-- The delay loop at 0x8C: count `a0` down to 0. -/
theorem fs_delay {M : Word → BitVec 8} (C : FsCode M) :
    ∀ k : Nat, ∀ {n : Machine}, 1 ≤ k → k < 2 ^ 32 → St M FP n 0x8C (reg n) → reg n a0 = BitVec.ofNat 32 k →
      ∃ n', Steps n n' ∧ St M FP n' 0x90 (reg n') ∧ ∀ q, q ≠ a0 → reg n' q = reg n q
  | 0, _, h, _, _, _ => absurd h (by decide)
  | k + 1, n, _, hk, s, ha => by
    obtain ⟨n1, d1, u1⟩ := s.aluImm C.self fs_at_8c (off' := 0x8E) (by decide)
    have e1 : aluEval .add (reg n a0) 0xFFFFFFFF = BitVec.ofNat 32 k := by
      rw [ha]; apply BitVec.eq_of_toNat_eq
      show (BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF).toNat = _
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 0xFFFFFFFF from rfl]
      omega
    have k1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q hq => by rw [u1.regs]; exact updz s.zero hq
    by_cases h0 : k = 0
    · subst h0
      obtain ⟨n2, d2, u2⟩ := u1.self.notTaken C.self 0x90 fs_at_8e (by decide) (by
        show branchTaken .bne (reg n1 a0) 0 = false
        rw [u1.regs]; simp +decide only [upd, ↓reduceIte]; rw [e1]; decide)
      exact ⟨n2, .cons d1 (.single d2), u2.self, fun q hq => by rw [u2.regs, k1 q hq]⟩
    · obtain ⟨n2, d2, u2⟩ := u1.self.taken C.self 0x8C fs_at_8e (by decide) (by
        show branchTaken .bne (reg n1 a0) 0 = true
        rw [u1.regs]; simp +decide only [upd, ↓reduceIte]; rw [e1]
        simp only [branchTaken, bne_iff_ne, ne_eq]
        intro h; apply h0
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl, Nat.mod_eq_of_lt (by omega)] at this
        exact this)
      obtain ⟨n3, c3, u3, k3⟩ := fs_delay C k (by omega) (by omega) u2.self (by
        rw [u2.regs, u1.regs]; simp +decide only [upd, ↓reduceIte]; exact e1)
      exact ⟨n3, .cons d1 (.cons d2 c3), u3, fun q hq => by rw [k3 q hq, u2.regs, k1 q hq]⟩

def fsD0 : List BInstr := [.aluImm .add (18 : Fin 32) sp 0x2A4, .aluImm .add a0 x0 0x61]
def fsD1 : List BInstr :=
  [.lbu a0 (9 : Fin 32) 0x1, .lbu a1 (9 : Fin 32) 0x0, .lbu a2 (9 : Fin 32) 0x2, .lbu (8 : Fin 32) (9 : Fin 32) 0x3,
   .lbu (19 : Fin 32) (9 : Fin 32) 0x4, .lbu (20 : Fin 32) (9 : Fin 32) 0x5, .lbu (21 : Fin 32) (9 : Fin 32) 0x6,
   .lbu (22 : Fin 32) (9 : Fin 32) 0x7, .aluImm .sll a0 a0 0x8, .alu .or a0 a0 a1, .aluImm .add a1 (9 : Fin 32) 0x8,
   .aluImm .add (9 : Fin 32) (9 : Fin 32) 0x37]
def fsD2 : List BInstr := [.sb sp a2 0x396, .aluImm .add a0 sp 0x210, .aluImm .add a2 x0 0x2F]
def fsD3 : List BInstr := [.aluImm .add a0 sp 0x1AC, .aluImm .add a2 x0 0x2A, .alu .add a1 x0 (9 : Fin 32)]
def fsD4 : List BInstr := [.lbu a1 sp 0x396]
def fsD5 : List BInstr :=
  [.sb sp a1 0x14, .sb sp (8 : Fin 32) 0x15, .sb sp (19 : Fin 32) 0x16, .sb sp (20 : Fin 32) 0x17,
   .sb sp (21 : Fin 32) 0x18, .sb sp (22 : Fin 32) 0x19, .aluImm .add a0 sp 0x1A, .aluImm .add a1 sp 0x210,
   .aluImm .add a2 x0 0x2F]
def fsD6 : List BInstr := [.aluImm .add a0 sp 0x49, .aluImm .add a1 sp 0x1AC, .aluImm .add a2 x0 0x2A]

theorem fsD0_end : blockEnd p384FromSec1Code 0x82 fsD0 = some 0x8A := by decide
theorem fsD1_end : blockEnd p384FromSec1Code 0x90 fsD1 = some 0xBC := by decide
theorem fsD2_end : blockEnd p384FromSec1Code 0xC0 fsD2 = some 0xCA := by decide
theorem fsD3_end : blockEnd p384FromSec1Code 0xD2 fsD3 = some 0xDA := by decide
theorem fsD4_end : blockEnd p384FromSec1Code 0xE6 fsD4 = some 0xEA := by decide
theorem fsD5_end : blockEnd p384FromSec1Code 0xEE fsD5 = some 0x110 := by decide
theorem fsD6_end : blockEnd p384FromSec1Code 0x118 fsD6 = some 0x122 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **Copying the input**, from 0x82 to 0x12A: after a delay loop, the 97
input bytes land at `S + 0x12`, through `S + 0x210`, `S + 0x1AC`, and
`S + 0x394`. -/
theorem fs_stC {M : Word → BitVec 8} {n : Machine} {S inp : Word} (C : FsCode M) (F : Fr S 0x420)
    (s : St M FP n 0x82 (reg n)) (rsp : reg n sp = S) (r9 : reg n (9 : Fin 32) = inp)
    (sI : Sep inp 0x61 (S + 0xFFFFFE60) 0x5C0) (hI : inp.toNat + 0x61 ≤ 0x40000000) :
    ∃ n', Steps n n' ∧ St n'.mem FP n' 0x12A (reg n') ∧ FsCode n'.mem ∧
      (∀ k, k < 0x61 → n'.mem (S + BitVec.ofNat 32 (0x12 + k)) = M (inp + BitVec.ofNat 32 k)) ∧
      (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x12) 0x61 x 1 →
        Sep (S + BitVec.ofNat 32 0x1AC) 0x93 x 1 → Sep (S + BitVec.ofNat 32 0x394) 3 x 1 → n'.mem x = M x) ∧
      reg n' sp = S ∧ ∀ q : Fin 32, q.val ∈ [3, 4, 24, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨n1, c1, u1⟩ := s.block fsD0 C.self fsD0_end ⟨trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock fsD0 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have v1 : St M FP n1 0x8A (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have a1v : reg n1 a0 = BitVec.ofNat 32 0x61 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, fsD0, upd, ↓reduceIte]; (try rw [hz]); try rfl
  obtain ⟨n2, d2, u2⟩ := v1.notTaken C.self 0x8C fs_at_8a (by decide) (by
    show branchTaken .beq (reg n1 a0) 0 = false; rw [a1v]; decide)
  obtain ⟨n3, c3, u3, k3⟩ := fs_delay C 0x61 (by decide) (by decide) u2.self (by rw [u2.regs]; exact a1v)
  have K3 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 24, 26, 27] → reg n3 q = reg n q := fun q hq => by
    rw [k3 q (by revert hq; revert q; decide), u2.regs, r1, runBlock_reg _ _ _ q hz (by simp only [fsD0]; revert hq; revert q; decide)]
  have sp3 : reg n3 sp = S := by rw [K3 sp (by decide)]; exact rsp
  have i3 : reg n3 (9 : Fin 32) = inp := by rw [K3 9 (by decide)]; exact r9
  -- the first eight bytes, into registers
  obtain ⟨n4, c4, u4⟩ := u3.block fsD1 C.self fsD1_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r4 : ∀ q, reg n4 q = (runBlock fsD1 (M, reg n3)).2 q := fun q => by rw [u4.regs]
  have ib : ∀ k : Nat, inp + BitVec.ofNat 32 k = inp + BitVec.ofNat 32 k := fun _ => rfl
  have eb : ∀ (q : Fin 32) (k : Nat), q.val ∈ [8, 19, 20, 21, 22, 12] →
      reg n4 q = (M (inp + BitVec.ofNat 32 k)).zeroExtend 32 → (reg n4 q).extractLsb' 0 8 = M (inp + BitVec.ofNat 32 k) :=
    fun q k _ h => by rw [h, ze_ex]
  have e8 : reg n4 (8 : Fin 32) = (M (inp + BitVec.ofNat 32 3)).zeroExtend 32 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, fsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e19 : reg n4 (19 : Fin 32) = (M (inp + BitVec.ofNat 32 4)).zeroExtend 32 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, fsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e20 : reg n4 (20 : Fin 32) = (M (inp + BitVec.ofNat 32 5)).zeroExtend 32 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, fsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e21 : reg n4 (21 : Fin 32) = (M (inp + BitVec.ofNat 32 6)).zeroExtend 32 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, fsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e22 : reg n4 (22 : Fin 32) = (M (inp + BitVec.ofNat 32 7)).zeroExtend 32 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, fsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e12 : reg n4 a2 = (M (inp + BitVec.ofNat 32 2)).zeroExtend 32 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, fsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e10 : reg n4 a0 = aluEval .or (aluEval .sll ((M (inp + BitVec.ofNat 32 1)).zeroExtend 32) 0x8)
      ((M (inp + BitVec.ofNat 32 0)).zeroExtend 32) := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, fsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e11 : reg n4 a1 = inp + 8 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, fsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have e9 : reg n4 (9 : Fin 32) = inp + 0x37 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, fsD1, upd, ↓reduceIte]; rw [i3]; rfl
  have sp4 : reg n4 sp = S := by rw [r4, runBlock_reg _ _ _ sp u3.zero (by decide)]; exact sp3
  have hb1A : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have iF : ∀ {j l c m : Nat}, j + l ≤ 0x61 → c + m ≤ 0x420 → Sep (inp + BitVec.ofNat 32 j) l (S + BitVec.ofNat 32 c) m :=
    fun {j l c m} h1 h2 => by
      have := (sI.sub (c := j) (l := l) (by omega)).subR (c := 0x1A0 + c) (l := m) (by omega)
      rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
        omega] at this
  have iL : ∀ {j l : Nat}, j + l ≤ 0x61 → Sep (inp + BitVec.ofNat 32 j) l (S + 0xFFFFFFF0) 16 := fun {j l} h => by
    have := (sI.sub (c := j) (l := l) (by omega)).subR (c := 0x190) (l := 16) (by decide)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x190 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
  have iT : ∀ j, j ≤ 0x61 → (inp + BitVec.ofNat 32 j).toNat = inp.toNat + j := fun j hj => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hiI : ∀ (x : Word) (j : Nat), 0x40000000 ≤ x.toNat → j < 0x61 → x ≠ inp + BitVec.ofNat 32 j := fun x j hx hj e => by
    have := iT j (by omega); rw [← e] at this; omega
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have l16b : ∀ d, d + 1 ≤ 0x420 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 1 := fun d hd => F.lowB hb16 (by decide) hd
  have sq : ∀ c l d, c + l ≤ 0x420 → d + 1 ≤ 0x420 → (c + l ≤ d ∨ d + 1 ≤ c) →
      Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 d) 1 := fun c l d h1 h2 h3 => sepS S h3 (by omega) (by omega)
  have kc : ∀ {m m' : Machine}, (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg m' q = reg m q) →
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q :=
    fun h q hq => h q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  obtain ⟨fA, fW, hFC⟩ := F.mc
  -- the first two bytes to `S + 0x394`
  have v4 : St M FP n4 0xBC (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
  obtain ⟨n5, d5, u5⟩ := v4.sh C.self fs_at_bc (off' := 0xC0) (by decide) (by
    rw [sp4]; show (S + BitVec.ofNat 32 0x394).toNat % 2 = 0; rw [F.at _ (by decide)]; omega)
  have e395 : S + BitVec.ofNat 32 0x394 + 1 = S + BitVec.ofNat 32 0x395 := by rw [BitVec.add_assoc]; rfl
  have hw0' : (reg n4 a0).extractLsb' 0 8 = M (inp + BitVec.ofNat 32 0) := by rw [e10]; exact hw0 _ _
  have hw1' : (reg n4 a0).extractLsb' 8 8 = M (inp + BitVec.ofNat 32 1) := by rw [e10]; exact hw1 _ _
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore8 (memStore8 M (S + BitVec.ofNat 32 0x394) (M (inp + BitVec.ofNat 32 0)))
      (S + BitVec.ofNat 32 0x395) (M (inp + BitVec.ofNat 32 1)) = M1 := ⟨_, rfl⟩
  have v5 : St M1 FP n5 0xC0 (reg n5) := by
    rw [← hM1]; refine ⟨u5.pc, ?_, fun _ => rfl⟩
    rw [u5.mem, sp4, show S + 0x394 = S + BitVec.ofNat 32 0x394 from rfl, e395, hw0', hw1']
  have r5 : ∀ q, reg n5 q = reg n4 q := u5.regs
  have h1 : ∀ x, Sep (S + BitVec.ofNat 32 0x394) 2 x 1 → M1 x = M x := fun x hx => by
    rw [← hM1, dq_st8 ((hx.sub (c := 1) (l := 1) (by decide)) |> fun h => by rwa [add_ofNat_assoc] at h),
      dq_st8 ((hx.sub (c := 0) (l := 1) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h)]
  have C1 := C.hi fun x hx => h1 x (F.hiOut (by decide) hx)
  -- the third byte, and the copy of bytes 8..0x36 to `S + 0x210`
  obtain ⟨n6, c6, u6⟩ := v5.block fsD2 C1.self fsD2_end (by
    simp only [BlockOk, BInstr.ok, fsD2]; simp +decide only [and_true]
    rw [r5, sp4]; exact F.sepHi (by decide) (by decide) (by decide))
  have r6 : ∀ q, reg n6 q = (runBlock fsD2 (M1, reg n5)).2 q := fun q => by rw [u6.regs]
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore8 M1 (S + BitVec.ofNat 32 0x396) (M (inp + BitVec.ofNat 32 2)) = M2 := ⟨_, rfl⟩
  have m6 : n6.mem = M2 := by
    rw [u6.mem, ← hM2]; simp +decide only [runBlock, BInstr.run, fsD2, upd, ↓reduceIte]
    rw [r5, r5, sp4, e12, ze_ex]; rfl
  have h2 : ∀ x, Sep (S + BitVec.ofNat 32 0x396) 1 x 1 → M2 x = M1 x := fun x hx => by rw [← hM2]; exact dq_st8 hx
  have C2 := C1.hi fun x hx => h2 x (F.hiOut (by decide) hx)
  have sp6 : reg n6 sp = S := by rw [r6, runBlock_reg _ _ _ sp v5.zero (by decide), r5]; exact sp4
  obtain ⟨n7, c7, u7, fr7, k7⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x210) (src := inp + BitVec.ofNat 32 8) (S := S)
    (N := 0x2F) (⟨u6.pc, m6, fun _ => rfl⟩ : St M2 FP n6 0xCA (reg n6)) C2.self C2.K fs_at_ca fs_at_ce (by decide) (by decide)
    sp6 (by rw [r6]; simp +decide only [runBlock, BInstr.run, fsD2, upd, ↓reduceIte]; rw [r5, sp4]; rfl)
    (by rw [r6, runBlock_reg _ _ _ a1 v5.zero (by decide), r5]; exact e11)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, fsD2, upd, ↓reduceIte]; (try rw [v5.zero]); try rfl)
    ⟨C2.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), iL (by decide),
      (iF (by decide) (by decide)).symm, fA, fW, by rw [F.at _ (by decide)]; omega, by rw [iT _ (by decide)]; omega⟩
  have fr7' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x210) 0x2F x 1 → n7.mem x = M2 x :=
    fun x a b => by rw [fr7 x a, copyBytes_sep b (Nat.le_refl _)]
  have C7 := C2.hi fun x hx => fr7' x (lo16 x hx) (F.hiOut (by decide) hx)
  have k7' := kc k7
  have sp7 : reg n7 sp = S := by rw [k7' sp (by decide)]; exact sp6
  have K7 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 19, 20, 21, 22, 24, 26, 27] → reg n7 q = reg n4 q := fun q hq => by
    rw [k7' q (by revert hq; revert q; decide), r6, runBlock_reg _ _ _ q v5.zero (by simp only [fsD2]; revert hq; revert q; decide), r5]
  -- bytes 0x37..0x60 to `S + 0x1AC`
  obtain ⟨n8, c8, u8⟩ := u7.block fsD3 C7.self fsD3_end ⟨trivial, trivial, trivial, trivial⟩
  have r8 : ∀ q, reg n8 q = (runBlock fsD3 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
  obtain ⟨n9, c9, u9, fr9, k9⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x1AC) (src := inp + BitVec.ofNat 32 0x37)
    (S := S) (N := 0x2A) (⟨u8.pc, u8.mem, fun _ => rfl⟩ : St n7.mem FP n8 0xDA (reg n8)) C7.self C7.K fs_at_da fs_at_de
    (by decide) (by decide) (by rw [r8, runBlock_reg _ _ _ sp u7.zero (by decide)]; exact sp7)
    (by rw [r8]; simp +decide only [runBlock, BInstr.run, fsD3, upd, ↓reduceIte]; rw [sp7]; rfl)
    (by rw [r8]; simp +decide only [runBlock, BInstr.run, fsD3, upd, ↓reduceIte]; rw [K7 9 (by decide), e9]
        exact BitVec.zero_add _)
    (by rw [r8]; simp +decide only [runBlock, BInstr.run, fsD3, upd, ↓reduceIte]; (try rw [u7.zero]); try rfl)
    ⟨C7.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), iL (by decide),
      (iF (by decide) (by decide)).symm, fA, fW, by rw [F.at _ (by decide)]; omega, by rw [iT _ (by decide)]; omega⟩
  have fr9' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x1AC) 0x2A x 1 → n9.mem x = n7.mem x :=
    fun x a b => by rw [fr9 x a, copyBytes_sep b (Nat.le_refl _)]
  have C9 := C7.hi fun x hx => fr9' x (lo16 x hx) (F.hiOut (by decide) hx)
  have k9' := kc k9
  have sp9 : reg n9 sp = S := by rw [k9' sp (by decide), r8, runBlock_reg _ _ _ sp u7.zero (by decide)]; exact sp7
  have K9 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 19, 20, 21, 22, 24, 26, 27] → reg n9 q = reg n4 q := fun q hq => by
    rw [k9' q (by revert hq; revert q; decide), r8, runBlock_reg _ _ _ q u7.zero (by simp only [fsD3]; revert hq; revert q; decide),
      K7 q (by revert hq; revert q; decide)]
  -- the first two bytes back from `S + 0x394`, and the third from `S + 0x396`
  have v9 : St n9.mem FP n9 0xE2 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  obtain ⟨n10, d10, u10⟩ := v9.lh C9.self fs_at_e2 (off' := 0xE6) (by decide) (by
    rw [sp9]; show (S + BitVec.ofNat 32 0x394).toNat % 2 = 0; rw [F.at _ (by decide)]; omega)
  obtain ⟨n11, c11, u11⟩ := u10.self.block fsD4 C9.self fsD4_end ⟨trivial, trivial⟩
  have r11 : ∀ q, q ≠ a1 → reg n11 q = reg n10 q := fun q hq => by
    rw [u11.regs]; simp only [runBlock, BInstr.run, fsD4]; exact updz u10.self.zero hq
  have a11 : reg n11 a1 = (n9.mem (S + BitVec.ofNat 32 0x396)).zeroExtend 32 := by
    rw [u11.regs]; simp +decide only [runBlock, BInstr.run, fsD4, upd, ↓reduceIte]; rw [u10.regs]
    simp +decide only [upd, ↓reduceIte]; rw [sp9]; rfl
  have a10 : reg n11 a0 = (n9.mem (S + BitVec.ofNat 32 0x395) ++ n9.mem (S + BitVec.ofNat 32 0x394)).signExtend 32 := by
    rw [r11 a0 (by decide), u10.regs]; simp +decide only [upd, ↓reduceIte]; rw [sp9]
    rw [show S + 0x394 = S + BitVec.ofNat 32 0x394 from rfl, e395]
  have sp11 : reg n11 sp = S := by rw [r11 sp (by decide), u10.regs]; simp +decide only [upd, ↓reduceIte]; exact sp9
  have v11 : St n9.mem FP n11 0xEA (reg n11) := ⟨u11.pc, u11.mem, fun _ => rfl⟩
  obtain ⟨n12, d12, u12⟩ := v11.sh C9.self fs_at_ea (off' := 0xEE) (by decide) (by
    rw [sp11]; show (S + BitVec.ofNat 32 0x12).toNat % 2 = 0; rw [F.at _ (by decide)]; omega)
  obtain ⟨M12, hM12⟩ : ∃ M12, memStore8 (memStore8 n9.mem (S + BitVec.ofNat 32 0x12) (n9.mem (S + BitVec.ofNat 32 0x394)))
      (S + BitVec.ofNat 32 0x13) (n9.mem (S + BitVec.ofNat 32 0x395)) = M12 := ⟨_, rfl⟩
  have v12 : St M12 FP n12 0xEE (reg n12) := by
    rw [← hM12]; refine ⟨u12.pc, ?_, fun _ => rfl⟩
    rw [u12.mem, sp11, a10, signExtend_lo, signExtend_hi,
      show S + 0x12 = S + BitVec.ofNat 32 0x12 from rfl,
      show S + BitVec.ofNat 32 0x12 + 1 = S + BitVec.ofNat 32 0x13 by rw [BitVec.add_assoc]; rfl]
  have h12 : ∀ x, Sep (S + BitVec.ofNat 32 0x12) 2 x 1 → M12 x = n9.mem x := fun x hx => by
    rw [← hM12, dq_st8 ((hx.sub (c := 1) (l := 1) (by decide)) |> fun h => by rwa [add_ofNat_assoc] at h),
      dq_st8 ((hx.sub (c := 0) (l := 1) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h)]
  have C12 := C9.hi fun x hx => h12 x (F.hiOut (by decide) hx)
  have r12 : ∀ q, reg n12 q = reg n11 q := u12.regs
  -- bytes 2..7
  obtain ⟨n13, c13, u13⟩ := v12.block fsD5 C12.self fsD5_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, fsD5]; simp +decide only [and_true]
    rw [r12, sp11]
    exact ⟨F.sepHi (by decide) (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide),
      F.sepHi (by decide) (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide),
      F.sepHi (by decide) (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩)
  have r13 : ∀ q, reg n13 q = (runBlock fsD5 (M12, reg n12)).2 q := fun q => by rw [u13.regs]
  obtain ⟨M13, hM13⟩ : ∃ M13, memStore8 (memStore8 (memStore8 (memStore8 (memStore8 (memStore8 M12
      (S + BitVec.ofNat 32 0x14) (n9.mem (S + BitVec.ofNat 32 0x396))) (S + BitVec.ofNat 32 0x15) (M (inp + BitVec.ofNat 32 3)))
      (S + BitVec.ofNat 32 0x16) (M (inp + BitVec.ofNat 32 4))) (S + BitVec.ofNat 32 0x17) (M (inp + BitVec.ofNat 32 5)))
      (S + BitVec.ofNat 32 0x18) (M (inp + BitVec.ofNat 32 6))) (S + BitVec.ofNat 32 0x19) (M (inp + BitVec.ofNat 32 7)) = M13 :=
    ⟨_, rfl⟩
  have m13 : n13.mem = M13 := by
    rw [u13.mem, ← hM13]; simp +decide only [runBlock, BInstr.run, fsD5, upd, ↓reduceIte]
    rw [r12, r12, r12, r12, r12, r12, r12, sp11, a11, ze_ex, r11 8 (by decide), r11 19 (by decide), r11 20 (by decide),
      r11 21 (by decide), r11 22 (by decide), u10.regs, u10.regs, u10.regs, u10.regs, u10.regs]
    simp +decide only [upd, ↓reduceIte]
    rw [K9 8 (by decide), K9 19 (by decide), K9 20 (by decide), K9 21 (by decide), K9 22 (by decide), e8, e19, e20, e21, e22,
      ze_ex, ze_ex, ze_ex, ze_ex, ze_ex]; rfl
  have h13 : ∀ x, Sep (S + BitVec.ofNat 32 0x14) 6 x 1 → M13 x = M12 x := fun x hx => by
    have sb : ∀ c, c < 6 → Sep (S + BitVec.ofNat 32 (0x14 + c)) 1 x 1 := fun c hc => by
      have := hx.sub (c := c) (l := 1) (by omega); rwa [add_ofNat_assoc] at this
    rw [← hM13, dq_st8 (sb 5 (by decide)), dq_st8 (sb 4 (by decide)), dq_st8 (sb 3 (by decide)), dq_st8 (sb 2 (by decide)),
      dq_st8 (sb 1 (by decide)), dq_st8 (sb 0 (by decide))]
  have C13 := C12.hi fun x hx => h13 x (F.hiOut (by decide) hx)
  have sp13 : reg n13 sp = S := by rw [r13, runBlock_reg _ _ _ sp v12.zero (by decide), r12]; exact sp11
  -- bytes 8..0x36 to `S + 0x1A`, and 0x37..0x60 to `S + 0x49`
  obtain ⟨n14, c14, u14, fr14, k14⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x1A) (src := S + BitVec.ofNat 32 0x210)
    (S := S) (N := 0x2F) (⟨u13.pc, m13, fun _ => rfl⟩ : St M13 FP n13 0x110 (reg n13)) C13.self C13.K fs_at_110 fs_at_114
    (by decide) (by decide) sp13
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, fsD5, upd, ↓reduceIte]; rw [r12, sp11]; rfl)
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, fsD5, upd, ↓reduceIte]; rw [r12, sp11]; rfl)
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, fsD5, upd, ↓reduceIte]; (try rw [v12.zero]); try rfl)
    ⟨C13.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inl (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr14' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x1A) 0x2F x 1 → n14.mem x = M13 x :=
    fun x a b => by rw [fr14 x a, copyBytes_sep b (Nat.le_refl _)]
  have C14 := C13.hi fun x hx => fr14' x (lo16 x hx) (F.hiOut (by decide) hx)
  have k14' := kc k14
  have sp14 : reg n14 sp = S := by rw [k14' sp (by decide)]; exact sp13
  obtain ⟨n15, c15, u15⟩ := u14.block fsD6 C14.self fsD6_end ⟨trivial, trivial, trivial, trivial⟩
  have r15 : ∀ q, reg n15 q = (runBlock fsD6 (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
  obtain ⟨n16, c16, u16, fr16, k16⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x49) (src := S + BitVec.ofNat 32 0x1AC)
    (S := S) (N := 0x2A) (⟨u15.pc, u15.mem, fun _ => rfl⟩ : St n14.mem FP n15 0x122 (reg n15)) C14.self C14.K fs_at_122 fs_at_126
    (by decide) (by decide) (by rw [r15, runBlock_reg _ _ _ sp u14.zero (by decide)]; exact sp14)
    (by rw [r15]; simp +decide only [runBlock, BInstr.run, fsD6, upd, ↓reduceIte]; rw [sp14]; rfl)
    (by rw [r15]; simp +decide only [runBlock, BInstr.run, fsD6, upd, ↓reduceIte]; rw [sp14]; rfl)
    (by rw [r15]; simp +decide only [runBlock, BInstr.run, fsD6, upd, ↓reduceIte]; (try rw [u14.zero]); try rfl)
    ⟨C14.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inl (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr16' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x49) 0x2A x 1 → n16.mem x = n14.mem x :=
    fun x a b => by rw [fr16 x a, copyBytes_sep b (Nat.le_refl _)]
  have C16 := C14.hi fun x hx => fr16' x (lo16 x hx) (F.hiOut (by decide) hx)
  have k16' := kc k16
  have KK : ∀ q : Fin 32, q.val ∈ [3, 4, 24, 26, 27] → reg n16 q = reg n q := fun q hq => by
    rw [k16' q (by revert hq; revert q; decide), r15, runBlock_reg _ _ _ q u14.zero (by simp only [fsD6]; revert hq; revert q; decide),
      k14' q (by revert hq; revert q; decide), r13, runBlock_reg _ _ _ q v12.zero (by simp only [fsD5]; revert hq; revert q; decide),
      r12, r11 q (by revert hq; revert q; decide), u10.regs, updz v9.zero (by revert hq; revert q; decide),
      K9 q (by revert hq; revert q; decide), r4, runBlock_reg _ _ _ q u3.zero (by simp only [fsD1]; revert hq; revert q; decide),
      K3 q (by revert hq; revert q; decide)]
  have sp16 : reg n16 sp = S := by
    rw [k16' sp (by decide), r15, runBlock_reg _ _ _ sp u14.zero (by decide)]; exact sp14
  -- where each byte came from
  have back9 : ∀ d, d + 1 ≤ 0x420 → (d + 1 ≤ 0x12 ∨ 0x1A ≤ d) → (d + 1 ≤ 0x1A ∨ 0x49 ≤ d) → (d + 1 ≤ 0x49 ∨ 0x73 ≤ d) →
      n16.mem (S + BitVec.ofNat 32 d) = n9.mem (S + BitVec.ofNat 32 d) := fun d h1 h2 h3 h4 => by
    rw [fr16' _ (l16b _ h1) (sq _ _ _ (by decide) h1 (by rcases h4 with h | h; exact .inr h; exact .inl h)),
      fr14' _ (l16b _ h1) (sq _ _ _ (by decide) h1 (by rcases h3 with h | h; exact .inr h; exact .inl h)),
      h13 _ (sq _ _ _ (by decide) h1 (by rcases h2 with h | h; exact .inr (by omega); exact .inl (by omega))),
      h12 _ (sq _ _ _ (by decide) h1 (by rcases h2 with h | h; exact .inr h; exact .inl (by omega)))]
  have m2I : ∀ j, j < 0x61 → M2 (inp + BitVec.ofNat 32 j) = M (inp + BitVec.ofNat 32 j) := fun j hj => by
    rw [h2 _ ((iF (by omega) (by decide)).symm), h1 _ ((iF (by omega) (by decide)).symm)]
  have n7I : ∀ j, j < 0x61 → n7.mem (inp + BitVec.ofNat 32 j) = M (inp + BitVec.ofNat 32 j) := fun j hj => by
    rw [fr7' _ ((iL (by omega)).symm) ((iF (by omega) (by decide)).symm), m2I j hj]
  have h9I : n9.mem (S + BitVec.ofNat 32 0x396) = n9.mem (S + BitVec.ofNat 32 0x396) := rfl
  refine ⟨n16, c1.trans (.cons d2 (c3.trans (c4.trans (.cons d5 (c6.trans (c7.trans (c8.trans (c9.trans (.cons d10
    (c11.trans (.cons d12 (c13.trans (c14.trans (c15.trans c16)))))))))))))), u16, C16, fun k hk => ?_,
    fun x h16 h12' h1AC h394 => ?_, sp16, KK⟩
  · match k, hk with
    | 0, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x12) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        h13 _ (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM12,
        dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x13) 1 (S + BitVec.ofNat 32 0x12) 1),
        memStore8_same, fr9' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inl (by decide))),
        fr7' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inl (by decide))),
        h2 _ (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM1,
        dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x395) 1 (S + BitVec.ofNat 32 0x394) 1),
        memStore8_same]
    | 1, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x13) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        h13 _ (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM12, memStore8_same,
        fr9' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inl (by decide))),
        fr7' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inl (by decide))),
        h2 _ (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM1, memStore8_same]
    | 2, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x14) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM13]
      rw [dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x19) 1 (S + BitVec.ofNat 32 0x14) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x18) 1 (S + BitVec.ofNat 32 0x14) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x17) 1 (S + BitVec.ofNat 32 0x14) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x16) 1 (S + BitVec.ofNat 32 0x14) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x15) 1 (S + BitVec.ofNat 32 0x14) 1), memStore8_same]
      rw [h9I, fr9' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inl (by decide))), fr7' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inl (by decide))), ← hM2, memStore8_same]
    | 3, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x15) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM13]
      rw [dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x19) 1 (S + BitVec.ofNat 32 0x15) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x18) 1 (S + BitVec.ofNat 32 0x15) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x17) 1 (S + BitVec.ofNat 32 0x15) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x16) 1 (S + BitVec.ofNat 32 0x15) 1), memStore8_same]
    | 4, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x16) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM13]
      rw [dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x19) 1 (S + BitVec.ofNat 32 0x16) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x18) 1 (S + BitVec.ofNat 32 0x16) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x17) 1 (S + BitVec.ofNat 32 0x16) 1), memStore8_same]
    | 5, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x17) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM13]
      rw [dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x19) 1 (S + BitVec.ofNat 32 0x17) 1), dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x18) 1 (S + BitVec.ofNat 32 0x17) 1), memStore8_same]
    | 6, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x18) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM13]
      rw [dq_st8 (sq _ _ _ (by decide) (by decide) (.inr (by decide)) : Sep (S + BitVec.ofNat 32 0x19) 1 (S + BitVec.ofNat 32 0x18) 1), memStore8_same]
    | 7, _ =>
      show n16.mem (S + BitVec.ofNat 32 0x19) = _
      rw [fr16' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))),
        fr14' _ (l16b _ (by decide)) (sq _ _ _ (by decide) (by decide) (.inr (by decide))), ← hM13]
      rw [memStore8_same]
    | k + 8, hk =>
      by_cases hj : k < 0x2F
      · rw [show 0x12 + (k + 8) = 0x1A + k by omega, ← add_ofNat_assoc,
          fr16' _ (by rw [add_ofNat_assoc]; exact l16b _ (by omega))
            (by rw [add_ofNat_assoc]; exact sq _ _ _ (by decide) (by omega) (.inr (by omega))),
          fr14 _ (by rw [add_ofNat_assoc]; exact l16b _ (by omega)), cp_at hj (by decide), add_ofNat_assoc,
          h13 _ (sq _ _ _ (by decide) (by omega) (.inl (by omega))), h12 _ (sq _ _ _ (by decide) (by omega) (.inl (by omega))),
          fr9' _ (l16b _ (by omega)) (sq _ _ _ (by decide) (by omega) (.inl (by omega))),
          ← add_ofNat_assoc, fr7 _ (by rw [add_ofNat_assoc]; exact l16b _ (by omega)), cp_at hj (by decide),
          add_ofNat_assoc, m2I _ (by omega), show 8 + k = k + 8 by omega]
      · rw [show 0x12 + (k + 8) = 0x49 + (k - 0x2F) by omega, ← add_ofNat_assoc,
          fr16 _ (by rw [add_ofNat_assoc]; exact l16b _ (by omega)), cp_at (by omega) (by decide), add_ofNat_assoc,
          fr14' _ (l16b _ (by omega)) (sq _ _ _ (by decide) (by omega) (.inl (by omega))),
          h13 _ (sq _ _ _ (by decide) (by omega) (.inl (by omega))), h12 _ (sq _ _ _ (by decide) (by omega) (.inl (by omega))),
          ← add_ofNat_assoc, fr9 _ (by rw [add_ofNat_assoc]; exact l16b _ (by omega)), cp_at (by omega) (by decide),
          add_ofNat_assoc, n7I _ (by omega), show 0x37 + (k - 0x2F) = k + 8 by omega]
  · have sub : ∀ {c l : Nat} (b : Word) (L : Nat), Sep b L x 1 → c + l ≤ L → Sep (b + BitVec.ofNat 32 c) l x 1 :=
      fun {c l} b L h hl => h.sub (c := c) (l := l) hl
    rw [fr16' x h16 (by have := sub (c := 0x37) (l := 0x2A) _ _ h12' (by decide); rwa [add_ofNat_assoc] at this),
      fr14' x h16 (by have := sub (c := 8) (l := 0x2F) _ _ h12' (by decide); rwa [add_ofNat_assoc] at this),
      h13 x (by have := sub (c := 2) (l := 6) _ _ h12' (by decide); rwa [add_ofNat_assoc] at this),
      h12 x (by have := sub (c := 0) (l := 2) _ _ h12' (by decide); rwa [add_ofNat_zero] at this),
      fr9' x h16 (by have := sub (c := 0) (l := 0x2A) _ _ h1AC (by decide); rwa [add_ofNat_zero] at this),
      fr7' x h16 (by have := sub (c := 0x64) (l := 0x2F) _ _ h1AC (by decide); rwa [add_ofNat_assoc] at this),
      h2 x (by have := sub (c := 2) (l := 1) _ _ h394 (by decide); rwa [add_ofNat_assoc] at this),
      h1 x (by have := sub (c := 0) (l := 2) _ _ h394 (by decide); rwa [add_ofNat_zero] at this)]

def fsT1 : List BInstr := [.lbu (22 : Fin 32) sp 0x12, .alu .add a0 x0 (22 : Fin 32)]
def fsT2 : List BInstr := [.aluImm .add (19 : Fin 32) sp 0x13, .alu .add a0 x0 (22 : Fin 32)]
def fsT3 : List BInstr := [.aluImm .and (8 : Fin 32) a0 0xFE, .alu .add a0 x0 (22 : Fin 32)]
def fsT4 : List BInstr := [.aluImm .add a1 x0 0x2, .aluImm .and a0 a0 0xFF]
def fsT5 : List BInstr := [.aluImm .add a1 x0 0x5]
theorem fsT1_end : blockEnd p384FromSec1Code 0x12A fsT1 = some 0x130 := by decide
theorem fsT2_end : blockEnd p384FromSec1Code 0x158 fsT2 = some 0x15E := by decide
theorem fsT3_end : blockEnd p384FromSec1Code 0x166 fsT3 = some 0x16C := by decide
theorem fsT4_end : blockEnd p384FromSec1Code 0x174 fsT4 = some 0x17A := by decide
theorem fsT5_end : blockEnd p384FromSec1Code 0x19A fsT5 = some 0x19C := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **The tag dispatch**, from 0x12A to the uncompressed branch at 0x2DC,
for the tag 4 at `S + 0x12`: `is_identity` is false, and `tag` is neither
compressed nor compact. -/
theorem fs_stD {M : Word → BitVec 8} {n : Machine} {S : Word} (C : FsCode M) (F : Fr S 0x420)
    (s : St M FP n 0x12A (reg n)) (rsp : reg n sp = S) (ht : M (S + BitVec.ofNat 32 0x12) = 4) :
    ∃ n', Steps n n' ∧ St n'.mem FP n' 0x2DC (reg n') ∧ FsCode n'.mem ∧
      (∀ x, Sep (S + 0xFFFFFFB0) 0x50 x 1 → n'.mem x = M x) ∧ reg n' sp = S ∧
      reg n' (19 : Fin 32) = S + BitVec.ofNat 32 0x13 ∧ reg n' (22 : Fin 32) = (4 : BitVec 8).zeroExtend 32 ∧
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
  obtain ⟨n1, c1, u1⟩ := s.block fsT1 C.self fsT1_end ⟨trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock fsT1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have e22 : reg n1 (22 : Fin 32) = (4 : BitVec 8).zeroExtend 32 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, fsT1, upd, ↓reduceIte]; rw [rsp]
    show (M (S + BitVec.ofNat 32 0x12)).zeroExtend 32 = _; rw [ht]
  obtain ⟨n2, c2, u2, a2, sp2, k2, fr2⟩ := c_isid (t := 4) (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M FP n1 0x130 (reg n1))
    C.self C.K F fs_at_130 fs_at_134 (by decide) (by decide) (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, fsT1, upd, ↓reduceIte]; rw [← e22, r1]
        simp +decide only [runBlock, BInstr.run, fsT1, upd, ↓reduceIte]; exact BitVec.zero_add _) ok4
  have C2 := C.hi fun x hx => fr2 x (loA x hx)
  obtain ⟨n3, d3, u3⟩ := u2.taken C2.self 0x158 fs_at_138 (by decide) (by
    show branchTaken .beq (reg n2 a0) 0 = true; rw [a2]; decide)
  have K2 : ∀ q : Fin 32, q.val ∈ [3, 4, 24, 26, 27] → reg n3 q = reg n q := fun q hq => by
    rw [u3.regs, k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), r1,
      runBlock_reg _ _ _ q hz (by simp only [fsT1]; revert hq; revert q; decide)]
  have e322 : reg n3 (22 : Fin 32) = (4 : BitVec 8).zeroExtend 32 := by
    rw [u3.regs, k2 22 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact e22
  have sp3 : reg n3 sp = S := by rw [u3.regs]; exact sp2
  obtain ⟨n4, c4, u4⟩ := u3.self.block fsT2 C2.self fsT2_end ⟨trivial, trivial, trivial⟩
  have r4 : ∀ q, reg n4 q = (runBlock fsT2 (n2.mem, reg n3)).2 q := fun q => by rw [u4.regs]
  obtain ⟨n5, c5, u5, a5, sp5, k5, fr5⟩ := c_tag (t := 4) (⟨u4.pc, u4.mem, fun _ => rfl⟩ : St n2.mem FP n4 0x15E (reg n4))
    C2.self C2.K F fs_at_15e fs_at_162 (by decide) (by decide)
    (by rw [r4, runBlock_reg _ _ _ sp u3.self.zero (by decide)]; exact sp3)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, fsT2, upd, ↓reduceIte]; rw [e322]; exact BitVec.zero_add _) ok4
  have C5 := C2.hi fun x hx => fr5 x (sub40 (loA x hx))
  obtain ⟨n6, c6, u6⟩ := u5.block fsT3 C5.self fsT3_end ⟨trivial, trivial, trivial⟩
  have r6 : ∀ q, reg n6 q = (runBlock fsT3 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  have K5 : ∀ q : Fin 32, q.val ∈ [3, 4, 22, 24, 26, 27] → reg n5 q = reg n3 q := fun q hq => by
    rw [k5 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), r4,
      runBlock_reg _ _ _ q u3.self.zero (by simp only [fsT2]; revert hq; revert q; decide)]
  obtain ⟨n7, c7, u7, a7, sp7, k7, fr7⟩ := c_tag (t := 4) (⟨u6.pc, u6.mem, fun _ => rfl⟩ : St n5.mem FP n6 0x16C (reg n6))
    C5.self C5.K F fs_at_16c fs_at_170 (by decide) (by decide)
    (by rw [r6, runBlock_reg _ _ _ sp u5.zero (by decide)]; exact sp5)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, fsT3, upd, ↓reduceIte]; rw [K5 22 (by decide), e322]
        exact BitVec.zero_add _) ok4
  have C7 := C5.hi fun x hx => fr7 x (sub40 (loA x hx))
  have e78 : reg n7 (8 : Fin 32) = aluEval .and ((4 : BitVec 8).zeroExtend 32) 0xFE := by
    rw [k7 8 (by decide) (by decide) (by decide) (by decide) (by decide), r6]
    simp +decide only [runBlock, BInstr.run, fsT3, upd, ↓reduceIte]; rw [a5]
  obtain ⟨n8, c8, u8⟩ := u7.block fsT4 C7.self fsT4_end ⟨trivial, trivial, trivial⟩
  have r8 : ∀ q, reg n8 q = (runBlock fsT4 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
  obtain ⟨n9, d9, u9⟩ := (⟨u8.pc, u8.mem, fun _ => rfl⟩ : St n7.mem FP n8 0x17A (reg n8)).taken C7.self 0x19A fs_at_17a
    (by decide) (by
      show branchTaken .bne (reg n8 (8 : Fin 32)) (reg n8 a1) = true
      rw [r8, r8]; simp +decide only [runBlock, BInstr.run, fsT4, upd, ↓reduceIte]; rw [e78, u7.zero]; decide)
  obtain ⟨n10, c10, u10⟩ := u9.self.block fsT5 C7.self fsT5_end ⟨trivial, trivial⟩
  have r10 : ∀ q, reg n10 q = (runBlock fsT5 (n7.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  obtain ⟨n11, d11, u11⟩ := (⟨u10.pc, u10.mem, fun _ => rfl⟩ : St n7.mem FP n10 0x19C (reg n10)).taken C7.self 0x2DC
    fs_at_19c (by decide) (by
      show branchTaken .bne (reg n10 a0) (reg n10 a1) = true
      rw [r10, r10]; simp +decide only [runBlock, BInstr.run, fsT5, upd, ↓reduceIte]; rw [u9.regs, r8]
      simp +decide only [runBlock, BInstr.run, fsT4, upd, ↓reduceIte]; rw [a7, u9.self.zero]; decide)
  have KK : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 19, 22, 24, 26, 27] → reg n11 q = reg n7 q := fun q hq => by
    rw [u11.regs, r10, runBlock_reg _ _ _ q u9.self.zero (by simp only [fsT5]; revert hq; revert q; decide), u9.regs, r8,
      runBlock_reg _ _ _ q u7.zero (by simp only [fsT4]; revert hq; revert q; decide)]
  have K7 : ∀ q : Fin 32, q.val ∈ [3, 4, 19, 22, 24, 26, 27] → reg n7 q = reg n5 q := fun q hq => by
    rw [k7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), r6,
      runBlock_reg _ _ _ q u5.zero (by simp only [fsT3]; revert hq; revert q; decide)]
  refine ⟨n11, c1.trans (c2.trans (.cons d3 (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (.cons d9 (c10.trans
    (.single d11)))))))))), ⟨u11.pc, by rw [u11.mem], fun _ => rfl⟩, by rw [u11.mem]; exact C7,
    fun x hx => by rw [u11.mem, fr7 x (sub40 hx), fr5 x (sub40 hx), fr2 x hx], ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [KK sp (by decide)]; exact sp7
  · rw [KK 19 (by decide), K7 19 (by decide), k5 19 (by decide) (by decide) (by decide) (by decide) (by decide), r4]
    simp +decide only [runBlock, BInstr.run, fsT2, upd, ↓reduceIte]; rw [sp3]; rfl
  · rw [KK 22 (by decide), K7 22 (by decide), K5 22 (by decide)]; exact e322
  · rw [KK q (by revert hq; revert q; decide), K7 q (by revert hq; revert q; decide), K5 q (by revert hq; revert q; decide),
      K2 q (by revert hq; revert q; decide)]

/-- `v` in Montgomery form when it is below `p`, else 0: what `from_repr`
and the select after it leave. -/
def fsMont (v : Nat) : Nat := if v < p384 then v * 2 ^ 384 % p384 else 0

/-- Whether `v` is below `p`, as `from_repr`'s choice. -/
def fsOk (v : Nat) : Word := if v < p384 then 1 else 0

def fsY1 : List BInstr := [.aluImm .add a1 sp 0x43, .aluImm .add a0 sp 0x210]
def fsY2 : List BInstr := [.aluImm .add a0 sp 0x2D4, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0]
def fsY3 : List BInstr :=
  [.lbu (18 : Fin 32) sp 0x240, .aluImm .add a0 sp 0x364, .aluImm .add a1 sp 0x2D4, .aluImm .add a2 sp 0x210,
   .alu .add a3 x0 (18 : Fin 32)]
def fsX1 : List BInstr := [.aluImm .add a0 sp 0x144, .alu .add a1 x0 (19 : Fin 32)]
def fsX2 : List BInstr := [.aluImm .add a0 sp 0x304, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0]
def fsX3 : List BInstr :=
  [.lbu (19 : Fin 32) sp 0x174, .aluImm .add a0 sp 0x3C4, .aluImm .add a1 sp 0x304, .aluImm .add a2 sp 0x144,
   .alu .add a3 x0 (19 : Fin 32)]
theorem fsY1_end : blockEnd p384FromSec1Code 0x2DC fsY1 = some 0x2E2 := by decide
theorem fsY2_end : blockEnd p384FromSec1Code 0x2EA fsY2 = some 0x2F2 := by decide
theorem fsY3_end : blockEnd p384FromSec1Code 0x2FA fsY3 = some 0x306 := by decide
theorem fsX1_end : blockEnd p384FromSec1Code 0x30E fsX1 = some 0x312 := by decide
theorem fsX2_end : blockEnd p384FromSec1Code 0x31A fsX2 = some 0x322 := by decide
theorem fsX3_end : blockEnd p384FromSec1Code 0x32A fsX3 = some 0x336 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **Decoding `y`**, from 0x2DC to 0x30E: `from_repr` on the 48 bytes at
`S + 0x43`, then the select of its result or zero into `S + 0x364`; `s2`
holds the choice. -/
theorem fs_decY {M : Word → BitVec 8} {n : Machine} {S : Word} (C : FsCode M) (D : P3Data M) (F : Fr S 0x420)
    (s : St M FP n 0x2DC (reg n)) (rsp : reg n sp = S) :
    ∃ n', Steps n n' ∧ St n'.mem FP n' 0x30E (reg n') ∧ FsCode n'.mem ∧ P3Data n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x364) 12 = fsMont (beNat (memBytes M (S + BitVec.ofNat 32 0x43) 48)) ∧
      reg n' (18 : Fin 32) = fsOk (beNat (memBytes M (S + BitVec.ofNat 32 0x43) 48)) ∧
      (∀ x, Sep (S + 0xFFFFFE60) 0x1A0 x 1 → Sep (S + BitVec.ofNat 32 0x210) 0x31 x 1 →
        Sep (S + BitVec.ofNat 32 0x2D4) 0x30 x 1 → Sep (S + BitVec.ofNat 32 0x364) 0x30 x 1 → n'.mem x = M x) ∧
      reg n' sp = S ∧ ∀ q : Fin 32, q.val ∈ [3, 4, 19, 22, 24, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hbF : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have hb60 : (S + 0xFFFFFFA0).toNat = S.toNat - 0x60 := F.below 0x60 (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block fsY1 C.self fsY1_end ⟨trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock fsY1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, ok2, bad2, fr2, sp2, k2⟩ := c_frp (out := S + BitVec.ofNat 32 0x210)
    (inp := S + BitVec.ofNat 32 0x43) (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M FP n1 0x2E2 (reg n1)) C.self C.K D F
    fs_at_2e2 fs_at_2e6 (by decide) (by decide) (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, fsY1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, fsY1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (co := 0x210) (by decide) rfl
    ((sep_of_le (by rw [hbF, F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega)).symm)
  have hv2 : accV n2.mem (S + BitVec.ofNat 32 0x210) 12 = fsMont (beNat (memBytes M (S + BitVec.ofNat 32 0x43) 48)) ∧
      n2.mem (S + BitVec.ofNat 32 0x210 + 0x30) = (if beNat (memBytes M (S + BitVec.ofNat 32 0x43) 48) < p384 then 1 else 0) := by
    unfold fsMont
    by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x43) 48) < p384
    · obtain ⟨o1, olt, ocg⟩ := ok2 hx
      rw [ite_eq_left hx, ite_eq_left hx]
      have hR : accV M (PARAMS + BitVec.ofNat 32 0x60) 12 = dataVal p384ParamsData 0x60 12 :=
        code_accV D.params 0x60 12 (by decide)
      rw [hR] at ocg
      exact ⟨frp_val olt ocg, o1⟩
    · obtain ⟨o0, a0'⟩ := bad2 (Nat.le_of_not_lt hx)
      rw [ite_eq_right hx, ite_eq_right hx]; exact ⟨a0', o0⟩
  clear ok2 bad2
  have h2hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n2.mem x = M x := fun x hx =>
    fr2 x (sep_of_le (by rw [hbF]; omega) (by have := x.isLt; omega)) (F.hiOut (by decide) hx)
  have C2 := C.hi h2hi
  have D2 : P3Data n2.mem := D.of F fun x hx => fr2 x (hx.sub (c := 0) (l := 0x1A0) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h) (fr_inFrame (by decide) hx)
  obtain ⟨n3, c3, u3⟩ := u2.block fsY2 C2.self fsY2_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock fsY2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, mem4, k4⟩ := c_memset (dst := S + BitVec.ofNat 32 0x2D4) (b := 0) (N := 48)
    (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem FP n3 0x2F2 (reg n3)) C2.self C2.K fs_at_2f2 fs_at_2f6 (by decide) (by decide)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsY2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsY2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsY2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [F.at _ (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  have h4 : ∀ x, Sep (S + BitVec.ofNat 32 0x2D4) 48 x 1 → n4.mem x = n2.mem x := fun x hx => by
    rw [mem4, fillBytes_sep hx (Nat.le_refl _)]
  have C4 := C2.hi fun x hx => h4 x (F.hiOut (by decide) hx)
  have k4' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg n4 q = reg n2 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 hr => by
      rw [k4 q h0 h2 h3 h4 h5 h6 hr, r3, runBlock_reg _ _ _ q u2.zero (by simp only [fsY2]; revert h0 h1 h2; revert q; decide)]
  have sp4 : reg n4 sp = S := by
    rw [k4' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp2
  have a70 : n4.mem (S + BitVec.ofNat 32 0x210 + 0x30) = n2.mem (S + BitVec.ofNat 32 0x210 + 0x30) :=
    h4 _ (sepS S (c := 0x2D4) (n := 48) (d := 0x240) (k := 1) (.inr (by decide)) (by decide) (by decide) |> fun h => by
      rwa [show S + BitVec.ofNat 32 0x240 = S + BitVec.ofNat 32 0x210 + 0x30 from by rw [BitVec.add_assoc]; rfl] at h)
  obtain ⟨n5, c5, u5⟩ := u4.block fsY3 C4.self fsY3_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock fsY3 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have e18 : reg n5 (18 : Fin 32) = (n2.mem (S + BitVec.ofNat 32 0x210 + 0x30)).zeroExtend 32 := by
    rw [r5]; simp +decide only [runBlock, BInstr.run, fsY3, upd, ↓reduceIte]; rw [sp4, ← a70]
    rw [show S + BitVec.ofNat 32 0x210 + 0x30 = S + 0x240 from by rw [BitVec.add_assoc]; rfl]
  have hc01 : (n2.mem (S + BitVec.ofNat 32 0x210 + 0x30)).zeroExtend 32 = (0 : Word) ∨
      (n2.mem (S + BitVec.ofNat 32 0x210 + 0x30)).zeroExtend 32 = (1 : Word) := by
    by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x43) 48) < p384
    · rw [hv2.2, ite_eq_left hx]; exact .inr rfl
    · rw [hv2.2, ite_eq_right hx]; exact .inl rfl
  obtain ⟨n6, c6, u6, vals6, fr6, sp6, k6⟩ := c_csel (out := S + BitVec.ofNat 32 0x364) (a := S + BitVec.ofNat 32 0x2D4)
    (b := S + BitVec.ofNat 32 0x210) (c := (n2.mem (S + BitVec.ofNat 32 0x210 + 0x30)).zeroExtend 32)
    (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem FP n5 0x306 (reg n5)) C4.self C4.K F fs_at_306 fs_at_30a (by decide) (by decide)
    (by rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, fsY3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, fsY3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, fsY3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, fsY3, upd, ↓reduceIte]; rw [sp4]
        show aluEval .add 0 ((n4.mem (S + 0x240)).zeroExtend 32) = _
        rw [show (S + 0x240 : Word) = S + BitVec.ofNat 32 0x210 + 0x30 from by rw [BitVec.add_assoc]; rfl, a70]
        exact BitVec.zero_add _)
    hc01 (co := 0x364) (ca := 0x2D4) (cb := 0x210) (by decide) (by decide) (by decide) rfl rfl rfl (by decide)
  have h6hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n6.mem x = M x := fun x hx => by
    rw [fr6 x (sep_of_le (by rw [hb60]; omega) (by have := x.isLt; omega)) (F.hiOut (c := 0x364) (n := 48) (by decide) hx),
      h4 x (F.hiOut (by decide) hx), h2hi x hx]
  have frame : ∀ x, Sep (S + 0xFFFFFE60) 0x1A0 x 1 → Sep (S + BitVec.ofNat 32 0x210) 0x31 x 1 →
      Sep (S + BitVec.ofNat 32 0x2D4) 0x30 x 1 → Sep (S + BitVec.ofNat 32 0x364) 0x30 x 1 → n6.mem x = M x := by
    intro x hF h210 h2D4 h364
    have h60 : Sep (S + 0xFFFFFFA0) 0x60 x 1 := by
      have := hF.sub (c := 0x140) (l := 0x60) (by decide)
      rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x140 = S + 0xFFFFFFA0 by rw [BitVec.add_assoc]; rfl] at this
    rw [fr6 x h60 h364, h4 x h2D4, fr2 x hF h210]
  have D6 : P3Data n6.mem := D.of F fun x hx => frame x (hx.sub (c := 0) (l := 0x1A0) (by decide) |> fun h => by
      rwa [add_ofNat_zero] at h) (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx)
  have e618 : reg n6 (18 : Fin 32) = (n2.mem (S + BitVec.ofNat 32 0x210 + 0x30)).zeroExtend 32 := by
    rw [k6 18 (by decide), e18]
  refine ⟨n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))), u6, C.hi h6hi, D6, ?_, ?_, frame, sp6, fun q hq => ?_⟩
  · by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x43) 48) < p384
    · have hc1 : (n2.mem (S + BitVec.ofNat 32 0x210 + 0x30)).zeroExtend 32 = (1 : Word) := by
        rw [hv2.2, ite_eq_left hx]; rfl
      rw [← hv2.1]
      exact accV_congr2 12 fun i hi => by
        rw [vals6 i hi, ite_eq_left hc1]
        exact memLoad32_congr fun q hq => by
          rw [add_ofNat_assoc, add_ofNat_assoc]
          exact h4 _ (sepS S (.inr (by omega)) (by decide) (by omega))
    · have hc0 : (n2.mem (S + BitVec.ofNat 32 0x210 + 0x30)).zeroExtend 32 = (0 : Word) := by
        rw [hv2.2, ite_eq_right hx]; rfl
      unfold fsMont; rw [ite_eq_right hx]
      exact accV_zero 12 fun i hi => by
        rw [vals6 i hi, ite_eq_right (by rw [hc0]; decide), mem4]
        exact fill_word0 (by omega) (by decide)
  · rw [e618, hv2.2]; unfold fsOk
    by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x43) 48) < p384
    · rw [ite_eq_left hx, ite_eq_left hx]; rfl
    · rw [ite_eq_right hx, ite_eq_right hx]; rfl
  · rw [k6 q (by revert hq; revert q; decide), r5, runBlock_reg _ _ _ q u4.zero (by simp only [fsY3]; revert hq; revert q; decide),
      k4' q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide), r1,
      runBlock_reg _ _ _ q hz (by simp only [fsY1]; revert hq; revert q; decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **Decoding `x`**, from 0x30E to 0x33E: `from_repr` on the 48 bytes at
`S + 0x13`, then the select of its result or zero into `S + 0x3C4`; `s3`
holds the choice. -/
theorem fs_decX {M : Word → BitVec 8} {n : Machine} {S : Word} (C : FsCode M) (D : P3Data M) (F : Fr S 0x420)
    (s : St M FP n 0x30E (reg n)) (rsp : reg n sp = S) (r19 : reg n (19 : Fin 32) = S + BitVec.ofNat 32 0x13) :
    ∃ n', Steps n n' ∧ St n'.mem FP n' 0x33E (reg n') ∧ FsCode n'.mem ∧ P3Data n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x3C4) 12 = fsMont (beNat (memBytes M (S + BitVec.ofNat 32 0x13) 48)) ∧
      reg n' (19 : Fin 32) = fsOk (beNat (memBytes M (S + BitVec.ofNat 32 0x13) 48)) ∧
      (∀ x, Sep (S + 0xFFFFFE60) 0x1A0 x 1 → Sep (S + BitVec.ofNat 32 0x144) 0x31 x 1 →
        Sep (S + BitVec.ofNat 32 0x304) 0x30 x 1 → Sep (S + BitVec.ofNat 32 0x3C4) 0x30 x 1 → n'.mem x = M x) ∧
      reg n' sp = S ∧ ∀ q : Fin 32, q.val ∈ [3, 4, 18, 22, 24, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hbF : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have hb60 : (S + 0xFFFFFFA0).toNat = S.toNat - 0x60 := F.below 0x60 (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block fsX1 C.self fsX1_end ⟨trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock fsX1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, ok2, bad2, fr2, sp2, k2⟩ := c_frp (out := S + BitVec.ofNat 32 0x144)
    (inp := S + BitVec.ofNat 32 0x13) (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M FP n1 0x312 (reg n1)) C.self C.K D F
    fs_at_312 fs_at_316 (by decide) (by decide) (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, fsX1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, fsX1, upd, ↓reduceIte]; rw [r19]; exact BitVec.zero_add _)
    (co := 0x144) (by decide) rfl
    ((sep_of_le (by rw [hbF, F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega)).symm)
  have hv2 : accV n2.mem (S + BitVec.ofNat 32 0x144) 12 = fsMont (beNat (memBytes M (S + BitVec.ofNat 32 0x13) 48)) ∧
      n2.mem (S + BitVec.ofNat 32 0x144 + 0x30) = (if beNat (memBytes M (S + BitVec.ofNat 32 0x13) 48) < p384 then 1 else 0) := by
    unfold fsMont
    by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x13) 48) < p384
    · obtain ⟨o1, olt, ocg⟩ := ok2 hx
      rw [ite_eq_left hx, ite_eq_left hx]
      have hR : accV M (PARAMS + BitVec.ofNat 32 0x60) 12 = dataVal p384ParamsData 0x60 12 :=
        code_accV D.params 0x60 12 (by decide)
      rw [hR] at ocg
      exact ⟨frp_val olt ocg, o1⟩
    · obtain ⟨o0, a0'⟩ := bad2 (Nat.le_of_not_lt hx)
      rw [ite_eq_right hx, ite_eq_right hx]; exact ⟨a0', o0⟩
  clear ok2 bad2
  have h2hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n2.mem x = M x := fun x hx =>
    fr2 x (sep_of_le (by rw [hbF]; omega) (by have := x.isLt; omega)) (F.hiOut (by decide) hx)
  have C2 := C.hi h2hi
  have D2 : P3Data n2.mem := D.of F fun x hx => fr2 x (hx.sub (c := 0) (l := 0x1A0) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h) (fr_inFrame (by decide) hx)
  obtain ⟨n3, c3, u3⟩ := u2.block fsX2 C2.self fsX2_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock fsX2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, mem4, k4⟩ := c_memset (dst := S + BitVec.ofNat 32 0x304) (b := 0) (N := 48)
    (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem FP n3 0x322 (reg n3)) C2.self C2.K fs_at_322 fs_at_326 (by decide) (by decide)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsX2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsX2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsX2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [F.at _ (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  have h4 : ∀ x, Sep (S + BitVec.ofNat 32 0x304) 48 x 1 → n4.mem x = n2.mem x := fun x hx => by
    rw [mem4, fillBytes_sep hx (Nat.le_refl _)]
  have C4 := C2.hi fun x hx => h4 x (F.hiOut (by decide) hx)
  have k4' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg n4 q = reg n2 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 hr => by
      rw [k4 q h0 h2 h3 h4 h5 h6 hr, r3, runBlock_reg _ _ _ q u2.zero (by simp only [fsX2]; revert h0 h1 h2; revert q; decide)]
  have sp4 : reg n4 sp = S := by
    rw [k4' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp2
  have a70 : n4.mem (S + BitVec.ofNat 32 0x144 + 0x30) = n2.mem (S + BitVec.ofNat 32 0x144 + 0x30) :=
    h4 _ (sepS S (c := 0x304) (n := 48) (d := 0x174) (k := 1) (.inr (by decide)) (by decide) (by decide) |> fun h => by
      rwa [show S + BitVec.ofNat 32 0x174 = S + BitVec.ofNat 32 0x144 + 0x30 from by rw [BitVec.add_assoc]; rfl] at h)
  obtain ⟨n5, c5, u5⟩ := u4.block fsX3 C4.self fsX3_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock fsX3 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have e19x : reg n5 (19 : Fin 32) = (n2.mem (S + BitVec.ofNat 32 0x144 + 0x30)).zeroExtend 32 := by
    rw [r5]; simp +decide only [runBlock, BInstr.run, fsX3, upd, ↓reduceIte]; rw [sp4, ← a70]
    rw [show S + BitVec.ofNat 32 0x144 + 0x30 = S + 0x174 from by rw [BitVec.add_assoc]; rfl]
  have hc01 : (n2.mem (S + BitVec.ofNat 32 0x144 + 0x30)).zeroExtend 32 = (0 : Word) ∨
      (n2.mem (S + BitVec.ofNat 32 0x144 + 0x30)).zeroExtend 32 = (1 : Word) := by
    by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x13) 48) < p384
    · rw [hv2.2, ite_eq_left hx]; exact .inr rfl
    · rw [hv2.2, ite_eq_right hx]; exact .inl rfl
  obtain ⟨n6, c6, u6, vals6, fr6, sp6, k6⟩ := c_csel (out := S + BitVec.ofNat 32 0x3C4) (a := S + BitVec.ofNat 32 0x304)
    (b := S + BitVec.ofNat 32 0x144) (c := (n2.mem (S + BitVec.ofNat 32 0x144 + 0x30)).zeroExtend 32)
    (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem FP n5 0x336 (reg n5)) C4.self C4.K F fs_at_336 fs_at_33a (by decide) (by decide)
    (by rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, fsX3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, fsX3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, fsX3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, fsX3, upd, ↓reduceIte]; rw [sp4]
        show aluEval .add 0 ((n4.mem (S + 0x174)).zeroExtend 32) = _
        rw [show (S + 0x174 : Word) = S + BitVec.ofNat 32 0x144 + 0x30 from by rw [BitVec.add_assoc]; rfl, a70]
        exact BitVec.zero_add _)
    hc01 (co := 0x3C4) (ca := 0x304) (cb := 0x144) (by decide) (by decide) (by decide) rfl rfl rfl (by decide)
  have h6hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n6.mem x = M x := fun x hx => by
    rw [fr6 x (sep_of_le (by rw [hb60]; omega) (by have := x.isLt; omega)) (F.hiOut (c := 0x3C4) (n := 48) (by decide) hx),
      h4 x (F.hiOut (by decide) hx), h2hi x hx]
  have frame : ∀ x, Sep (S + 0xFFFFFE60) 0x1A0 x 1 → Sep (S + BitVec.ofNat 32 0x144) 0x31 x 1 →
      Sep (S + BitVec.ofNat 32 0x304) 0x30 x 1 → Sep (S + BitVec.ofNat 32 0x3C4) 0x30 x 1 → n6.mem x = M x := by
    intro x hF h210 h2D4 h364
    have h60 : Sep (S + 0xFFFFFFA0) 0x60 x 1 := by
      have := hF.sub (c := 0x140) (l := 0x60) (by decide)
      rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x140 = S + 0xFFFFFFA0 by rw [BitVec.add_assoc]; rfl] at this
    rw [fr6 x h60 h364, h4 x h2D4, fr2 x hF h210]
  have D6 : P3Data n6.mem := D.of F fun x hx => frame x (hx.sub (c := 0) (l := 0x1A0) (by decide) |> fun h => by
      rwa [add_ofNat_zero] at h) (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx)
  have e619 : reg n6 (19 : Fin 32) = (n2.mem (S + BitVec.ofNat 32 0x144 + 0x30)).zeroExtend 32 := by
    rw [k6 19 (by decide), e19x]
  refine ⟨n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))), u6, C.hi h6hi, D6, ?_, ?_, frame, sp6, fun q hq => ?_⟩
  · by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x13) 48) < p384
    · have hc1 : (n2.mem (S + BitVec.ofNat 32 0x144 + 0x30)).zeroExtend 32 = (1 : Word) := by
        rw [hv2.2, ite_eq_left hx]; rfl
      rw [← hv2.1]
      exact accV_congr2 12 fun i hi => by
        rw [vals6 i hi, ite_eq_left hc1]
        exact memLoad32_congr fun q hq => by
          rw [add_ofNat_assoc, add_ofNat_assoc]
          exact h4 _ (sepS S (.inr (by omega)) (by decide) (by omega))
    · have hc0 : (n2.mem (S + BitVec.ofNat 32 0x144 + 0x30)).zeroExtend 32 = (0 : Word) := by
        rw [hv2.2, ite_eq_right hx]; rfl
      unfold fsMont; rw [ite_eq_right hx]
      exact accV_zero 12 fun i hi => by
        rw [vals6 i hi, ite_eq_right (by rw [hc0]; decide), mem4]
        exact fill_word0 (by omega) (by decide)
  · rw [e619, hv2.2]; unfold fsOk
    by_cases hx : beNat (memBytes M (S + BitVec.ofNat 32 0x13) 48) < p384
    · rw [ite_eq_left hx, ite_eq_left hx]; rfl
    · rw [ite_eq_right hx, ite_eq_right hx]; rfl
  · rw [k6 q (by revert hq; revert q; decide), r5, runBlock_reg _ _ _ q u4.zero (by simp only [fsX3]; revert hq; revert q; decide),
      k4' q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide), r1,
      runBlock_reg _ _ _ q hz (by simp only [fsX1]; revert hq; revert q; decide)]

def fsF1 : List BInstr := [.aluImm .add a0 sp 0x334, .aluImm .add a1 sp 0x364, .aluImm .add a2 sp 0x364]
def fsF2 : List BInstr := [.aluImm .add a0 sp 0xDC, .aluImm .add a1 sp 0x3C4, .aluImm .add a2 sp 0x3C4]
def fsF3 : List BInstr := [.aluImm .add a0 sp 0x1AC, .aluImm .add a1 sp 0xDC, .aluImm .add a2 sp 0x3C4]
def fsF4 : List BInstr := [.lui a1 0x3FCC4000, .aluImm .add a1 a1 0x74, .aluImm .add a0 sp 0xDC, .aluImm .add a2 sp 0x3C4]
def fsF5 : List BInstr := [.aluImm .add a0 sp 0x394, .aluImm .add a1 sp 0x1AC, .aluImm .add a2 sp 0xDC]
def fsF6 : List BInstr := [.lui a2 0x3FCC4000, .aluImm .add a2 a2 0xA4, .aluImm .add a0 sp 0x1AC, .aluImm .add a1 sp 0x394]
def fsF7 : List BInstr := [.aluImm .add a0 sp 0xDC, .aluImm .add a1 sp 0x3C4, .aluImm .add a2 x0 0x30]
def fsF8 : List BInstr := [.aluImm .add a0 sp 0x10C, .aluImm .add a1 sp 0x364, .aluImm .add a2 x0 0x30]
theorem fsF1_end : blockEnd p384FromSec1Code 0x33E fsF1 = some 0x344 := by decide
theorem fsF2_end : blockEnd p384FromSec1Code 0x34C fsF2 = some 0x352 := by decide
theorem fsF3_end : blockEnd p384FromSec1Code 0x35A fsF3 = some 0x360 := by decide
theorem fsF4_end : blockEnd p384FromSec1Code 0x368 fsF4 = some 0x374 := by decide
theorem fsF5_end : blockEnd p384FromSec1Code 0x37C fsF5 = some 0x382 := by decide
theorem fsF6_end : blockEnd p384FromSec1Code 0x38A fsF6 = some 0x396 := by decide
theorem fsF7_end : blockEnd p384FromSec1Code 0x39E fsF7 = some 0x3A6 := by decide
theorem fsF8_end : blockEnd p384FromSec1Code 0x3AE fsF8 = some 0x3B6 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **The curve equation**, from 0x33E to 0x3BE: `y²` into `S + 0x334` and
`x³ + ax + b` into `S + 0x1AC`, in Montgomery form, then `x` and `y` copied
to `S + 0xDC` and `S + 0x10C`. -/
theorem fs_stF {M : Word → BitVec 8} {n : Machine} {S : Word} {X Y : Nat} (C : FsCode M) (D : P3Data M) (F : Fr S 0x420)
    (s : St M FP n 0x33E (reg n)) (rsp : reg n sp = S) (hX : accV M (S + BitVec.ofNat 32 0x3C4) 12 = X) (hXp : X < p384)
    (hY : accV M (S + BitVec.ofNat 32 0x364) 12 = Y) (hYp : Y < p384) :
    ∃ n', Steps n n' ∧ St n'.mem FP n' 0x3BE (reg n') ∧ FsCode n'.mem ∧ P3Data n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x334) 12 = p3fm Y Y ∧ accV n'.mem (S + BitVec.ofNat 32 0x1AC) 12 = dqAlpha X ∧
      accV n'.mem (S + BitVec.ofNat 32 0xDC) 12 = X ∧ accV n'.mem (S + BitVec.ofNat 32 0x10C) 12 = Y ∧
      (∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 → Sep (S + BitVec.ofNat 32 0xDC) 0x60 x 1 →
        Sep (S + BitVec.ofNat 32 0x1AC) 0x30 x 1 → Sep (S + BitVec.ofNat 32 0x334) 0x30 x 1 →
        Sep (S + BitVec.ofNat 32 0x394) 0x30 x 1 → n'.mem x = M x) ∧
      reg n' sp = S ∧ ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 22, 24, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hbF : (S + 0xFFFFFF10).toNat = S.toNat - 0xF0 := F.below 0xF0 (by decide) (by decide)
  have hbA : (S + 0xFFFFFF4C).toNat = S.toNat - 0xB4 := F.below 0xB4 (by decide) (by decide)
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have sF : ∀ c, c + 48 ≤ 0x420 → Sep (S + BitVec.ofNat 32 c) 48 (S + 0xFFFFFF10) 0xF0 := fun c h =>
    (sep_of_le (by rw [hbF, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm
  have sA : ∀ c, c + 48 ≤ 0x420 → Sep (S + BitVec.ofNat 32 c) 48 (S + 0xFFFFFF4C) 0xB4 := fun c h =>
    (sep_of_le (by rw [hbA, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm
  have al : ∀ c, c + 4 ≤ 0x420 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  have hiF : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFF10) 0xF0 x 1 := fun x hx =>
    sep_of_le (by rw [hbF]; omega) (by have := x.isLt; omega)
  have hiA : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFF4C) 0xB4 x 1 := fun x hx =>
    sep_of_le (by rw [hbA]; omega) (by have := x.isLt; omega)
  have keepF : ∀ {Mx My : Word → BitVec 8} {c : Nat}, (∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 →
      Sep (S + BitVec.ofNat 32 c) 48 x 1 → My x = Mx x) → ∀ d, d + 48 ≤ 0x420 → c + 48 ≤ 0x420 →
      (c + 48 ≤ d ∨ d + 48 ≤ c) → accV My (S + BitVec.ofNat 32 d) 12 = accV Mx (S + BitVec.ofNat 32 d) 12 :=
    fun {Mx My c} h d hd hc hcd => accV_congr2 12 fun i hi => memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc, add_ofNat_assoc]
      exact h _ (sep_of_le (by rw [hbF, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega))
        (sepS S (by rcases hcd with h | h; exact .inl (by omega); exact .inr (by omega)) (by omega) (by omega))
  have keepA : ∀ {Mx My : Word → BitVec 8} {c : Nat}, (∀ x, Sep (S + 0xFFFFFF4C) 0xB4 x 1 →
      Sep (S + BitVec.ofNat 32 c) 48 x 1 → My x = Mx x) → (∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 →
      Sep (S + BitVec.ofNat 32 c) 48 x 1 → My x = Mx x) := fun h x hF hc => h x (by
        have := hF.sub (c := 0x3C) (l := 0xB4) (by decide)
        rwa [show S + 0xFFFFFF10 + BitVec.ofNat 32 0x3C = S + 0xFFFFFF4C by rw [BitVec.add_assoc]; rfl] at this) hc
  have keep16 : ∀ {Mx My : Word → BitVec 8} {c : Nat}, (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 →
      Sep (S + BitVec.ofNat 32 c) 48 x 1 → My x = Mx x) → (∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 →
      Sep (S + BitVec.ofNat 32 c) 48 x 1 → My x = Mx x) := fun h x hF hc => h x (by
        have := hF.sub (c := 0xE0) (l := 16) (by decide)
        rwa [show S + 0xFFFFFF10 + BitVec.ofNat 32 0xE0 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this) hc
  have dOf : ∀ {Mx My : Word → BitVec 8} {c : Nat}, c + 48 ≤ 0x420 → P3Data Mx → (∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 →
      Sep (S + BitVec.ofNat 32 c) 48 x 1 → My x = Mx x) → P3Data My := fun {Mx My c} hc Dx h => Dx.of F fun x hx => h x (by
        have := hx.sub (c := 0x1A0 - 0xF0) (l := 0xF0) (by decide)
        rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 - 0xF0) = 0xFFFFFF10 from rfl] at this)
      (fr_inFrame (by omega) hx)
  -- y²
  obtain ⟨n1, c1, u1⟩ := s.block fsF1 C.self fsF1_end ⟨trivial, trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock fsF1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, v2, fr2, sp2, k2⟩ := c_p3mul (out := S + BitVec.ofNat 32 0x334) (xp := S + BitVec.ofNat 32 0x364)
    (yp := S + BitVec.ofNat 32 0x364) (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M FP n1 0x344 (reg n1)) C.self C.K D F fs_at_344
    fs_at_348 (by decide) (by decide) (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, fsF1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, fsF1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, fsF1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (co := 0x334) (by decide) rfl (by decide) (sF _ (by decide)) (al _ (by decide) (by decide)) (sF _ (by decide))
    (al _ (by decide) (by decide)) (by rw [limbVal_wordsAt, hY]; exact hYp)
  simp only [limbVal_wordsAt] at v2
  rw [hY] at v2
  have C2 := C.hi fun x hx => fr2 x (hiF x hx) (F.hiOut (by decide) hx)
  have D2 : P3Data n2.mem := dOf (by decide) D fr2
  have kk2 : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 22, 24, 26, 27] → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1, runBlock_reg _ _ _ q hz (by simp only [fsF1]; revert hq; revert q; decide)]
  have eX2 : accV n2.mem (S + BitVec.ofNat 32 0x3C4) 12 = X := by
    rw [keepF fr2 0x3C4 (by decide) (by decide) (.inl (by decide)), hX]
  have eY2 : accV n2.mem (S + BitVec.ofNat 32 0x364) 12 = Y := by
    rw [keepF fr2 0x364 (by decide) (by decide) (.inl (by decide)), hY]
  -- x²
  obtain ⟨n3, c3, u3⟩ := u2.block fsF2 C2.self fsF2_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock fsF2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, v4, fr4, sp4, k4⟩ := c_p3mul (out := S + BitVec.ofNat 32 0xDC) (xp := S + BitVec.ofNat 32 0x3C4)
    (yp := S + BitVec.ofNat 32 0x3C4) (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem FP n3 0x352 (reg n3)) C2.self C2.K D2 F
    fs_at_352 fs_at_356 (by decide) (by decide) (by rw [r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsF2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsF2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsF2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (co := 0xDC) (by decide) rfl (by decide) (sF _ (by decide)) (al _ (by decide) (by decide)) (sF _ (by decide))
    (al _ (by decide) (by decide)) (by rw [limbVal_wordsAt, eX2]; exact hXp)
  simp only [limbVal_wordsAt] at v4
  rw [eX2] at v4
  have C4 := C2.hi fun x hx => fr4 x (hiF x hx) (F.hiOut (by decide) hx)
  have D4 : P3Data n4.mem := dOf (by decide) D2 fr4
  have kk4 : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 22, 24, 26, 27] → reg n4 q = reg n q := fun q hq => by
    rw [k4 q (by revert hq; revert q; decide), r3, runBlock_reg _ _ _ q u2.zero (by simp only [fsF2]; revert hq; revert q; decide),
      kk2 q hq]
  have eX4 : accV n4.mem (S + BitVec.ofNat 32 0x3C4) 12 = X := by
    rw [keepF fr4 0x3C4 (by decide) (by decide) (.inl (by decide)), eX2]
  -- x³
  obtain ⟨n5, c5, u5⟩ := u4.block fsF3 C4.self fsF3_end ⟨trivial, trivial, trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock fsF3 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  obtain ⟨n6, c6, u6, v6, fr6, sp6, k6⟩ := c_p3mul (out := S + BitVec.ofNat 32 0x1AC) (xp := S + BitVec.ofNat 32 0xDC)
    (yp := S + BitVec.ofNat 32 0x3C4) (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem FP n5 0x360 (reg n5)) C4.self C4.K D4 F
    fs_at_360 fs_at_364 (by decide) (by decide) (by rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, fsF3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, fsF3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, fsF3, upd, ↓reduceIte]; rw [sp4]; rfl)
    (co := 0x1AC) (by decide) rfl (by decide) (sF _ (by decide)) (al _ (by decide) (by decide)) (sF _ (by decide))
    (al _ (by decide) (by decide)) (by rw [limbVal_wordsAt, eX4]; exact hXp)
  simp only [limbVal_wordsAt] at v6
  rw [v4, eX4] at v6
  have C6 := C4.hi fun x hx => fr6 x (hiF x hx) (F.hiOut (by decide) hx)
  have D6 : P3Data n6.mem := dOf (by decide) D4 fr6
  have kk6 : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 22, 24, 26, 27] → reg n6 q = reg n q := fun q hq => by
    rw [k6 q (by revert hq; revert q; decide), r5, runBlock_reg _ _ _ q u4.zero (by simp only [fsF3]; revert hq; revert q; decide),
      kk4 q hq]
  have eX6 : accV n6.mem (S + BitVec.ofNat 32 0x3C4) 12 = X := by
    rw [keepF fr6 0x3C4 (by decide) (by decide) (.inl (by decide)), eX4]
  -- ax
  obtain ⟨n7, c7, u7⟩ := u6.block fsF4 C6.self fsF4_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r7 : ∀ q, reg n7 q = (runBlock fsF4 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  have hAv : accV n6.mem CURVEA 12 = p3A := by
    rw [show CURVEA = CURVEA + BitVec.ofNat 32 0 from (add_ofNat_zero _).symm, code_accV D6.ca 0 12 (by decide),
      curveA_val]
  obtain ⟨n8, c8, u8, v8, fr8, sp8, k8⟩ := c_p3mul (out := S + BitVec.ofNat 32 0xDC) (xp := CURVEA)
    (yp := S + BitVec.ofNat 32 0x3C4) (⟨u7.pc, u7.mem, fun _ => rfl⟩ : St n6.mem FP n7 0x374 (reg n7)) C6.self C6.K D6 F
    fs_at_374 fs_at_378 (by decide) (by decide) (by rw [r7, runBlock_reg _ _ _ sp u6.zero (by decide)]; exact sp6)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, fsF4, upd, ↓reduceIte]; rw [sp6]; rfl)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, fsF4, upd, ↓reduceIte]; try rfl)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, fsF4, upd, ↓reduceIte]; rw [sp6]; rfl)
    (co := 0xDC) (by decide) rfl (by decide) (F.lowData (c := 0xF0) (by decide) rfl (by decide) (by decide)).symm
    (by decide) (sF _ (by decide)) (al _ (by decide) (by decide)) (by rw [limbVal_wordsAt, eX6]; exact hXp)
  simp only [limbVal_wordsAt] at v8
  rw [hAv, eX6] at v8
  have C8 := C6.hi fun x hx => fr8 x (hiF x hx) (F.hiOut (by decide) hx)
  have D8 : P3Data n8.mem := dOf (by decide) D6 fr8
  have kk8 : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 22, 24, 26, 27] → reg n8 q = reg n q := fun q hq => by
    rw [k8 q (by revert hq; revert q; decide), r7, runBlock_reg _ _ _ q u6.zero (by simp only [fsF4]; revert hq; revert q; decide),
      kk6 q hq]
  have e8x3 : accV n8.mem (S + BitVec.ofNat 32 0x1AC) 12 = p3fm (p3fm X X) X := by
    rw [keepF fr8 0x1AC (by decide) (by decide) (.inl (by decide)), v6]
  have eX8 : accV n8.mem (S + BitVec.ofNat 32 0x3C4) 12 = X := by
    rw [keepF fr8 0x3C4 (by decide) (by decide) (.inl (by decide)), eX6]
  -- x³ + ax
  obtain ⟨n9, c9, u9⟩ := u8.block fsF5 C8.self fsF5_end ⟨trivial, trivial, trivial, trivial⟩
  have r9 : ∀ q, reg n9 q = (runBlock fsF5 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
  obtain ⟨n10, c10, u10, v10, fr10, sp10, k10⟩ := c_p3add (out := S + BitVec.ofNat 32 0x394) (lp := S + BitVec.ofNat 32 0x1AC)
    (rp := S + BitVec.ofNat 32 0xDC) (⟨u9.pc, u9.mem, fun _ => rfl⟩ : St n8.mem FP n9 0x382 (reg n9)) C8.self C8.K D8 F
    fs_at_382 fs_at_386 (by decide) (by decide) (by rw [r9, runBlock_reg _ _ _ sp u8.zero (by decide)]; exact sp8)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, fsF5, upd, ↓reduceIte]; rw [sp8]; rfl)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, fsF5, upd, ↓reduceIte]; rw [sp8]; rfl)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, fsF5, upd, ↓reduceIte]; rw [sp8]; rfl)
    (co := 0x394) (by decide) rfl (by decide) (sA _ (by decide)) (al _ (by decide) (by decide)) (sA _ (by decide))
    (al _ (by decide) (by decide))
  simp only [limbVal_wordsAt] at v10
  rw [e8x3, v8] at v10
  have fr10' := keepA fr10
  have C10 := C8.hi fun x hx => fr10 x (hiA x hx) (F.hiOut (by decide) hx)
  have D10 : P3Data n10.mem := dOf (by decide) D8 fr10'
  have kk10 : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 22, 24, 26, 27] → reg n10 q = reg n q := fun q hq => by
    rw [k10 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r9, runBlock_reg _ _ _ q u8.zero (by simp only [fsF5]; revert hq; revert q; decide), kk8 q hq]
  -- + b
  obtain ⟨n11, c11, u11⟩ := u10.block fsF6 C10.self fsF6_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r11 : ∀ q, reg n11 q = (runBlock fsF6 (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
  obtain ⟨n12, c12, u12, v12, fr12, sp12, k12⟩ := c_p3add (out := S + BitVec.ofNat 32 0x1AC)
    (lp := S + BitVec.ofNat 32 0x394) (rp := p3bA) (⟨u11.pc, u11.mem, fun _ => rfl⟩ : St n10.mem FP n11 0x396 (reg n11))
    C10.self C10.K D10 F fs_at_396 fs_at_39a (by decide) (by decide)
    (by rw [r11, runBlock_reg _ _ _ sp u10.zero (by decide)]; exact sp10)
    (by rw [r11]; simp +decide only [runBlock, BInstr.run, fsF6, upd, ↓reduceIte]; rw [sp10]; rfl)
    (by rw [r11]; simp +decide only [runBlock, BInstr.run, fsF6, upd, ↓reduceIte]; rw [sp10]; rfl)
    (by rw [r11]; simp +decide only [runBlock, BInstr.run, fsF6, upd, ↓reduceIte]; try rfl)
    (co := 0x1AC) (by decide) rfl (by decide) (sA _ (by decide)) (al _ (by decide) (by decide))
    (F.lowData (c := 0xB4) (by decide) rfl (by decide) (by decide)).symm (by decide)
  rw [p3B_val D10.cb, limbVal_wordsAt, limbVal_wordsAt, v10] at v12
  have fr12' := keepA fr12
  have C12 := C10.hi fun x hx => fr12 x (hiA x hx) (F.hiOut (by decide) hx)
  have D12 : P3Data n12.mem := dOf (by decide) D10 fr12'
  have kk12 : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 22, 24, 26, 27] → reg n12 q = reg n q := fun q hq => by
    rw [k12 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r11, runBlock_reg _ _ _ q u10.zero (by simp only [fsF6]; revert hq; revert q; decide), kk10 q hq]
  have sp12' : reg n12 sp = S := sp12
  have kc : ∀ {m m' : Machine}, (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg m' q = reg m q) →
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q :=
    fun h q hq => h q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  obtain ⟨fA, fW, hFC⟩ := F.mc
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have eX12 : accV n12.mem (S + BitVec.ofNat 32 0x3C4) 12 = X := by
    rw [keepF fr12' 0x3C4 (by decide) (by decide) (.inl (by decide)), keepF fr10' 0x3C4 (by decide) (by decide) (.inl (by decide)),
      eX8]
  have eY12 : accV n12.mem (S + BitVec.ofNat 32 0x364) 12 = Y := by
    rw [keepF fr12' 0x364 (by decide) (by decide) (.inl (by decide)), keepF fr10' 0x364 (by decide) (by decide) (.inr (by decide)),
      keepF fr8 0x364 (by decide) (by decide) (.inl (by decide)), keepF fr6 0x364 (by decide) (by decide) (.inl (by decide)),
      keepF fr4 0x364 (by decide) (by decide) (.inl (by decide)), eY2]
  have eS12 : accV n12.mem (S + BitVec.ofNat 32 0x334) 12 = p3fm Y Y := by
    rw [keepF fr12' 0x334 (by decide) (by decide) (.inl (by decide)), keepF fr10' 0x334 (by decide) (by decide) (.inr (by decide)),
      keepF fr8 0x334 (by decide) (by decide) (.inl (by decide)), keepF fr6 0x334 (by decide) (by decide) (.inl (by decide)),
      keepF fr4 0x334 (by decide) (by decide) (.inl (by decide)), v2]
  -- copy x and y
  obtain ⟨n13, c13, u13⟩ := u12.block fsF7 C12.self fsF7_end ⟨trivial, trivial, trivial, trivial⟩
  have r13 : ∀ q, reg n13 q = (runBlock fsF7 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
  obtain ⟨n14, c14, u14, fr14, k14⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0xDC) (src := S + BitVec.ofNat 32 0x3C4)
    (S := S) (N := 0x30) (⟨u13.pc, u13.mem, fun _ => rfl⟩ : St n12.mem FP n13 0x3A6 (reg n13)) C12.self C12.K fs_at_3a6 fs_at_3aa
    (by decide) (by decide) (by rw [r13, runBlock_reg _ _ _ sp u12.zero (by decide)]; exact sp12)
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, fsF7, upd, ↓reduceIte]; rw [sp12]; rfl)
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, fsF7, upd, ↓reduceIte]; rw [sp12]; rfl)
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, fsF7, upd, ↓reduceIte]; (try rw [u12.zero]); try rfl)
    ⟨C12.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inl (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr14' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0xDC) 48 x 1 → n14.mem x = n12.mem x :=
    fun x a b => by rw [fr14 x a, copyBytes_sep b (Nat.le_refl _)]
  have C14 := C12.hi fun x hx => fr14' x (lo16 x hx) (F.hiOut (by decide) hx)
  have k14' := kc k14
  have sp14 : reg n14 sp = S := by rw [k14' sp (by decide), r13, runBlock_reg _ _ _ sp u12.zero (by decide)]; exact sp12
  obtain ⟨n15, c15, u15⟩ := u14.block fsF8 C14.self fsF8_end ⟨trivial, trivial, trivial, trivial⟩
  have r15 : ∀ q, reg n15 q = (runBlock fsF8 (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
  obtain ⟨n16, c16, u16, fr16, k16⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x10C) (src := S + BitVec.ofNat 32 0x364)
    (S := S) (N := 0x30) (⟨u15.pc, u15.mem, fun _ => rfl⟩ : St n14.mem FP n15 0x3B6 (reg n15)) C14.self C14.K fs_at_3b6 fs_at_3ba
    (by decide) (by decide) (by rw [r15, runBlock_reg _ _ _ sp u14.zero (by decide)]; exact sp14)
    (by rw [r15]; simp +decide only [runBlock, BInstr.run, fsF8, upd, ↓reduceIte]; rw [sp14]; rfl)
    (by rw [r15]; simp +decide only [runBlock, BInstr.run, fsF8, upd, ↓reduceIte]; rw [sp14]; rfl)
    (by rw [r15]; simp +decide only [runBlock, BInstr.run, fsF8, upd, ↓reduceIte]; (try rw [u14.zero]); try rfl)
    ⟨C14.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inl (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr16' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x10C) 48 x 1 → n16.mem x = n14.mem x :=
    fun x a b => by rw [fr16 x a, copyBytes_sep b (Nat.le_refl _)]
  have C16 := C14.hi fun x hx => fr16' x (lo16 x hx) (F.hiOut (by decide) hx)
  have k16' := kc k16
  have D16 : P3Data n16.mem := dOf (by decide) (dOf (by decide) D12 (keep16 fr14')) (keep16 fr16')
  have l16 : ∀ d, d + 4 ≤ 0x420 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  refine ⟨n16, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans
    (c11.trans (c12.trans (c13.trans (c14.trans (c15.trans c16)))))))))))))), u16, C16, D16, ?_, ?_, ?_, ?_,
    fun x hF hDC h1AC h334 h394 => ?_, ?_, fun q hq => ?_⟩
  · rw [keepF (keep16 fr16') 0x334 (by decide) (by decide) (.inl (by decide)),
      keepF (keep16 fr14') 0x334 (by decide) (by decide) (.inl (by decide)), eS12]
  · rw [keepF (keep16 fr16') 0x1AC (by decide) (by decide) (.inl (by decide)),
      keepF (keep16 fr14') 0x1AC (by decide) (by decide) (.inl (by decide)), v12]; rfl
  · rw [keepF (keep16 fr16') 0xDC (by decide) (by decide) (.inr (by decide)), ← eX12]
    exact accV_congr2 12 fun i hi => by
      rw [load_frame fr14 (by rw [add_ofNat_assoc]; exact l16 _ (by omega)), cp_word (by omega) (by decide)]
  · rw [← eY12]
    exact accV_congr2 12 fun i hi => by
      rw [load_frame fr16 (by rw [add_ofNat_assoc]; exact l16 _ (by omega)), cp_word (by omega) (by decide)]
      exact memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc, add_ofNat_assoc]
        exact fr14' _ (F.lowB hb16 (by decide) (by omega)) (sepS S (.inl (by omega)) (by decide) (by omega))
  · have sub : ∀ {c l : Nat} (b : Word) (L : Nat), Sep b L x 1 → c + l ≤ L → Sep (b + BitVec.ofNat 32 c) l x 1 :=
      fun {c l} b L h hl => h.sub (c := c) (l := l) hl
    have hDC0 : Sep (S + BitVec.ofNat 32 0xDC) 48 x 1 := by
      have := sub (c := 0) (l := 48) _ _ hDC (by decide); rwa [add_ofNat_zero] at this
    have hDC1 : Sep (S + BitVec.ofNat 32 0x10C) 48 x 1 := by
      have := sub (c := 0x30) (l := 48) _ _ hDC (by decide); rwa [add_ofNat_assoc] at this
    rw [keep16 fr16' x hF hDC1, keep16 fr14' x hF hDC0, fr12' x hF h1AC, fr10' x hF h394, fr8 x hF hDC0, fr6 x hF h1AC,
      fr4 x hF hDC0, fr2 x hF h334]
  · rw [k16' sp (by decide), r15, runBlock_reg _ _ _ sp u14.zero (by decide)]; exact sp14
  · rw [k16' q (by revert hq; revert q; decide), r15, runBlock_reg _ _ _ q u14.zero (by simp only [fsF8]; revert hq; revert q; decide),
      k14' q (by revert hq; revert q; decide), r13, runBlock_reg _ _ _ q u12.zero (by simp only [fsF7]; revert hq; revert q; decide),
      kk12 q hq]

def fsG1 : List BInstr := [.aluImm .add a0 sp 0x334, .aluImm .add a1 sp 0x1AC]
def fsG2 : List BInstr := [.aluImm .and a0 a0 0xFF]
def fsG3 : List BInstr := [.alu .and a0 (19 : Fin 32) a0]
def fsG4 : List BInstr := [.alu .and a0 (18 : Fin 32) a0]
def fsG5 : List BInstr := [.alu .add (9 : Fin 32) x0 a0, .aluImm .add a0 sp 0x144, .aluImm .add a1 sp 0xDC, .aluImm .add a2 x0 0x60]
def fsG6 : List BInstr := [.sb sp x0 0x1A4, .sb sp (9 : Fin 32) 0x1A8]
theorem fsG1_end : blockEnd p384FromSec1Code 0x3BE fsG1 = some 0x3C2 := by decide
theorem fsG2_end : blockEnd p384FromSec1Code 0x3CA fsG2 = some 0x3CE := by decide
theorem fsG3_end : blockEnd p384FromSec1Code 0x3D6 fsG3 = some 0x3DA := by decide
theorem fsG4_end : blockEnd p384FromSec1Code 0x3E2 fsG4 = some 0x3E6 := by decide
theorem fsG5_end : blockEnd p384FromSec1Code 0x3EE fsG5 = some 0x3F8 := by decide
theorem fsG6_end : blockEnd p384FromSec1Code 0x400 fsG6 = some 0x408 := by decide

theorem and01 (a b : Word) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    ((aluEval .and a b).extractLsb' 0 8).zeroExtend 32 = if a = 1 ∧ b = 1 then 1 else 0 := by
  rcases ha with h | h <;> rcases hb with h' | h' <;> (rw [h, h']; decide)

theorem ite_and3 (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] :
    (if R ∧ (if Q ∧ (if P then (1 : Word) else 0) = 1 then (1 : Word) else 0) = 1 then (1 : Word) else 0) =
      if P ∧ Q ∧ R then 1 else 0 := by
  have z1 : ¬ ((0 : Word) = 1) := by decide
  by_cases hp : P
  · rw [ite_eq_left hp]
    by_cases hq : Q
    · rw [ite_eq_left (show Q ∧ (1 : Word) = 1 from ⟨hq, rfl⟩)]
      by_cases hr : R
      · rw [ite_eq_left (show R ∧ (1 : Word) = 1 from ⟨hr, rfl⟩), ite_eq_left (show P ∧ Q ∧ R from ⟨hp, hq, hr⟩)]
      · rw [ite_eq_right (show ¬ (R ∧ (1 : Word) = 1) from fun h => hr h.1),
          ite_eq_right (show ¬ (P ∧ Q ∧ R) from fun h => hr h.2.2)]
    · rw [ite_eq_right (show ¬ (Q ∧ (1 : Word) = 1) from fun h => hq h.1),
        ite_eq_right (show ¬ (R ∧ (0 : Word) = 1) from fun h => z1 h.2),
        ite_eq_right (show ¬ (P ∧ Q ∧ R) from fun h => hq h.2.1)]
  · rw [ite_eq_right hp, ite_eq_right (show ¬ (Q ∧ (0 : Word) = 1) from fun h => z1 h.2),
      ite_eq_right (show ¬ (R ∧ (0 : Word) = 1) from fun h => z1 h.2),
      ite_eq_right (show ¬ (P ∧ Q ∧ R) from fun h => hp h.1)]

theorem ite01w (P : Prop) [Decidable P] : (if P then (1 : Word) else 0) = 0 ∨ (if P then (1 : Word) else 0) = 1 := by
  by_cases h : P
  · exact .inr (ite_eq_left h)
  · exact .inl (ite_eq_right h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **The choice**, from 0x3BE to 0x408: `y² = x³ + ax + b`, `x < p`, and
`y < p` combine into the choice byte of the `CtOption<AffinePoint>` that
`S + 0x144` now holds, after `x`, `y`, and the identity flag 0. -/
theorem fs_stG {M : Word → BitVec 8} {n : Machine} {S : Word} {A1 A2 X Y : Nat} {xo yo : Word} (C : FsCode M)
    (D : P3Data M) (F : Fr S 0x420) (s : St M FP n 0x3BE (reg n)) (rsp : reg n sp = S)
    (h1 : accV M (S + BitVec.ofNat 32 0x334) 12 = A1) (h2 : accV M (S + BitVec.ofNat 32 0x1AC) 12 = A2)
    (hX : accV M (S + BitVec.ofNat 32 0xDC) 12 = X) (hY : accV M (S + BitVec.ofNat 32 0x10C) 12 = Y)
    (r19 : reg n (19 : Fin 32) = xo) (r18 : reg n (18 : Fin 32) = yo) (hxo : xo = 0 ∨ xo = 1) (hyo : yo = 0 ∨ yo = 1) :
    ∃ n', Steps n n' ∧ St n'.mem FP n' 0x408 (reg n') ∧ FsCode n'.mem ∧ P3Data n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x144) 12 = X ∧ accV n'.mem (S + BitVec.ofNat 32 0x174) 12 = Y ∧
      n'.mem (S + BitVec.ofNat 32 0x1A4) = 0 ∧
      n'.mem (S + BitVec.ofNat 32 0x1A8) = (if A1 = A2 ∧ xo = 1 ∧ yo = 1 then 1 else 0) ∧
      (∀ x, Sep (S + 0xFFFFFFBC) 0x44 x 1 → Sep (S + BitVec.ofNat 32 0x144) 0x65 x 1 → n'.mem x = M x) ∧
      reg n' sp = S ∧ ∀ q : Fin 32, q.val ∈ [3, 4, 22, 24, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hbE : (S + 0xFFFFFFBC).toNat = S.toNat - 0x44 := F.below 0x44 (by decide) (by decide)
  have hb1 : (S + 0xFFFFFFFF).toNat = S.toNat - 1 := F.below 1 (by decide) (by decide)
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have loE : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFBC) 0x44 x 1 := fun x hx =>
    sep_of_le (by rw [hbE]; omega) (by have := x.isLt; omega)
  have sub1 : ∀ {x : Word}, Sep (S + 0xFFFFFFBC) 0x44 x 1 → Sep (S + 0xFFFFFFFF) 1 x 1 := fun {x} hx => by
    have := hx.sub (c := 0x43) (l := 1) (by decide)
    rwa [show S + 0xFFFFFFBC + BitVec.ofNat 32 0x43 = S + 0xFFFFFFFF by rw [BitVec.add_assoc]; rfl] at this
  have sub16 : ∀ {x : Word}, Sep (S + 0xFFFFFFBC) 0x44 x 1 → Sep (S + 0xFFFFFFF0) 16 x 1 := fun {x} hx => by
    have := hx.sub (c := 0x34) (l := 16) (by decide)
    rwa [show S + 0xFFFFFFBC + BitVec.ofNat 32 0x34 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
  have sE : ∀ c, c + 48 ≤ 0x420 → Sep (S + BitVec.ofNat 32 c) 48 (S + 0xFFFFFFBC) 0x44 := fun c h =>
    (sep_of_le (by rw [hbE, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm
  have al : ∀ c, c + 4 ≤ 0x420 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  -- Uint::ct_eq
  obtain ⟨n1, c1, u1⟩ := s.block fsG1 C.self fsG1_end ⟨trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock fsG1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, ea2, fr2, sp2, k2⟩ := c_uce (pa := S + BitVec.ofNat 32 0x334) (pb := S + BitVec.ofNat 32 0x1AC)
    (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M FP n1 0x3C2 (reg n1)) C.self C.K F fs_at_3c2 fs_at_3c6 (by decide) (by decide)
    (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, fsG1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, fsG1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (al _ (by decide) (by decide)) (al _ (by decide) (by decide)) (sE _ (by decide)) (sE _ (by decide))
  have heq : (if ∀ i : Nat, i < 12 → memLoad32 M (S + BitVec.ofNat 32 0x334 + BitVec.ofNat 32 (4 * i)) =
      memLoad32 M (S + BitVec.ofNat 32 0x1AC + BitVec.ofNat 32 (4 * i)) then (1 : Word) else 0) =
      (if A1 = A2 then 1 else 0) := by
    by_cases h : A1 = A2
    · rw [ite_eq_left ((eq12_iff).2 (by rw [h1, h2, h])), ite_eq_left h]
    · rw [ite_eq_right (fun e => h (by rw [← h1, ← h2]; exact (eq12_iff).1 e)), ite_eq_right h]
  rw [heq] at ea2
  have C2 := C.hi fun x hx => fr2 x (loE x hx)
  have D2 : P3Data n2.mem := D.of F fun x hx => fr2 x (by
    have := hx.sub (c := 0x15C) (l := 0x44) (by decide)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x15C = S + 0xFFFFFFBC by rw [BitVec.add_assoc]; rfl] at this)
  obtain ⟨n3, c3, u3⟩ := u2.block fsG2 C2.self fsG2_end ⟨trivial, trivial⟩
  have r3 : ∀ q, q ≠ a0 → reg n3 q = reg n2 q := fun q hq => by
    rw [u3.regs]; simp only [runBlock, BInstr.run, fsG2]; exact updz u2.zero hq
  obtain ⟨n4, c4, u4, ea4, fr4, k4⟩ := c_bb (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem FP n3 0x3CE (reg n3)) C2.self C2.K F
    fs_at_3ce fs_at_3d2 (by decide) (by decide) (by rw [r3 sp (by decide)]; exact sp2)
  have e4 : reg n4 a0 = if A1 = A2 then 1 else 0 := by
    rw [ea4, u3.regs]; simp +decide only [runBlock, BInstr.run, fsG2, upd, ↓reduceIte]; rw [ea2]
    by_cases h : A1 = A2
    · rw [ite_eq_left h]; decide
    · rw [ite_eq_right h]; decide
  have C4 := C2.hi fun x hx => fr4 x (sub1 (loE x hx))
  have KA : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 22, 24, 26, 27] → reg n4 q = reg n q := fun q hq => by
    rw [k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), r3 q (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), r1, runBlock_reg _ _ _ q hz (by simp only [fsG1]; revert hq; revert q; decide)]
  obtain ⟨n5, c5, u5⟩ := u4.block fsG3 C4.self fsG3_end ⟨trivial, trivial⟩
  have r5 : ∀ q, q ≠ a0 → reg n5 q = reg n4 q := fun q hq => by
    rw [u5.regs]; simp only [runBlock, BInstr.run, fsG3]; exact updz u4.zero hq
  obtain ⟨n6, c6, u6, ea6, fr6, k6⟩ := c_bb (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem FP n5 0x3DA (reg n5)) C4.self C4.K F
    fs_at_3da fs_at_3de (by decide) (by decide) (by rw [r5 sp (by decide), KA sp (by decide)]; exact rsp)
  have e6 : reg n6 a0 = if xo = 1 ∧ (if A1 = A2 then (1 : Word) else 0) = 1 then 1 else 0 := by
    rw [ea6, u5.regs]; simp +decide only [runBlock, BInstr.run, fsG3, upd, ↓reduceIte]
    rw [KA 19 (by decide), r19, e4]; exact and01 _ _ hxo (ite01w _)
  have C6 := C4.hi fun x hx => fr6 x (sub1 (loE x hx))
  obtain ⟨n7, c7, u7⟩ := u6.block fsG4 C6.self fsG4_end ⟨trivial, trivial⟩
  have r7 : ∀ q, q ≠ a0 → reg n7 q = reg n6 q := fun q hq => by
    rw [u7.regs]; simp only [runBlock, BInstr.run, fsG4]; exact updz u6.zero hq
  have KB : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 22, 24, 26, 27] → reg n7 q = reg n q := fun q hq => by
    rw [r7 q (by revert hq; revert q; decide), k6 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), r5 q (by revert hq; revert q; decide), KA q hq]
  obtain ⟨n8, c8, u8, ea8, fr8, k8⟩ := c_bb (⟨u7.pc, u7.mem, fun _ => rfl⟩ : St n6.mem FP n7 0x3E6 (reg n7)) C6.self C6.K F
    fs_at_3e6 fs_at_3ea (by decide) (by decide) (by rw [KB sp (by decide)]; exact rsp)
  have e8 : reg n8 a0 = if A1 = A2 ∧ xo = 1 ∧ yo = 1 then 1 else 0 := by
    rw [ea8, u7.regs]; simp +decide only [runBlock, BInstr.run, fsG4, upd, ↓reduceIte]
    rw [show reg n6 (18 : Fin 32) = yo by rw [← r7 18 (by decide), KB 18 (by decide), r18], e6, and01 _ _ hyo (ite01w _)]
    exact ite_and3 _ _ _
  have C8 := C6.hi fun x hx => fr8 x (sub1 (loE x hx))
  have KC : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 22, 24, 26, 27] → reg n8 q = reg n q := fun q hq => by
    rw [k8 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), KB q (by revert hq; revert q; decide)]
  have kc : ∀ {m m' : Machine}, (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg m' q = reg m q) →
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q :=
    fun h q hq => h q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  obtain ⟨fA, fW, hFC⟩ := F.mc
  have sp8 : reg n8 sp = S := by rw [KC sp (by decide)]; exact rsp
  obtain ⟨n9, c9, u9⟩ := u8.block fsG5 C8.self fsG5_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r9 : ∀ q, reg n9 q = (runBlock fsG5 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
  obtain ⟨n10, c10, u10, fr10, k10⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x144) (src := S + BitVec.ofNat 32 0xDC)
    (S := S) (N := 0x60) (⟨u9.pc, u9.mem, fun _ => rfl⟩ : St n8.mem FP n9 0x3F8 (reg n9)) C8.self C8.K fs_at_3f8 fs_at_3fc
    (by decide) (by decide) (by rw [r9, runBlock_reg _ _ _ sp u8.zero (by decide)]; exact sp8)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, fsG5, upd, ↓reduceIte]; rw [sp8]; rfl)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, fsG5, upd, ↓reduceIte]; rw [sp8]; rfl)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, fsG5, upd, ↓reduceIte]; (try rw [u8.zero]); try rfl)
    ⟨C8.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr10' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x144) 0x60 x 1 → n10.mem x = n8.mem x :=
    fun x a b => by rw [fr10 x a, copyBytes_sep b (Nat.le_refl _)]
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have C10 := C8.hi fun x hx => fr10' x (lo16 x hx) (F.hiOut (by decide) hx)
  have k10' := kc k10
  have sp10 : reg n10 sp = S := by rw [k10' sp (by decide), r9, runBlock_reg _ _ _ sp u8.zero (by decide)]; exact sp8
  have e109 : reg n10 (9 : Fin 32) = if A1 = A2 ∧ xo = 1 ∧ yo = 1 then 1 else 0 := by
    rw [k10' 9 (by decide), r9]; simp +decide only [runBlock, BInstr.run, fsG5, upd, ↓reduceIte]; rw [e8]
    exact BitVec.zero_add _
  obtain ⟨n11, c11, u11⟩ := u10.block fsG6 C10.self fsG6_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, fsG6]; simp +decide only [and_true]
    rw [sp10]; exact ⟨F.sepHi (by decide) (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩)
  obtain ⟨M11, hM11⟩ : ∃ M11, memStore8 (memStore8 n10.mem (S + BitVec.ofNat 32 0x1A4) 0) (S + BitVec.ofNat 32 0x1A8)
      (if A1 = A2 ∧ xo = 1 ∧ yo = 1 then 1 else 0) = M11 := ⟨_, rfl⟩
  have hv : (reg n10 (9 : Fin 32)).extractLsb' 0 8 = if A1 = A2 ∧ xo = 1 ∧ yo = 1 then 1 else 0 := by
    rw [e109]
    by_cases h : A1 = A2 ∧ xo = 1 ∧ yo = 1
    · rw [ite_eq_left h, ite_eq_left h]; rfl
    · rw [ite_eq_right h, ite_eq_right h]; rfl
  have m11 : n11.mem = M11 := by
    rw [u11.mem, ← hM11]; simp only [runBlock, BInstr.run, fsG6]
    rw [sp10, hv, u10.zero]; rfl
  have h11 : ∀ x, Sep (S + BitVec.ofNat 32 0x1A4) 5 x 1 → M11 x = n10.mem x := fun x hx => by
    rw [← hM11, dq_st8 ((hx.sub (c := 4) (l := 1) (by decide)) |> fun h => by rwa [add_ofNat_assoc] at h),
      dq_st8 ((hx.sub (c := 0) (l := 1) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h)]
  have l16 : ∀ d, d + 4 ≤ 0x420 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have back8 : ∀ d, d + 1 ≤ 0x420 → n8.mem (S + BitVec.ofNat 32 d) = M (S + BitVec.ofNat 32 d) := fun d hd => by
    rw [fr8 _ (F.lowB hb1 (by decide) hd), fr6 _ (F.lowB hb1 (by decide) hd), fr4 _ (F.lowB hb1 (by decide) hd),
      fr2 _ (F.lowB hbE (by decide) hd)]
  have cpW : ∀ k, k + 4 ≤ 0x60 → memLoad32 M11 (S + BitVec.ofNat 32 (0x144 + k)) = memLoad32 M (S + BitVec.ofNat 32 (0xDC + k)) :=
    fun k hk => by
      rw [memLoad32_congr (M := n10.mem) fun j hj => by
        rw [add_ofNat_assoc]; exact h11 _ (sepS S (.inr (by omega)) (by decide) (by omega)),
        load_frame fr10 (l16 _ (by omega)), ← add_ofNat_assoc S 0x144, cp_word hk (by decide), add_ofNat_assoc]
      exact memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact back8 _ (by omega)
  have D11 : P3Data M11 := D2.of F fun x hx => by
    have hx16 : Sep (S + 0xFFFFFFF0) 16 x 1 := by
      have := hx.sub (c := 0x190) (l := 16) (by decide)
      rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x190 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
    have hx1 : Sep (S + 0xFFFFFFFF) 1 x 1 := by
      have := hx.sub (c := 0x19F) (l := 1) (by decide)
      rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x19F = S + 0xFFFFFFFF by rw [BitVec.add_assoc]; rfl] at this
    rw [h11 x (fr_inFrame (by decide) hx), fr10' x hx16 (fr_inFrame (by decide) hx), fr8 x hx1, fr6 x hx1, fr4 x hx1]
  refine ⟨n11, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans
    c11))))))))), ⟨u11.pc, rfl, fun _ => rfl⟩,
    by rw [m11]; exact C10.hi fun x hx => h11 x (F.hiOut (by decide) hx), by rw [m11]; exact D11, ?_, ?_, ?_, ?_,
    fun x hE h144 => ?_, ?_, fun q hq => ?_⟩
  · rw [m11, ← hX]
    exact accV_congr2 12 fun i hi => by rw [add_ofNat_assoc, add_ofNat_assoc]; exact cpW _ (by omega)
  · rw [m11, ← hY]
    exact accV_congr2 12 fun i hi => by
      rw [add_ofNat_assoc, add_ofNat_assoc, show 0x174 + 4 * i = 0x144 + (0x30 + 4 * i) by omega, cpW _ (by omega),
        show 0xDC + (0x30 + 4 * i) = 0x10C + 4 * i by omega]
  · rw [m11, ← hM11, dq_st8 (sepS S (.inr (by decide)) (by decide) (by decide)), memStore8_same]
  · rw [m11, ← hM11, memStore8_same]
  · have h1A4 : Sep (S + BitVec.ofNat 32 0x1A4) 5 x 1 := by
      have := h144.sub (c := 0x60) (l := 5) (by decide); rwa [add_ofNat_assoc] at this
    have h14460 : Sep (S + BitVec.ofNat 32 0x144) 0x60 x 1 := by
      have := h144.sub (c := 0) (l := 0x60) (by decide); rwa [add_ofNat_zero] at this
    rw [m11, h11 x h1A4, fr10' x (sub16 hE) h14460, fr8 x (sub1 hE), fr6 x (sub1 hE), fr4 x (sub1 hE), fr2 x hE]
  · rw [u11.regs]; simp only [runBlock, BInstr.run, fsG6]; exact sp10
  · rw [u11.regs]; simp only [runBlock, BInstr.run, fsG6]
    rw [k10' q (by revert hq; revert q; decide), r9, runBlock_reg _ _ _ q u8.zero (by simp only [fsG5]; revert hq; revert q; decide),
      KC q (by revert hq; revert q; decide)]

def fsH1 : List BInstr := [.aluImm .add a0 sp 0x74, .aluImm .add a1 sp 0x144]
def fsH2 : List BInstr := [.alu .add a0 x0 (22 : Fin 32)]
def fsH3 : List BInstr :=
  [.lbu a1 sp 0xD8, .aluImm .add a0 a0 0xFFFFFFFF, .alu .and a0 a0 a1, .aluImm .and a0 a0 0x1, .sb sp a0 0x144,
   .aluImm .add a0 sp 0x144, .lbu a0 sp 0x144]
def fsH4 : List BInstr := [.aluImm .add a0 (24 : Fin 32) 0x4, .aluImm .add a1 sp 0x74, .aluImm .add a2 x0 0x64]
def fsH5 : List BInstr := [.aluImm .add a0 x0 0x0]
theorem fsH1_end : blockEnd p384FromSec1Code 0x408 fsH1 = some 0x40C := by decide
theorem fsH2_end : blockEnd p384FromSec1Code 0x414 fsH2 = some 0x416 := by decide
theorem fsH3_end : blockEnd p384FromSec1Code 0x41E fsH3 = some 0x432 := by decide
theorem fsH4_end : blockEnd p384FromSec1Code 0x434 fsH4 = some 0x43E := by decide
theorem fsH5_end : blockEnd p384FromSec1Code 0x446 fsH5 = some 0x448 := by decide

theorem ch_and (c : BitVec 8) (hc : c = 0 ∨ c = 1) :
    aluEval .and (aluEval .and (aluEval .add (0 : Word) 0xFFFFFFFF) (c.zeroExtend 32)) 1 = c.zeroExtend 32 := by
  rcases hc with h | h <;> (rw [h]; decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **The result**, from 0x408 to the return: `CtOption::into` with the
identity as the default, then `Ok` and the point at `out + 4` when the choice
is 1, else `Err`. -/
theorem fs_stH {M M0 : Word → BitVec 8} {n n0 : Machine} {S out : Word} {X Y : Nat} {P : Prop} [Decidable P]
    (C : FsCode M) (F : Fr S 0x420) (s : St M FP n 0x408 (reg n)) (rsp : reg n sp = S)
    (r22 : reg n (22 : Fin 32) = (4 : BitVec 8).zeroExtend 32) (r24 : reg n (24 : Fin 32) = out)
    (hX : accV M (S + BitVec.ofNat 32 0x144) 12 = X) (hY : accV M (S + BitVec.ofNat 32 0x174) 12 = Y)
    (hz : M (S + BitVec.ofNat 32 0x1A4) = 0) (hc : M (S + BitVec.ofNat 32 0x1A8) = (if P then 1 else 0))
    (hoa : out.toNat % 4 = 0) (hO : out.toNat + 0x68 ≤ 0x40000000) (sO : Sep out 0x68 (S + 0xFFFFFE60) 0x5C0)
    (hS : ∀ k, k < 11 → memLoad32 M (S + BitVec.ofNat 32 (0x41C - 4 * k)) = reg n0 (savedReg k))
    (hret : reg n0 ra &&& ~~~1 = reg n0 ra) (k3 : ∀ q : Fin 32, q.val ∈ [3, 4, 26, 27] → reg n q = reg n0 q)
    (hM : ∀ x, Sep (S + 0xFFFFFE60) 0x5C0 x 1 → M x = M0 x) :
    ∃ n', Steps n n' ∧ FsRet M0 n0 S out n' ∧
      ((P → memLoad32 n'.mem out = 0 ∧ accV n'.mem (out + BitVec.ofNat 32 4) 12 = X ∧
        accV n'.mem (out + BitVec.ofNat 32 0x34) 12 = Y ∧ n'.mem (out + BitVec.ofNat 32 0x64) = 0) ∧
      (¬ P → memLoad32 n'.mem out = 1)) := by
  have hz0 := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hb90 : (S + 0xFFFFFF70).toNat = S.toNat - 0x90 := F.below 0x90 (by decide) (by decide)
  have hbA : (S + 0xFFFFFFB0).toNat = S.toNat - 0x50 := F.below 0x50 (by decide) (by decide)
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have hch : M (S + BitVec.ofNat 32 0x144 + 0x64) = 0 ∨ M (S + BitVec.ofNat 32 0x144 + 0x64) = 1 := by
    rw [show S + BitVec.ofNat 32 0x144 + 0x64 = S + BitVec.ofNat 32 0x1A8 by rw [BitVec.add_assoc]; rfl, hc]
    by_cases h : P
    · rw [ite_eq_left h]; exact .inr rfl
    · rw [ite_eq_right h]; exact .inl rfl
  -- CtOption::into
  obtain ⟨n1, c1, u1⟩ := s.block fsH1 C.self fsH1_end ⟨trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock fsH1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, w2, v2, z2, ch2, sp2, k2, fr2⟩ := c_into (out := S + BitVec.ofNat 32 0x74)
    (sv := S + BitVec.ofNat 32 0x144) (co := 0x74) (cs := 0x144)
    (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M FP n1 0x40C (reg n1)) C.self C.K F fs_at_40c fs_at_410 (by decide) (by decide)
    (by rw [r1, runBlock_reg _ _ _ sp hz0 (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, fsH1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, fsH1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by decide) (by decide) rfl rfl (by decide) (.inl (by decide)) hch
  have loN : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFF70) 0x90 x 1 := fun x hx =>
    sep_of_le (by rw [hb90]; omega) (by have := x.isLt; omega)
  have C2 := C.hi fun x hx => fr2 x (loN x hx) (F.hiOut (by decide) hx)
  have K2 : ∀ q : Fin 32, q.val ∈ [3, 4, 22, 24, 26, 27] → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1, runBlock_reg _ _ _ q hz0 (by simp only [fsH1]; revert hq; revert q; decide)]
  -- is_identity on the tag 4
  obtain ⟨n3, c3, u3⟩ := u2.block fsH2 C2.self fsH2_end ⟨trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock fsH2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, a4, sp4, k4, fr4⟩ := c_isid (t := 4) (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem FP n3 0x416 (reg n3))
    C2.self C2.K F fs_at_416 fs_at_41a (by decide) (by decide) (by rw [r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, fsH2, upd, ↓reduceIte]; rw [K2 22 (by decide), r22]
        exact BitVec.zero_add _) (by decide)
  have loA : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFB0) 0x50 x 1 := fun x hx =>
    sep_of_le (by rw [hbA]; omega) (by have := x.isLt; omega)
  have C4 := C2.hi fun x hx => fr4 x (loA x hx)
  -- the choice from `S + 0xD8`
  obtain ⟨n5, c5, u5⟩ := u4.block fsH3 C4.self fsH3_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, fsH3]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp4]; exact F.sepHi (by decide) (by decide) (by decide))
  have chv : n4.mem (S + BitVec.ofNat 32 0xD8) = if P then 1 else 0 := by
    rw [fr4 _ (F.lowB hbA (by decide) (by decide)),
      show S + BitVec.ofNat 32 0xD8 = S + BitVec.ofNat 32 0x74 + 0x64 by rw [BitVec.add_assoc]; rfl, ch2,
      show S + BitVec.ofNat 32 0x144 + 0x64 = S + BitVec.ofNat 32 0x1A8 by rw [BitVec.add_assoc]; rfl, hc]
  have ch01 : (if P then (1 : BitVec 8) else 0) = 0 ∨ (if P then (1 : BitVec 8) else 0) = 1 := by
    by_cases h : P
    · rw [ite_eq_left h]; exact .inr rfl
    · rw [ite_eq_right h]; exact .inl rfl
  have a5 : reg n5 a0 = (if P then (1 : BitVec 8) else 0).zeroExtend 32 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, fsH3, upd, ↓reduceIte]; rw [sp4, a4]
    show (memStore8 n4.mem (S + 0x144) ((aluEval .and (aluEval .and (aluEval .add (0 : Word) 0xFFFFFFFF)
      ((n4.mem (S + 0xD8)).zeroExtend 32)) 1).extractLsb' 0 8) (S + 0x144)).zeroExtend 32 = _
    rw [memStore8_same, show (S + 0xD8 : Word) = S + BitVec.ofNat 32 0xD8 from rfl, chv, ch_and _ ch01, ze_ex]
  obtain ⟨M5, hM5⟩ : ∃ M5, memStore8 n4.mem (S + BitVec.ofNat 32 0x144) (if P then 1 else 0) = M5 := ⟨_, rfl⟩
  have m5 : n5.mem = M5 := by
    rw [u5.mem, ← hM5]; simp +decide only [runBlock, BInstr.run, fsH3, upd, ↓reduceIte]; rw [sp4, a4]
    show memStore8 n4.mem (S + BitVec.ofNat 32 0x144) ((aluEval .and (aluEval .and (aluEval .add (0 : Word) 0xFFFFFFFF)
      ((n4.mem (S + BitVec.ofNat 32 0xD8)).zeroExtend 32)) 1).extractLsb' 0 8) = _
    rw [chv, ch_and _ ch01, ze_ex]
  have h5 : ∀ x, Sep (S + BitVec.ofNat 32 0x144) 1 x 1 → M5 x = n4.mem x := fun x hx => by rw [← hM5]; exact dq_st8 hx
  have C5 : FsCode M5 := C4.hi fun x hx => h5 x (F.hiOut (by decide) hx)
  have v5 : St M5 FP n5 0x432 (reg n5) := ⟨u5.pc, m5, fun _ => rfl⟩
  have r5 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 22, 24, 26, 27] → reg n5 q = reg n4 q := fun q hq => by
    rw [u5.regs, runBlock_reg _ _ _ q u4.zero (by simp only [fsH3]; revert hq; revert q; decide)]
  have K5 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 24, 26, 27] → reg n5 q = reg n q := fun q hq => by
    rw [r5 q (by revert hq; revert q; decide),
      k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide), r3,
      runBlock_reg _ _ _ q u2.zero (by simp only [fsH2]; revert hq; revert q; decide)]
    by_cases hs : q = sp
    · subst hs; rw [sp2, rsp]
    · rw [K2 q (by revert hs hq; revert q; decide)]
  have sp5 : reg n5 sp = S := by rw [K5 sp (by decide)]; exact rsp
  -- memory facts from here back to the stage's start
  have back5 : ∀ d, d + 1 ≤ 0x420 → (d + 1 ≤ 0x74 ∨ 0xD9 ≤ d) → (d + 1 ≤ 0x144 ∨ 0x145 ≤ d) →
      M5 (S + BitVec.ofNat 32 d) = M (S + BitVec.ofNat 32 d) := fun d h1 h2 h3 => by
    rw [h5 _ (sepS S (by rcases h3 with h | h; exact .inr h; exact .inl h) (by decide) (by omega)),
      fr4 _ (F.lowB hbA (by decide) h1),
      fr2 _ (F.lowB hb90 (by decide) h1) (sepS S (by rcases h2 with h | h; exact .inr h; exact .inl h) (by decide) (by omega))]
  have saves5 : ∀ k, k < 11 → memLoad32 M5 (S + BitVec.ofNat 32 (0x41C - 4 * k)) = reg n0 (savedReg k) := fun k hk => by
    rw [← hS k hk]
    exact memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact back5 _ (by omega) (.inr (by omega)) (.inr (by omega))
  have hb1A : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have frame5 : ∀ x, Sep (S + 0xFFFFFE60) 0x5C0 x 1 → M5 x = M0 x := fun x hx => by
    have hN : Sep (S + 0xFFFFFF70) 0x90 x 1 := by
      have := hx.sub (c := 0x110) (l := 0x90) (by decide)
      rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x110 = S + 0xFFFFFF70 by rw [BitVec.add_assoc]; rfl] at this
    have hA : Sep (S + 0xFFFFFFB0) 0x50 x 1 := by
      have := hx.sub (c := 0x150) (l := 0x50) (by decide)
      rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x150 = S + 0xFFFFFFB0 by rw [BitVec.add_assoc]; rfl] at this
    rw [h5 x (fr_inFrame (by decide) hx), fr4 x hA, fr2 x hN (fr_inFrame (by decide) hx), hM x hx]
  have kq : ∀ q : Fin 32, q.val ∈ [3, 4, 26, 27] → reg n5 q = reg n0 q := fun q hq => by
    rw [K5 q (by revert hq; revert q; decide), k3 q hq]
  by_cases hP : P
  · -- Ok: the point to `out + 4`
    have chP : M (S + BitVec.ofNat 32 0x144 + 0x64) = 1 := by
      rw [show S + BitVec.ofNat 32 0x144 + 0x64 = S + BitVec.ofNat 32 0x1A8 by rw [BitVec.add_assoc]; rfl, hc,
        ite_eq_left hP]
    obtain ⟨n6, d6, u6⟩ := v5.notTaken C5.self 0x434 fs_at_432 (by decide) (by
      show branchTaken .beq (reg n5 a0) 0 = false; rw [a5, ite_eq_left hP]; decide)
    obtain ⟨n7, c7, u7⟩ := u6.self.block fsH4 C5.self fsH4_end ⟨trivial, trivial, trivial, trivial⟩
    have r7 : ∀ q, reg n7 q = (runBlock fsH4 (M5, reg n6)).2 q := fun q => by rw [u7.regs]
    obtain ⟨fA, fW, hFC⟩ := F.mc
    have o4 : Sep (out + BitVec.ofNat 32 4) 0x64 (S + 0xFFFFFE60) 0x5C0 := by
      have := sO.sub (c := 4) (l := 0x64) (by decide); exact this
    have hMC : Sep (out + BitVec.ofNat 32 4) 0x64 (MCS + 8) memcpyBodyCode.length := by
      have : 0x40000000 ≤ (MCS + 8 : Word).toNat := by decide
      exact sep_of_le (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide)
    have o16 : Sep (out + BitVec.ofNat 32 4) 0x64 (S + 0xFFFFFFF0) 16 := by
      have := o4.subR (c := 0x190) (l := 16) (by decide)
      rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x190 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
    have oB : Sep (out + BitVec.ofNat 32 4) 0x64 (S + BitVec.ofNat 32 0x74) 0x64 := by
      have := o4.subR (c := 0x1A0 + 0x74) (l := 0x64) (by decide)
      rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x74) = BitVec.ofNat 32 0x74 from rfl] at this
    obtain ⟨n8, c8, u8, fr8, k8⟩ := c_memcpy (dst := out + BitVec.ofNat 32 4) (src := S + BitVec.ofNat 32 0x74) (S := S)
      (N := 0x64) (⟨u7.pc, u7.mem, fun _ => rfl⟩ : St M5 FP n7 0x43E (reg n7)) C5.self C5.K fs_at_43e fs_at_442 (by decide)
      (by decide) (by rw [r7, runBlock_reg _ _ _ sp u6.self.zero (by decide), u6.regs]; exact sp5)
      (by rw [r7]; simp +decide only [runBlock, BInstr.run, fsH4, upd, ↓reduceIte]; rw [u6.regs, K5 24 (by decide), r24]; rfl)
      (by rw [r7]; simp +decide only [runBlock, BInstr.run, fsH4, upd, ↓reduceIte]; rw [u6.regs, sp5]; rfl)
      (by rw [r7]; simp +decide only [runBlock, BInstr.run, fsH4, upd, ↓reduceIte]; (try rw [u6.self.zero]); try rfl)
      ⟨C5.K.body, hMC, hFC, o16, F.mcN (by decide), oB, fA, fW, by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
        by rw [F.at _ (by decide)]; omega⟩
    have fr8' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (out + BitVec.ofNat 32 4) 0x64 x 1 → n8.mem x = M5 x :=
      fun x a b => by rw [fr8 x a, copyBytes_sep b (Nat.le_refl _)]
    have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
      sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
    have C8 := C5.hi fun x hx => fr8' x (lo16 x hx) (sep_of_le (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      (by have := x.isLt; omega))
    obtain ⟨n9, c9, u9⟩ := u8.block fsH5 C8.self fsH5_end ⟨trivial, trivial⟩
    obtain ⟨n10, d10, u10⟩ := u9.jump C8.self fs_at_448 (off' := 0x44C) (by decide) (by rw [u9.pc]; decide)
    have k8' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 24, 26, 27] → reg n8 q = reg n5 q := fun q hq => by
      rw [k8 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r7, runBlock_reg _ _ _ q u6.self.zero (by simp only [fsH4]; revert hq; revert q; decide), u6.regs]
    have r10 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 24, 26, 27] → reg n10 q = reg n5 q := fun q hq => by
      rw [u10.regs, runBlock_reg _ _ _ q u8.zero (by simp only [fsH5]; revert hq; revert q; decide)]; exact k8' q hq
    have a10 : reg n10 a0 = 0 := by
      rw [u10.regs]; simp +decide only [runBlock, BInstr.run, fsH5, upd, ↓reduceIte]; rw [u8.zero]; rfl
    have hos : Sep out 4 (S + BitVec.ofNat 32 0x3F4) 0x2C := by
      have := (sO.sub (c := 0) (l := 4) (by decide)).subR (c := 0x1A0 + 0x3F4) (l := 0x2C) (by decide)
      rwa [add_ofNat_zero, BitVec.add_assoc,
        show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x3F4) = BitVec.ofNat 32 0x3F4 from rfl] at this
    have oF' : ∀ d, d + 1 ≤ 0x420 → Sep (out + BitVec.ofNat 32 4) 0x64 (S + BitVec.ofNat 32 d) 1 := fun d hd => by
      have := o4.subR (c := 0x1A0 + d) (l := 1) (by omega)
      rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + d) = BitVec.ofNat 32 d by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
        omega] at this
    have saves8 : ∀ k, k < 11 → memLoad32 n8.mem (S + BitVec.ofNat 32 (0x41C - 4 * k)) = reg n0 (savedReg k) := fun k hk => by
      rw [← saves5 k hk]
      exact memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]
        exact fr8' _ (F.lowB hb16 (by decide) (by omega)) (oF' _ (by omega))
    obtain ⟨n11, c11, pc11, sp11, sv11, m11, k11⟩ := fs_epi (v := 0) (w := fun k => reg n0 (savedReg k)) C8 F u10.self
      (by rw [r10 sp (by decide)]; exact sp5) (by rw [r10 24 (by decide), K5 24 (by decide)]; exact r24) a10 hoa (by omega)
      hos saves8 hret
    have o4' : ∀ j, j < 0x64 → Sep (S + 0xFFFFFFF0) 16 (out + BitVec.ofNat 32 (4 + j)) 1 := fun j hj => by
      have := o16.sub (c := j) (l := 1) (by omega); rw [add_ofNat_assoc] at this; exact this.symm
    have ldO : ∀ k, k + 4 ≤ 0x64 → memLoad32 n11.mem (out + BitVec.ofNat 32 (4 + k)) =
        memLoad32 M5 (S + BitVec.ofNat 32 (0x74 + k)) := fun k hk => by
      rw [m11, memLoad32_store32_sep (by
          have := sep_offsets out (c := 0) (n := 4) (d := 4 + k) (k := 4) (.inl (by omega)) (by decide) (by omega)
          rwa [add_ofNat_zero] at this),
        memLoad32_congr (M := copyBytes M5 (out + BitVec.ofNat 32 4) (S + BitVec.ofNat 32 0x74) 0x64) fun j hj => by
          rw [add_ofNat_assoc, fr8 _ (by rw [Nat.add_assoc]; exact o4' _ (by omega))],
        ← add_ofNat_assoc out 4, cp_word hk (by decide), add_ofNat_assoc]
    have m5n2 : ∀ d, d + 1 ≤ 0x420 → (d + 1 ≤ 0x144 ∨ 0x145 ≤ d) →
        M5 (S + BitVec.ofNat 32 d) = n2.mem (S + BitVec.ofNat 32 d) := fun d h1 h2 => by
      rw [h5 _ (sepS S (by rcases h2 with h | h; exact .inr h; exact .inl h) (by decide) (by omega)),
        fr4 _ (F.lowB hbA (by decide) h1)]
    refine ⟨n11, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (.cons d6 (c7.trans (c8.trans (c9.trans
      (.cons d10 c11))))))))), ⟨pc11, sp11, sv11, fun q hq => ?_, fun x hx ho => ?_⟩, fun _ => ⟨?_, ?_, ?_, ?_⟩,
      fun h => absurd hP h⟩
    · rw [k11 q hq, r10 q (by revert hq; revert q; decide), kq q hq]
    · rw [m11, memStore32_get_sep ((ho.sub (c := 0) (l := 4) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h),
        fr8' x (by
          have := hx.sub (c := 0x190) (l := 16) (by decide)
          rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 0x190 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this)
          (ho.sub (c := 4) (l := 0x64) (by decide)), frame5 x hx]
    · rw [m11]; exact memLoad32_store32_same _ _ _
    · rw [← hX]
      exact accV_congr2 12 fun i hi => by
        rw [add_ofNat_assoc, ldO _ (by omega), show 0x74 + 4 * i = 0x74 + 4 * i from rfl,
          memLoad32_congr (M := n2.mem) fun j hj => by rw [add_ofNat_assoc]; exact m5n2 _ (by omega) (.inl (by omega)),
          ← add_ofNat_assoc S 0x74, w2 i hi, ite_eq_left chP]
    · rw [← hY]
      exact accV_congr2 12 fun i hi => by
        rw [add_ofNat_assoc, show 0x34 + 4 * i = 4 + (0x30 + 4 * i) by omega, ldO _ (by omega),
          memLoad32_congr (M := n2.mem) fun j hj => by rw [add_ofNat_assoc]; exact m5n2 _ (by omega) (.inl (by omega)),
          show 0x74 + (0x30 + 4 * i) = 0xA4 + 4 * i by omega,
          show S + BitVec.ofNat 32 (0xA4 + 4 * i) = S + BitVec.ofNat 32 0x74 + 0x30 + BitVec.ofNat 32 (4 * i) by
            rw [BitVec.add_assoc, BitVec.add_assoc, show (0x30 : Word) + BitVec.ofNat 32 (4 * i) = BitVec.ofNat 32 (0x30 + 4 * i) by
              rw [show (0x30 : Word) = BitVec.ofNat 32 0x30 from rfl, ofNat_add_ofNat], ofNat_add_ofNat, ← Nat.add_assoc],
          v2 i hi, ite_eq_left chP,
          show S + BitVec.ofNat 32 0x144 + 0x30 + BitVec.ofNat 32 (4 * i) = S + BitVec.ofNat 32 0x174 + BitVec.ofNat 32 (4 * i) by
            rw [BitVec.add_assoc S (BitVec.ofNat 32 0x144) 0x30]; rfl]
    · rw [m11, memStore32_get_sep (by
          have := sep_offsets out (c := 0) (n := 4) (d := 0x64) (k := 1) (.inl (by decide)) (by decide) (by decide)
          rwa [add_ofNat_zero] at this),
        show out + BitVec.ofNat 32 0x64 = out + BitVec.ofNat 32 4 + BitVec.ofNat 32 0x60 by rw [add_ofNat_assoc],
        fr8 _ (by rw [add_ofNat_assoc]; exact o4' _ (by decide)), cp_at (by decide) (by decide),
        show S + BitVec.ofNat 32 0x74 + BitVec.ofNat 32 0x60 = S + BitVec.ofNat 32 0xD4 by rw [add_ofNat_assoc],
        m5n2 _ (by decide) (.inl (by decide)),
        show S + BitVec.ofNat 32 0xD4 = S + BitVec.ofNat 32 0x74 + 0x60 by rw [BitVec.add_assoc]; rfl, z2, ite_eq_left chP,
        show S + BitVec.ofNat 32 0x144 + 0x60 = S + BitVec.ofNat 32 0x1A4 by rw [BitVec.add_assoc]; rfl, hz]
  · -- Err
    obtain ⟨n6, d6, u6⟩ := v5.taken C5.self 0x44A fs_at_432 (by decide) (by
      show branchTaken .beq (reg n5 a0) 0 = true; rw [a5, ite_eq_right hP]; decide)
    obtain ⟨n7, c7, R7, w7⟩ := fs_err (M := M0) (n := n0) C5 F u6.self (by rw [u6.regs]; exact sp5)
      (by rw [u6.regs, K5 24 (by decide)]; exact r24) hoa hO sO saves5 hret (fun q hq => by rw [u6.regs]; exact kq q hq)
      frame5
    exact ⟨n7, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (.cons d6 c7))))), R7, fun h => absurd h hP, fun _ => w7⟩

/-! ## The whole function -/

theorem memBytes_eq {M M' : Word → BitVec 8} {p p' : Word} {n : Nat}
    (h : ∀ i, i < n → M' (p' + BitVec.ofNat 32 i) = M (p + BitVec.ofNat 32 i)) : memBytes M' p' n = memBytes M p n := by
  unfold memBytes
  exact List.map_congr_left fun i hi => congrArg BitVec.toNat (h i (List.mem_range.mp hi))

/-- The 48-byte big-endian number at `inp + o`. -/
def fsVal (M : Word → BitVec 8) (inp : Word) (o : Nat) : Nat := beNat (memBytes M (inp + BitVec.ofNat 32 o) 48)

/-- When `from_sec1_bytes` accepts the 97 bytes at `inp`: tag 4, then `x`
and `y` below `p` on the curve, checked in Montgomery form. -/
def FsOk (M : Word → BitVec 8) (inp : Word) : Prop :=
  M inp = 4 ∧ fsVal M inp 1 < p384 ∧ fsVal M inp 0x31 < p384 ∧
    p3fm (fsVal M inp 0x31 * 2 ^ 384 % p384) (fsVal M inp 0x31 * 2 ^ 384 % p384) = dqAlpha (fsVal M inp 1 * 2 ^ 384 % p384)

instance (M : Word → BitVec 8) (inp : Word) : Decidable (FsOk M inp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem fsOk_one {v : Nat} : fsOk v = 1 ↔ v < p384 := by
  unfold fsOk
  by_cases h : v < p384
  · rw [ite_eq_left h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [ite_eq_right h]; exact ⟨fun e => absurd e (by decide), fun e => absurd e h⟩

theorem fsOk01 (v : Nat) : fsOk v = 0 ∨ fsOk v = 1 := by
  unfold fsOk
  by_cases h : v < p384
  · rw [ite_eq_left h]; exact .inr rfl
  · rw [ite_eq_right h]; exact .inl rfl

theorem fsMont_of {v : Nat} (h : v < p384) : fsMont v = v * 2 ^ 384 % p384 := by unfold fsMont; rw [ite_eq_left h]

theorem fsMont_lt (v : Nat) : fsMont v < p384 := by
  unfold fsMont
  by_cases h : v < p384
  · rw [ite_eq_left h]; exact Nat.mod_lt _ p384_pos
  · rw [ite_eq_right h]; exact p384_pos

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **The compiled `VerifyingKey<NistP384>::from_sec1_bytes`** on the 97
bytes at `inp`. When they are tag 4 and an `x` and `y` below `p` with
`y² = x³ + ax + b` (`FsOk`), it returns `Ok`: the word 0 at `out`, then the
point's `x` and `y` in Montgomery form at `out + 4` and `out + 0x34`, and the
identity flag 0 at `out + 0x64`. Otherwise it returns `Err`: the word 1. It
returns to `ra` with the saved registers restored and changes no memory
outside its frame and the 0x68 bytes at `out`. -/
theorem p384FromSec1_correct (m : Machine) {S inp out : Word} (C : FsCode m.mem) (D : P3Data m.mem) (F : Fr S 0x420)
    (hpc : m.pc = FP) (hsp : reg m sp = S + 0x420) (ha0 : reg m a0 = out) (ha1 : reg m a1 = inp)
    (hret : reg m ra &&& ~~~1 = reg m ra) (sI : Sep inp 0x61 (S + 0xFFFFFE60) 0x5C0) (hI : inp.toNat + 0x61 ≤ 0x40000000)
    (hoa : out.toNat % 4 = 0) (hO : out.toNat + 0x68 ≤ 0x40000000) (sO : Sep out 0x68 (S + 0xFFFFFE60) 0x5C0) :
    ∃ m', Steps m m' ∧ FsRet m.mem m S out m' ∧
      (FsOk m.mem inp → memLoad32 m'.mem out = 0 ∧
        accV m'.mem (out + BitVec.ofNat 32 4) 12 = fsVal m.mem inp 1 * 2 ^ 384 % p384 ∧
        accV m'.mem (out + BitVec.ofNat 32 0x34) 12 = fsVal m.mem inp 0x31 * 2 ^ 384 % p384 ∧
        m'.mem (out + BitVec.ofNat 32 0x64) = 0) ∧
      (¬ FsOk m.mem inp → memLoad32 m'.mem out = 1) := by
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have s0 : St m.mem FP m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  obtain ⟨fbad, fgood⟩ := fs_front C F s0 hsp ha0 ha1 sI hoa hO sO hret
  by_cases h4n : m.mem inp ≠ 4
  · obtain ⟨n', c', R', w'⟩ := fbad h4n
    exact ⟨n', c', R', fun h => absurd h.1 h4n, fun _ => w'⟩
  have h4 : m.mem inp = 4 := Decidable.of_not_not h4n
  obtain ⟨n1, c1, u1, sp1, r19, r24, k1⟩ := fgood h4
  have hb1A : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have lowS : ∀ {k : Nat} {B' : Word} {x : Word}, B'.toNat = S.toNat - k → 0 < k → k ≤ 0x1A0 →
      Sep (S + 0xFFFFFE60) 0x5C0 x 1 → Sep B' k x 1 := fun {k B' x} hB' hk hk' hx => by
    have := hx.sub (c := 0x1A0 - k) (l := k) (by omega)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 - k) = B' by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hb1A, hB']; omega] at this
  have iF : ∀ {j c l : Nat}, j < 0x61 → c + l ≤ 0x420 → Sep (S + BitVec.ofNat 32 c) l (inp + BitVec.ofNat 32 j) 1 :=
    fun {j c l} h1 h2 => fr_inFrame h2 ((sI.sub (c := j) (l := 1) (by omega)).symm)
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have hb50 : (S + 0xFFFFFFB0).toNat = S.toNat - 0x50 := F.below 0x50 (by decide) (by decide)
  have hbF0 : (S + 0xFFFFFF10).toNat = S.toNat - 0xF0 := F.below 0xF0 (by decide) (by decide)
  have hb44 : (S + 0xFFFFFFBC).toNat = S.toNat - 0x44 := F.below 0x44 (by decide) (by decide)
  have sq : ∀ c l d, c + l ≤ 0x420 → d + 1 ≤ 0x420 → (c + l ≤ d ∨ d + 1 ≤ c) →
      Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 d) 1 := fun c l d h1 h2 h3 => sepS S h3 (by omega) (by omega)
  -- the memory after the checks
  have hM1 : ∀ x, Sep (S + 0xFFFFFE60) 0x5C0 x 1 → fsM3 m.mem S m 4 x = m.mem x := fun x hx =>
    fsM3_out (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx)
  have C1 : FsCode (fsM3 m.mem S m 4) := C.hi fun x hx => fsM3_out (F.hiOut (by decide) hx) (F.hiOut (by decide) hx)
  have hM1i : ∀ j, j < 0x61 → fsM3 m.mem S m 4 (inp + BitVec.ofNat 32 j) = m.mem (inp + BitVec.ofNat 32 j) := fun j hj =>
    fsM3_out (iF hj (by decide)) (iF hj (by decide))
  -- the stages
  obtain ⟨n2, c2, u2, C2, hb2, fr2, sp2, k2⟩ := fs_stC C1 F u1 sp1 r19 sI hI
  have ht : n2.mem (S + BitVec.ofNat 32 0x12) = 4 := by
    have := hb2 0 (by decide); rw [hM1i 0 (by decide), add_ofNat_zero, h4] at this; exact this
  obtain ⟨n3, c3, u3, C3, fr3, sp3, e319, e322, k3⟩ := fs_stD C2 F u2 sp2 ht
  have o2 : ∀ x, Sep (S + 0xFFFFFE60) 0x5C0 x 1 → n2.mem x = m.mem x := fun x hx => by
    rw [fr2 x (lowS hb16 (by decide) (by decide) hx) (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx)
      (fr_inFrame (by decide) hx), hM1 x hx]
  have o3 : ∀ x, Sep (S + 0xFFFFFE60) 0x5C0 x 1 → n3.mem x = m.mem x := fun x hx => by
    rw [fr3 x (lowS hb50 (by decide) (by decide) hx), o2 x hx]
  have D3 : P3Data n3.mem := D.of F o3
  obtain ⟨n4, c4, u4, C4, D4, hy4, e418, fr4, sp4, k4⟩ := fs_decY C3 D3 F u3 sp3
  obtain ⟨n5, c5, u5, C5, D5, hx5, e519, fr5, sp5, k5⟩ := fs_decX C4 D4 F u4 sp4 (by rw [k4 19 (by decide)]; exact e319)
  have hY5 : accV n5.mem (S + BitVec.ofNat 32 0x364) 12 = fsMont (beNat (memBytes n3.mem (S + BitVec.ofNat 32 0x43) 48)) := by
    rw [← hy4]; exact accV_keep fun q hq => fr5 _ (F.lowB hb1A (by decide) (by omega))
      (sq _ _ _ (by decide) (by omega) (.inl (by omega))) (sq _ _ _ (by decide) (by omega) (.inl (by omega)))
      (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
  obtain ⟨n6, c6, u6, C6, D6, h334, h1AC, hDC, h10C, fr6, sp6, k6⟩ := fs_stF C5 D5 F u5 sp5 hx5 (fsMont_lt _) hY5 (fsMont_lt _)
  obtain ⟨n7, c7, u7, C7, D7, h144, h174, h1A4, h1A8, fr7, sp7, k7⟩ := fs_stG C6 D6 F u6 sp6 h334 h1AC hDC h10C
    (by rw [k6 19 (by decide)]; exact e519) (by rw [k6 18 (by decide), k5 18 (by decide)]; exact e418) (fsOk01 _) (fsOk01 _)
  -- what stages D to G keep
  have keep7 : ∀ d, d + 1 ≤ 0x420 → (d + 1 ≤ 0xDC ∨ 0x3F4 ≤ d) → (d + 1 ≤ 0x12 ∨ 0x73 ≤ d) →
      n7.mem (S + BitVec.ofNat 32 d) = n2.mem (S + BitVec.ofNat 32 d) := fun d h1 h2 h0 => by
    have a1 : ∀ c l, c + l ≤ 0x420 → 0xDC ≤ c → c + l ≤ 0x3F4 → Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 d) 1 :=
      fun c l hl hc hc' => sq _ _ _ hl h1 (by rcases h2 with h | h; exact .inr (by omega); exact .inl (by omega))
    rw [fr7 _ (F.lowB hb44 (by decide) h1) (a1 _ _ (by decide) (by decide) (by decide)),
      fr6 _ (F.lowB hbF0 (by decide) h1) (a1 _ _ (by decide) (by decide) (by decide)) (a1 _ _ (by decide) (by decide) (by decide))
        (a1 _ _ (by decide) (by decide) (by decide)) (a1 _ _ (by decide) (by decide) (by decide)),
      fr5 _ (F.lowB hb1A (by decide) h1) (a1 _ _ (by decide) (by decide) (by decide)) (a1 _ _ (by decide) (by decide) (by decide))
        (a1 _ _ (by decide) (by decide) (by decide)),
      fr4 _ (F.lowB hb1A (by decide) h1) (a1 _ _ (by decide) (by decide) (by decide)) (a1 _ _ (by decide) (by decide) (by decide))
        (a1 _ _ (by decide) (by decide) (by decide)),
      fr3 _ (F.lowB hb50 (by decide) h1)]
  have hy3 : beNat (memBytes n3.mem (S + BitVec.ofNat 32 0x43) 48) = fsVal m.mem inp 0x31 := by
    unfold fsVal
    exact congrArg beNat (memBytes_eq fun i hi => by
      rw [add_ofNat_assoc, add_ofNat_assoc, fr3 _ (F.lowB hb50 (by decide) (by omega)),
        show 0x43 + i = 0x12 + (0x31 + i) by omega, hb2 _ (by omega), hM1i _ (by omega)])
  have hx4 : beNat (memBytes n4.mem (S + BitVec.ofNat 32 0x13) 48) = fsVal m.mem inp 1 := by
    unfold fsVal
    exact congrArg beNat (memBytes_eq fun i hi => by
      rw [add_ofNat_assoc, add_ofNat_assoc, fr4 _ (F.lowB hb1A (by decide) (by omega))
        (sq _ _ _ (by decide) (by omega) (.inr (by omega))) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
        (sq _ _ _ (by decide) (by omega) (.inr (by omega))), fr3 _ (F.lowB hb50 (by decide) (by omega)),
        show 0x13 + i = 0x12 + (1 + i) by omega, hb2 _ (by omega), hM1i _ (by omega)])
  rw [hy3] at h1A8 h174
  rw [hx4] at h1A8 h144
  have hS7 : ∀ k, k < 11 → memLoad32 n7.mem (S + BitVec.ofNat 32 (0x41C - 4 * k)) = reg m (savedReg k) := fun k hk => by
    rw [← fsM3_saves (M := m.mem) (S := S) (n := m) (b := 4) k hk]
    exact memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, keep7 _ (by omega) (.inr (by omega)) (.inr (by omega)),
        fr2 _ (F.lowB hb16 (by decide) (by omega)) (sq _ _ _ (by decide) (by omega) (.inl (by omega)))
          (sq _ _ _ (by decide) (by omega) (.inl (by omega))) (sq _ _ _ (by decide) (by omega) (.inl (by omega)))]
  have hM7 : ∀ x, Sep (S + 0xFFFFFE60) 0x5C0 x 1 → n7.mem x = m.mem x := fun x hx => by
    rw [fr7 x (lowS hb44 (by decide) (by decide) hx) (fr_inFrame (by decide) hx),
      fr6 x (lowS hbF0 (by decide) (by decide) hx) (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx)
        (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx),
      fr5 x (lowS hb1A (by decide) (by decide) hx) (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx)
        (fr_inFrame (by decide) hx),
      fr4 x (lowS hb1A (by decide) (by decide) hx) (fr_inFrame (by decide) hx) (fr_inFrame (by decide) hx)
        (fr_inFrame (by decide) hx), o3 x hx]
  obtain ⟨n8, c8, R8, okP, badP⟩ := fs_stH (M0 := m.mem) (n0 := m) C7 F u7 sp7
    (by rw [k7 22 (by decide), k6 22 (by decide), k5 22 (by decide), k4 22 (by decide)]; exact e322)
    (by rw [k7 24 (by decide), k6 24 (by decide), k5 24 (by decide), k4 24 (by decide), k3 24 (by decide),
      k2 24 (by decide)]; exact r24)
    h144 h174 h1A4 h1A8 hoa hO sO hS7 hret
    (fun q hq => by
      rw [k7 q (by revert hq; revert q; decide), k6 q (by revert hq; revert q; decide), k5 q (by revert hq; revert q; decide),
        k4 q (by revert hq; revert q; decide), k3 q (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide),
        k1 q hq]) hM7
  refine ⟨n8, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans c8)))))), R8, fun hok => ?_, fun hno => ?_⟩
  · obtain ⟨_, hxl, hyl, hc⟩ := hok
    obtain ⟨w0, wx, wy, wz⟩ := okP ⟨by rw [fsMont_of hxl, fsMont_of hyl]; exact hc, fsOk_one.2 hxl, fsOk_one.2 hyl⟩
    exact ⟨w0, by rw [wx, fsMont_of hxl], by rw [wy, fsMont_of hyl], wz⟩
  · refine badP fun ⟨hc, hxo, hyo⟩ => hno ⟨h4, fsOk_one.1 hxo, fsOk_one.1 hyo, ?_⟩
    rw [← fsMont_of (fsOk_one.1 hxo), ← fsMont_of (fsOk_one.1 hyo)]; exact hc

end C3.RV32.Fs
