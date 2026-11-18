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

end C3.RV32.Fs
