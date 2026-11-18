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

end C3.RV32.Fs
