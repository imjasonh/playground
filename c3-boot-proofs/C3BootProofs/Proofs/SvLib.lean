import C3BootProofs.Proofs.SvAt
import C3BootProofs.Proofs.Pv384A

/-!
# `sigstore::verify`: the frame, the prologue, and the exits

`c3_verify::sigstore::verify(out, bundle, root, digest)` opens a frame of
0x4C0 bytes. With the frame's base at `B + 0x21A0`, `Fr B 0x2660` describes
the frame and the 0x21A0 bytes below it. `p256_verify_prehash` needs more:
its frame goes down to `B - 0x1590`, so `SvR` excludes the stack from there.
The prologue saves `ra` and `s0..s11` at the top of the frame. Every error
leaves through 0x7A4, which stores 1 and the error's code at `out` and
returns; the success paths store 0 and the result and return through 0x7AE.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- What a step of `sigstore::verify` and its callees may write: the stack
from `B - 0x1590` to the caller's `sp`. -/
def SvR (B : Word) (x : Word) : Prop := Sep (B + 0xFFFFEA70) 0x3BF0 x 1

/-- `M'` agrees with `M` on the frame, except for the `w` bytes at offset `c`. -/
def SvKeep (B : Word) (M M' : Word → BitVec 8) (c w : Nat) : Prop :=
  ∀ e, e + 1 ≤ 0x4C0 → (e < c ∨ c + w ≤ e) →
    M' (B + 0x21A0 + BitVec.ofNat 32 e) = M (B + 0x21A0 + BitVec.ofNat 32 e)

/-- The prologue's saves, in order, at the top of the frame. -/
def svSaves (M : Word → BitVec 8) (B : Word) (n : Machine) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32
    (memStore32 (memStore32 (memStore32 (memStore32 M
    (B + BitVec.ofNat 32 0x265C) (reg n ra)) (B + BitVec.ofNat 32 0x2658) (reg n (8 : Fin 32)))
    (B + BitVec.ofNat 32 0x2654) (reg n (9 : Fin 32))) (B + BitVec.ofNat 32 0x2650) (reg n (18 : Fin 32)))
    (B + BitVec.ofNat 32 0x264C) (reg n (19 : Fin 32))) (B + BitVec.ofNat 32 0x2648) (reg n (20 : Fin 32)))
    (B + BitVec.ofNat 32 0x2644) (reg n (21 : Fin 32))) (B + BitVec.ofNat 32 0x2640) (reg n (22 : Fin 32)))
    (B + BitVec.ofNat 32 0x263C) (reg n (23 : Fin 32))) (B + BitVec.ofNat 32 0x2638) (reg n (24 : Fin 32)))
    (B + BitVec.ofNat 32 0x2634) (reg n (25 : Fin 32))) (B + BitVec.ofNat 32 0x2630) (reg n (26 : Fin 32)))
    (B + BitVec.ofNat 32 0x262C) (reg n (27 : Fin 32))

theorem ld_st_sv {M : Word → BitVec 8} {S v : Word} {c d : Nat} (hc : c % 4 = 0) (hd : d % 4 = 0)
    (hc' : c + 4 ≤ 0x10000) (hd' : d + 4 ≤ 0x10000) :
    memLoad32 (memStore32 M (S + BitVec.ofNat 32 c) v) (S + BitVec.ofNat 32 d) =
      if c = d then v else memLoad32 M (S + BitVec.ofNat 32 d) := ld_st_pv hc hd hc' hd'

theorem svSaves_read {M : Word → BitVec 8} {B : Word} {n : Machine} :
    ∀ k, k < 13 → memLoad32 (svSaves M B n) (B + BitVec.ofNat 32 (0x265C - 4 * k)) = reg n (savedReg k) := by
  intro k hk
  match k, hk with
  | 0, _ => unfold svSaves; simp (disch := decide) only [ld_st_sv, ite_eq_right, ite_eq_left]; rfl
  | 1, _ => unfold svSaves; simp (disch := decide) only [ld_st_sv, ite_eq_right, ite_eq_left]; rfl
  | 2, _ => unfold svSaves; simp (disch := decide) only [ld_st_sv, ite_eq_right, ite_eq_left]; rfl
  | 3, _ => unfold svSaves; simp (disch := decide) only [ld_st_sv, ite_eq_right, ite_eq_left]; rfl
  | 4, _ => unfold svSaves; simp (disch := decide) only [ld_st_sv, ite_eq_right, ite_eq_left]; rfl
  | 5, _ => unfold svSaves; simp (disch := decide) only [ld_st_sv, ite_eq_right, ite_eq_left]; rfl
  | 6, _ => unfold svSaves; simp (disch := decide) only [ld_st_sv, ite_eq_right, ite_eq_left]; rfl
  | 7, _ => unfold svSaves; simp (disch := decide) only [ld_st_sv, ite_eq_right, ite_eq_left]; rfl
  | 8, _ => unfold svSaves; simp (disch := decide) only [ld_st_sv, ite_eq_right, ite_eq_left]; rfl
  | 9, _ => unfold svSaves; simp (disch := decide) only [ld_st_sv, ite_eq_right, ite_eq_left]; rfl
  | 10, _ => unfold svSaves; simp (disch := decide) only [ld_st_sv, ite_eq_right, ite_eq_left]; rfl
  | 11, _ => unfold svSaves; simp (disch := decide) only [ld_st_sv, ite_eq_right, ite_eq_left]; rfl
  | 12, _ => unfold svSaves; simp (disch := decide) only [ld_st_sv, ite_eq_right, ite_eq_left]; rfl

theorem svSaves_out {M : Word → BitVec 8} {B : Word} {n : Machine} {x : Word}
    (h : Sep (B + BitVec.ofNat 32 0x262C) 0x34 x 1) : svSaves M B n x = M x := by
  have hs : ∀ c, 0x262C ≤ c → c + 4 ≤ 0x2660 → Sep (B + BitVec.ofNat 32 c) 4 x 1 := fun c h1 h2 => by
    have := h.sub (c := c - 0x262C) (l := 4) (by omega)
    rwa [add_ofNat_assoc, show 0x262C + (c - 0x262C) = c by omega] at this
  unfold svSaves
  simp (disch := first | decide | exact hs _ (by decide) (by decide)) only [memStore32_get_sep]

/-- From the entry to the call to `Der::sequence` at 0x5C. -/
def svA1 : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFB40, .aluImm .add a4 sp 0x480,
   .sw a4 ra 0x3C,
   .sw a4 (8 : Fin 32) 0x38,
   .sw a4 (9 : Fin 32) 0x34,
   .sw a4 (18 : Fin 32) 0x30,
   .sw a4 (19 : Fin 32) 0x2C,
   .sw a4 (20 : Fin 32) 0x28,
   .sw a4 (21 : Fin 32) 0x24,
   .sw a4 (22 : Fin 32) 0x20,
   .sw a4 (23 : Fin 32) 0x1C,
   .sw a4 (24 : Fin 32) 0x18,
   .sw a4 (25 : Fin 32) 0x14,
   .sw a4 (26 : Fin 32) 0x10,
   .sw a4 (27 : Fin 32) 0xC,
   .alu .add (20 : Fin 32) x0 a3, .alu .add (21 : Fin 32) x0 a2, .alu .add (19 : Fin 32) x0 a1,
   .alu .add (18 : Fin 32) x0 a0, .lw (26 : Fin 32) a1 0x0, .lw (22 : Fin 32) a1 0x4, .aluImm .add a0 sp 0x300,
   .sw a0 (26 : Fin 32) 0x60, .alu .add a1 x0 (22 : Fin 32), .sw a0 a1 0x64, .sw a0 (26 : Fin 32) 0x68,
   .sw a0 a1 0x6C, .aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x360]

set_option maxRecDepth 100000 in
theorem svA1_end : blockEnd sigstoreVerifyCode 0 svA1 = some 0x5C := by decide

/-- The memory at 0x5C: the saves, and a `Der` reader over the leaf
certificate at offset 0x360 of the frame. -/
def svProMem (M : Word → BitVec 8) (B : Word) (n : Machine) (lp ll : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (svSaves M B n) (B + BitVec.ofNat 32 0x2500) lp)
    (B + BitVec.ofNat 32 0x2504) ll) (B + BitVec.ofNat 32 0x2508) lp) (B + BitVec.ofNat 32 0x250C) ll

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The prologue**, from the entry to the call to `Der::sequence` at
0x5C: save `ra` and `s0..s11`, open the frame at `B + 0x21A0`, keep the
arguments in `s2`, `s3`, `s5`, and `s4`, and set up the reader over the
leaf certificate, whose address and length are the first two words of the
bundle. -/
theorem sv_pro {M : Word → BitVec 8} {n : Machine} {B : Word} (C : CodeIn M SV sigstoreVerifyCode)
    (F : Fr B 0x2660) (s : St M SV n 0 (reg n)) (rsp : reg n sp = B + 0x2660)
    (hb : (reg n a1).toNat % 4 = 0) (sb : Sep (reg n a1) 8 (B + BitVec.ofNat 32 0x262C) 0x34) :
    ∃ n', Steps n n' ∧
      St (svProMem M B n (memLoad32 M (reg n a1)) (memLoad32 M (reg n a1 + 4))) SV n' 0x5C (reg n') ∧
      reg n' sp = B + 0x21A0 ∧ reg n' (18 : Fin 32) = reg n a0 ∧ reg n' (19 : Fin 32) = reg n a1 ∧
      reg n' (21 : Fin 32) = reg n a2 ∧ reg n' (20 : Fin 32) = reg n a3 ∧
      reg n' (26 : Fin 32) = memLoad32 M (reg n a1) ∧ reg n' (22 : Fin 32) = memLoad32 M (reg n a1 + 4) ∧
      reg n' a0 = B + BitVec.ofNat 32 0x2220 ∧ reg n' a1 = B + BitVec.ofNat 32 0x2500 ∧
      ∀ q, q.val ∈ [3, 4] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hA : aluEval .add (B + 0x2660) 0xFFFFFB40 = B + 0x21A0 := by
    show B + 0x2660 + 0xFFFFFB40 = B + 0x21A0
    rw [BitVec.add_assoc]; rfl
  have hA4 : aluEval .add (B + 0x21A0) 0x480 = B + BitVec.ofNat 32 0x2620 := by
    show B + 0x21A0 + 0x480 = B + BitVec.ofNat 32 0x2620
    rw [BitVec.add_assoc]; rfl
  have hD : aluEval .add (B + 0x21A0) 0x300 = B + BitVec.ofNat 32 0x24A0 := by
    show B + 0x21A0 + 0x300 = B + BitVec.ofNat 32 0x24A0
    rw [BitVec.add_assoc]; rfl
  have hR : aluEval .add (B + 0x21A0) 0x80 = B + BitVec.ofNat 32 0x2220 := by
    show B + 0x21A0 + 0x80 = B + BitVec.ofNat 32 0x2220
    rw [BitVec.add_assoc]; rfl
  have hR1 : aluEval .add (B + 0x21A0) 0x360 = B + BitVec.ofNat 32 0x2500 := by
    show B + 0x21A0 + 0x360 = B + BitVec.ofNat 32 0x2500
    rw [BitVec.add_assoc]; rfl
  have alB : ∀ (c : Nat) (k : Word), c + k.toNat + 4 ≤ 0x2660 → (c + k.toNat) % 4 = 0 →
      (B + BitVec.ofNat 32 c + k).toNat % 4 = 0 := fun c k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  have sepB : ∀ (c : Nat) (k : Word), c + k.toNat + 4 ≤ 0x2660 →
      Sep (B + BitVec.ofNat 32 c + k) 4 SV sigstoreVerifyCode.length := fun c k h1 => by
    rw [frame_lit k (by omega)]; exact F.sepHi (by omega) (by decide) (by decide)
  have e0 : reg n a1 + 0 = reg n a1 := BitVec.add_zero _
  have hb0 : (reg n a1 + 0).toNat % 4 = 0 := by rw [e0]; exact hb
  obtain ⟨n1, c1, u1⟩ := s.block svA1 C svA1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, svA1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp, hA, hA4, hD]
    exact ⟨⟨alB 0x2620 0x3C (by decide) (by decide), sepB 0x2620 0x3C (by decide)⟩,
      ⟨alB 0x2620 0x38 (by decide) (by decide), sepB 0x2620 0x38 (by decide)⟩,
      ⟨alB 0x2620 0x34 (by decide) (by decide), sepB 0x2620 0x34 (by decide)⟩,
      ⟨alB 0x2620 0x30 (by decide) (by decide), sepB 0x2620 0x30 (by decide)⟩,
      ⟨alB 0x2620 0x2C (by decide) (by decide), sepB 0x2620 0x2C (by decide)⟩,
      ⟨alB 0x2620 0x28 (by decide) (by decide), sepB 0x2620 0x28 (by decide)⟩,
      ⟨alB 0x2620 0x24 (by decide) (by decide), sepB 0x2620 0x24 (by decide)⟩,
      ⟨alB 0x2620 0x20 (by decide) (by decide), sepB 0x2620 0x20 (by decide)⟩,
      ⟨alB 0x2620 0x1C (by decide) (by decide), sepB 0x2620 0x1C (by decide)⟩,
      ⟨alB 0x2620 0x18 (by decide) (by decide), sepB 0x2620 0x18 (by decide)⟩,
      ⟨alB 0x2620 0x14 (by decide) (by decide), sepB 0x2620 0x14 (by decide)⟩,
      ⟨alB 0x2620 0x10 (by decide) (by decide), sepB 0x2620 0x10 (by decide)⟩,
      ⟨alB 0x2620 0xC (by decide) (by decide), sepB 0x2620 0xC (by decide)⟩,
      hb0, aligned_add hb (k := 4) (by decide),
      ⟨alB 0x24A0 0x60 (by decide) (by decide), sepB 0x24A0 0x60 (by decide)⟩,
      ⟨alB 0x24A0 0x64 (by decide) (by decide), sepB 0x24A0 0x64 (by decide)⟩,
      ⟨alB 0x24A0 0x68 (by decide) (by decide), sepB 0x24A0 0x68 (by decide)⟩,
      ⟨alB 0x24A0 0x6C (by decide) (by decide), sepB 0x24A0 0x6C (by decide)⟩⟩)
  have sv1 : ∀ j, j < 4 → svSaves M B n (reg n a1 + BitVec.ofNat 32 j) = M (reg n a1 + BitVec.ofNat 32 j) :=
    fun j hj => svSaves_out (sb.sub (c := j) (l := 1) (by omega)).symm
  have sv2 : ∀ j, j < 4 → svSaves M B n (reg n a1 + 4 + BitVec.ofNat 32 j) = M (reg n a1 + 4 + BitVec.ofNat 32 j) :=
    fun j hj => svSaves_out (by
      have := (sb.sub (c := 4 + j) (l := 1) (by omega)).symm
      rwa [← add_ofNat_assoc] at this)
  have hl1 : memLoad32 (svSaves M B n) (reg n a1 + 0) = memLoad32 M (reg n a1) := by
    rw [e0]; exact memLoad32_congr sv1
  have hl2 : memLoad32 (svSaves M B n) (reg n a1 + 4) = memLoad32 M (reg n a1 + 4) := memLoad32_congr sv2
  have m1 : n1.mem = svProMem M B n (memLoad32 (svSaves M B n) (reg n a1 + 0))
      (memLoad32 (svSaves M B n) (reg n a1 + 4)) := by
    rw [u1.mem]; simp only [runBlock, BInstr.run, svA1]; simp +decide only [upd, ↓reduceIte]
    rw [rsp, hA, hA4, hD]
    simp (disch := decide) only [frame_lit, BitVec.reduceToNat, Nat.reduceAdd]
    have z : ∀ x : Word, (0 : Word) + x = x := fun x => BitVec.zero_add x
    simp only [aluEval, z]
    unfold svProMem svSaves
    rfl
  rw [hl1, hl2] at m1
  have g : ∀ q, reg n1 q = (runBlock svA1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have z : ∀ x : Word, (0 : Word) + x = x := fun x => BitVec.zero_add x
  refine ⟨n1, c1, ⟨u1.pc, m1, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [g]; simp +decide only [runBlock, BInstr.run, svA1, upd, ↓reduceIte]; rw [rsp, hA]
  · rw [g]; simp +decide only [runBlock, BInstr.run, svA1, upd, ↓reduceIte, aluEval, z]
  · rw [g]; simp +decide only [runBlock, BInstr.run, svA1, upd, ↓reduceIte, aluEval, z]
  · rw [g]; simp +decide only [runBlock, BInstr.run, svA1, upd, ↓reduceIte, aluEval, z]
  · rw [g]; simp +decide only [runBlock, BInstr.run, svA1, upd, ↓reduceIte, aluEval, z]
  · rw [g]; simp +decide only [runBlock, BInstr.run, svA1, upd, ↓reduceIte]; rw [rsp, hA, hA4]
    simp (disch := decide) only [frame_lit, BitVec.reduceToNat, Nat.reduceAdd]
    rw [← hl1]; rfl
  · rw [g]; simp +decide only [runBlock, BInstr.run, svA1, upd, ↓reduceIte]; rw [rsp, hA, hA4]
    simp (disch := decide) only [frame_lit, BitVec.reduceToNat, Nat.reduceAdd]
    rw [← hl2]; rfl
  · rw [g]; simp +decide only [runBlock, BInstr.run, svA1, upd, ↓reduceIte]; rw [rsp, hA, hR]
  · rw [g]; simp +decide only [runBlock, BInstr.run, svA1, upd, ↓reduceIte]; rw [rsp, hA, hR1]
  · rw [g, runBlock_reg _ _ _ q hz (by simp only [svA1]; revert hq; revert q; decide)]

/-- From 0x7AE to the return: restore `ra` and `s0..s11` and close the frame. -/
def svE : List BInstr :=
  [.aluImm .add a0 sp 0x480, .lw ra a0 0x3C, .lw (8 : Fin 32) a0 0x38, .lw (9 : Fin 32) a0 0x34, .lw (18 : Fin 32) a0 0x30, .lw (19 : Fin 32) a0 0x2C, .lw (20 : Fin 32) a0 0x28, .lw (21 : Fin 32) a0 0x24, .lw (22 : Fin 32) a0 0x20, .lw (23 : Fin 32) a0 0x1C, .lw (24 : Fin 32) a0 0x18, .lw (25 : Fin 32) a0 0x14, .lw (26 : Fin 32) a0 0x10, .lw (27 : Fin 32) a0 0xC,
   .aluImm .add sp sp 0x4C0]

set_option maxRecDepth 100000 in
theorem svE_end : blockEnd sigstoreVerifyCode 0x7AE svE = some 0x7E6 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The return**, from 0x7AE: restore `ra` and `s0..s11` from the top of
the frame, close it, and return. -/
theorem sv_ret {M : Word → BitVec 8} {n : Machine} {B : Word} {v : Nat → Word} (C : CodeIn M SV sigstoreVerifyCode)
    (F : Fr B 0x2660) (s : St M SV n 0x7AE (reg n)) (rsp : reg n sp = B + 0x21A0)
    (hS : ∀ k, k < 13 → memLoad32 M (B + BitVec.ofNat 32 (0x265C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0) :
    ∃ n', Steps n n' ∧ n'.pc = v 0 ∧ n'.mem = M ∧ reg n' sp = B + 0x2660 ∧
      (∀ k, k < 13 → reg n' (savedReg k) = v k) ∧
      reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hA : aluEval .add (B + 0x21A0) 0x480 = B + BitVec.ofNat 32 0x2620 := by
    show B + 0x21A0 + 0x480 = B + BitVec.ofNat 32 0x2620
    rw [BitVec.add_assoc]; rfl
  have alB : ∀ (k : Word), 0x2620 + k.toNat + 4 ≤ 0x2660 → (0x2620 + k.toNat) % 4 = 0 →
      (B + BitVec.ofNat 32 0x2620 + k).toNat % 4 = 0 := fun k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  obtain ⟨n1, c1, u1⟩ := s.block svE C svE_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, svE]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp, hA]
    exact ⟨alB 0x3C (by decide) (by decide), alB 0x38 (by decide) (by decide), alB 0x34 (by decide) (by decide), alB 0x30 (by decide) (by decide), alB 0x2C (by decide) (by decide), alB 0x28 (by decide) (by decide), alB 0x24 (by decide) (by decide), alB 0x20 (by decide) (by decide), alB 0x1C (by decide) (by decide), alB 0x18 (by decide) (by decide), alB 0x14 (by decide) (by decide), alB 0x10 (by decide) (by decide), alB 0xC (by decide) (by decide)⟩)
  have m1 : (runBlock svE (M, reg n)).1 = M := rfl
  obtain ⟨n2, st2, pc2, mem2, regs2⟩ := u1.jalr (by rw [m1]; exact C) sv_at_7e6
  have ld : ∀ k, k < 13 → ∀ c : Word, c.toNat = 0x3C - 4 * k →
      memLoad32 M (B + BitVec.ofNat 32 0x2620 + c) = v k := fun k hk c hc => by
    rw [frame_lit _ (by omega), hc, show 0x2620 + (0x3C - 4 * k) = 0x265C - 4 * k by omega]; exact hS k hk
  have ra1 : (runBlock svE (M, reg n)).2 ra = v 0 := by
    simp +decide only [runBlock, BInstr.run, svE, upd, ↓reduceIte]
    rw [rsp, hA]; exact ld 0 (by decide) _ (by decide)
  refine ⟨n2, c1.trans (.single st2), ?_, mem2.trans m1, ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [pc2, ra1]; exact (congrArg (· &&& ~~~1) (BitVec.add_zero _)).trans hret
  · rw [regs2]; simp +decide only [runBlock, BInstr.run, svE, upd, ↓reduceIte]; rw [rsp]
    show B + 0x21A0 + 0x4C0 = B + 0x2660
    rw [BitVec.add_assoc]; rfl
  · rw [regs2]
    match k, hk with
    | 0, _ => simp +decide only [runBlock, BInstr.run, svE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 0 (by decide) _ (by decide)
    | 1, _ => simp +decide only [runBlock, BInstr.run, svE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 1 (by decide) _ (by decide)
    | 2, _ => simp +decide only [runBlock, BInstr.run, svE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 2 (by decide) _ (by decide)
    | 3, _ => simp +decide only [runBlock, BInstr.run, svE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 3 (by decide) _ (by decide)
    | 4, _ => simp +decide only [runBlock, BInstr.run, svE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 4 (by decide) _ (by decide)
    | 5, _ => simp +decide only [runBlock, BInstr.run, svE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 5 (by decide) _ (by decide)
    | 6, _ => simp +decide only [runBlock, BInstr.run, svE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 6 (by decide) _ (by decide)
    | 7, _ => simp +decide only [runBlock, BInstr.run, svE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 7 (by decide) _ (by decide)
    | 8, _ => simp +decide only [runBlock, BInstr.run, svE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 8 (by decide) _ (by decide)
    | 9, _ => simp +decide only [runBlock, BInstr.run, svE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 9 (by decide) _ (by decide)
    | 10, _ => simp +decide only [runBlock, BInstr.run, svE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 10 (by decide) _ (by decide)
    | 11, _ => simp +decide only [runBlock, BInstr.run, svE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 11 (by decide) _ (by decide)
    | 12, _ => simp +decide only [runBlock, BInstr.run, svE, upd, ↓reduceIte, savedReg]; rw [rsp, hA]; exact ld 12 (by decide) _ (by decide)
    | _ + 13, h => exact absurd h (by omega)
  · rw [regs2, runBlock_reg _ _ _ 3 hz (by decide)]
  · rw [regs2, runBlock_reg _ _ _ 4 hz (by decide)]

/-- From 0x7A4 to 0x7AE: `Err` with the code in `s0`. -/
def svX : List BInstr := [.aluImm .add a0 x0 0x1, .sb (18 : Fin 32) a0 0x0, .sb (18 : Fin 32) (8 : Fin 32) 0x1]

set_option maxRecDepth 100000 in
theorem svX_end : blockEnd sigstoreVerifyCode 0x7A4 svX = some 0x7AE := by decide

/-- What `sigstore::verify` leaves at `out` when it fails with `code`. -/
def svErrMem (M : Word → BitVec 8) (out code : Word) : Word → BitVec 8 :=
  memStore8 (memStore8 M out 1) (out + 1) (code.extractLsb' 0 8)

set_option maxHeartbeats 4000000 in
/-- **The error exit**, from 0x7A4: store `Err` and the code in `s0` at
`out` (in `s2`), and return. -/
theorem sv_err {M : Word → BitVec 8} {n : Machine} {B out : Word} {v : Nat → Word} (C : CodeIn M SV sigstoreVerifyCode)
    (F : Fr B 0x2660) (s : St M SV n 0x7A4 (reg n)) (rsp : reg n sp = B + 0x21A0) (hout : reg n (18 : Fin 32) = out)
    (hS : ∀ k, k < 13 → memLoad32 M (B + BitVec.ofNat 32 (0x265C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0)
    (sOS : Sep out 2 (B + BitVec.ofNat 32 0x262C) 0x34) (sOC : Sep out 2 SV sigstoreVerifyCode.length) :
    ∃ n', Steps n n' ∧ n'.pc = v 0 ∧ n'.mem = svErrMem M out (reg n (8 : Fin 32)) ∧ reg n' sp = B + 0x2660 ∧
      (∀ k, k < 13 → reg n' (savedReg k) = v k) ∧
      reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  have hz := s.zero
  have e0 : out + 0 = out := BitVec.add_zero _
  obtain ⟨n1, c1, u1⟩ := s.block svX C svX_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, svX]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [hout, e0]
    exact ⟨sOC.sub (c := 0) (l := 1) (by decide) |> fun h => by rwa [add_ofNat_zero] at h,
      sOC.sub (c := 1) (l := 1) (by decide)⟩)
  have m1 : (runBlock svX (M, reg n)).1 = svErrMem M out (reg n (8 : Fin 32)) := by
    simp +decide only [runBlock, BInstr.run, svX, upd, ↓reduceIte]; rw [hout, e0]; rfl
  have r1 : ∀ q, q ≠ a0 → (runBlock svX (M, reg n)).2 q = reg n q := fun q hq => by
    simp only [runBlock, BInstr.run, svX]; exact updz hz hq
  have hS' : ∀ k, k < 13 → memLoad32 (svErrMem M out (reg n (8 : Fin 32))) (B + BitVec.ofNat 32 (0x265C - 4 * k)) = v k :=
    fun k hk => by
      rw [← hS k hk]; unfold svErrMem
      have hs : Sep out 2 (B + BitVec.ofNat 32 (0x265C - 4 * k)) 4 := by
        have := sOS.symm.sub (c := 0x30 - 4 * k) (l := 4) (by omega)
        rw [add_ofNat_assoc, show 0x262C + (0x30 - 4 * k) = 0x265C - 4 * k by omega] at this
        exact this.symm
      exact memLoad32_congr fun j hj => by
        have h1 : B + BitVec.ofNat 32 (0x265C - 4 * k) + BitVec.ofNat 32 j ≠ out + 1 := fun e => hs 1 (by decide) j hj e.symm
        have h0 : B + BitVec.ofNat 32 (0x265C - 4 * k) + BitVec.ofNat 32 j ≠ out := fun e =>
          hs 0 (by decide) j hj (by rw [add_ofNat_zero]; exact e.symm)
        rw [memStore8_ne h1, memStore8_ne h0]
  have C1 : CodeIn (svErrMem M out (reg n (8 : Fin 32))) SV sigstoreVerifyCode :=
    (C.store8 (by have := sOC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this)).store8
      (sOC.sub (c := 1) (l := 1) (by decide))
  have s1 : St (svErrMem M out (reg n (8 : Fin 32))) SV n1 0x7AE (reg n1) := ⟨u1.pc, u1.mem.trans m1, fun _ => rfl⟩
  obtain ⟨n2, c2, pc2, mem2, sp2, sv2, g2, t2⟩ := sv_ret (v := v) C1 F s1
    (by rw [u1.regs, r1 sp (by decide), rsp]) hS' hret
  refine ⟨n2, c1.trans c2, pc2, mem2, sp2, sv2, ?_, ?_⟩
  · rw [g2, u1.regs, r1 3 (by decide)]
  · rw [t2, u1.regs, r1 4 (by decide)]

end C3.RV32.Sv
