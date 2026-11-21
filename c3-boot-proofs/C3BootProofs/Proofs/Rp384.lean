import C3BootProofs.Proofs.Fs384Main

/-!
# `read_p384_point`

`c3_verify::trustroot::read_p384_point` reads 97 bytes from a `Reader`, checks
that they start with the uncompressed tag 4, and checks them as a P-384 point
with `VerifyingKey<NistP384>::from_sec1_bytes`. It returns the slice.
-/

namespace C3.RV32.Rp

open C3.Image C3.RV32.Dq C3.RV32.P3 C3.RV32.Fs

set_option maxRecDepth 20000

/-- Where `read_p384_point` is in the image. -/
abbrev RP : Word := BitVec.ofNat 32 readP384PointAddress
abbrev RB : Word := BitVec.ofNat 32 readerBytesAddress

theorem rp_at_0 : fetchRel readP384PointCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF80, 2) := by decide
theorem rp_at_2 : fetchRel readP384PointCode 0x2 = some (.store .sw sp ra 0x7C, 2) := by decide
theorem rp_at_4 : fetchRel readP384PointCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x78, 2) := by decide
theorem rp_at_6 : fetchRel readP384PointCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x74, 2) := by decide
theorem rp_at_8 : fetchRel readP384PointCode 0x8 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem rp_at_a : fetchRel readP384PointCode 0xA = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem rp_at_c : fetchRel readP384PointCode 0xC = some (.aluImm .add a2 x0 0x61, 4) := by decide
theorem rp_at_10 : fetchRel readP384PointCode 0x10 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem rp_at_14 : fetchRel readP384PointCode 0x14 = some (.jalr ra ra 0x3D4, 4) := by decide
theorem rp_at_18 : fetchRel readP384PointCode 0x18 = some (.load .lw (9 : Fin 32) sp 0xC, 2) := by decide
theorem rp_at_1a : fetchRel readP384PointCode 0x1A = some (.branch .beq (9 : Fin 32) x0 0x28, 2) := by decide
theorem rp_at_1c : fetchRel readP384PointCode 0x1C = some (.load .lw a0 sp 0x10, 2) := by decide
theorem rp_at_1e : fetchRel readP384PointCode 0x1E = some (.aluImm .add a0 a0 0xFFFFFF9F, 4) := by decide
theorem rp_at_22 : fetchRel readP384PointCode 0x22 = some (.branch .bne a0 x0 0x26, 2) := by decide
theorem rp_at_24 : fetchRel readP384PointCode 0x24 = some (.load .lbu a0 (9 : Fin 32) 0x0, 4) := by decide
theorem rp_at_28 : fetchRel readP384PointCode 0x28 = some (.aluImm .add a1 x0 0x4, 2) := by decide
theorem rp_at_2a : fetchRel readP384PointCode 0x2A = some (.branch .bne a0 a1 0x14, 4) := by decide
theorem rp_at_2e : fetchRel readP384PointCode 0x2E = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem rp_at_30 : fetchRel readP384PointCode 0x30 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem rp_at_32 : fetchRel readP384PointCode 0x32 = some (.auipc ra 0xFFFF8000, 4) := by decide
theorem rp_at_36 : fetchRel readP384PointCode 0x36 = some (.jalr ra ra 0x24, 4) := by decide
theorem rp_at_3a : fetchRel readP384PointCode 0x3A = some (.load .lw a0 sp 0xC, 2) := by decide
theorem rp_at_3c : fetchRel readP384PointCode 0x3C = some (.branch .beq a0 x0 0x22, 2) := by decide
theorem rp_at_3e : fetchRel readP384PointCode 0x3E = some (.aluImm .add a0 x0 0xE, 2) := by decide
theorem rp_at_40 : fetchRel readP384PointCode 0x40 = some (.jal x0 0xA, 2) := by decide
theorem rp_at_42 : fetchRel readP384PointCode 0x42 = some (.load .lbu a0 sp 0x10, 4) := by decide
theorem rp_at_46 : fetchRel readP384PointCode 0x46 = some (.jal x0 0x4, 2) := by decide
theorem rp_at_48 : fetchRel readP384PointCode 0x48 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem rp_at_4a : fetchRel readP384PointCode 0x4A = some (.store .sb (8 : Fin 32) a0 0x1, 4) := by decide
theorem rp_at_4e : fetchRel readP384PointCode 0x4E = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem rp_at_50 : fetchRel readP384PointCode 0x50 = some (.store .sb (8 : Fin 32) a0 0x0, 4) := by decide
theorem rp_at_54 : fetchRel readP384PointCode 0x54 = some (.load .lw ra sp 0x7C, 2) := by decide
theorem rp_at_56 : fetchRel readP384PointCode 0x56 = some (.load .lw (8 : Fin 32) sp 0x78, 2) := by decide
theorem rp_at_58 : fetchRel readP384PointCode 0x58 = some (.load .lw (9 : Fin 32) sp 0x74, 2) := by decide
theorem rp_at_5a : fetchRel readP384PointCode 0x5A = some (.aluImm .add sp sp 0x80, 2) := by decide
theorem rp_at_5c : fetchRel readP384PointCode 0x5C = some (.jalr x0 ra 0x0, 2) := by decide
theorem rp_at_5e : fetchRel readP384PointCode 0x5E = some (.store .sw (8 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem rp_at_60 : fetchRel readP384PointCode 0x60 = some (.jal x0 0xFFFFFFF0, 2) := by decide

/-- `read_p384_point`'s code and its callees'. -/
structure RpCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M RP readP384PointCode
  rb : CodeIn M RB readerBytesCode
  fs : FsCode M

theorem RpCode.hi {M M' : Word → BitVec 8} (C : RpCode M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    RpCode M' := ⟨codeHi C.self (by decide) (by decide) h, codeHi C.rb (by decide) (by decide) h, C.fs.hi h⟩

theorem _root_.C3.RV32.P3.Fr.shrink {S : Word} {N N' : Nat} (F : Fr S N) (h : N' ≤ N) : Fr S N' :=
  ⟨F.al, F.lo, by have := F.hi; omega, F.dsep.sub (c := 0) (l := N' + 0x1A0) (by omega) |> fun h => by
    rwa [add_ofNat_zero] at h⟩

/-- A call to `from_sec1_bytes` with its frame at `S`. -/
theorem c_fs {base : Word} {code : List Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word}
    {imm o S out inp : Word} (s : St Mx base n off g) (hcd : CodeIn Mx base code) (C : FsCode Mx) (D : P3Data Mx)
    (F : Fr S 0x420) (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = FP) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S + 0x420) (ha0 : g a0 = out) (ha1 : g a1 = inp)
    (sI : Sep inp 0x61 (S + 0xFFFFFE60) 0x5C0) (hI : inp.toNat + 0x61 ≤ 0x40000000)
    (hoa : out.toNat % 4 = 0) (hO : out.toNat + 0x68 ≤ 0x40000000) (sO : Sep out 0x68 (S + 0xFFFFFE60) 0x5C0) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧ reg n' sp = S + 0x420 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q) ∧
      (∀ x, Sep (S + 0xFFFFFE60) 0x5C0 x 1 → Sep out 0x68 x 1 → n'.mem x = Mx x) ∧
      (FsOk Mx inp → memLoad32 n'.mem out = 0) ∧ (¬ FsOk Mx inp → memLoad32 n'.mem out = 1) := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, ⟨pc2, sp2, sv2, k2, fr2⟩, ok2, bad2⟩ := p384FromSec1_correct n1 (by rw [mem1]; exact C)
    (by rw [mem1]; exact D) F pc1 (by rw [r1 sp (by decide)]; exact hsp) (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide only [upd, ↓reduceIte]; exact even_clear _ he8)
    sI hI hoa hO sO
  rw [mem1] at ok2 bad2 fr2
  have pcr : reg n1 ra = base + BitVec.ofNat 32 (off + 8) := by rw [regs1]; simp +decide only [upd, ↓reduceIte]
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2, pcr], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_, fr2,
    fun h => (ok2 h).1, bad2⟩
  match q, hq with
  | 3, _ => rw [k2 3 (by decide), r1 3 (by decide)]
  | 4, _ => rw [k2 4 (by decide), r1 4 (by decide)]
  | 26, _ => rw [k2 26 (by decide), r1 26 (by decide)]
  | 27, _ => rw [k2 27 (by decide), r1 27 (by decide)]
  | 8, _ => exact (sv2 1 (by decide)).trans (r1 8 (by decide))
  | 9, _ => exact (sv2 2 (by decide)).trans (r1 9 (by decide))
  | 18, _ => exact (sv2 3 (by decide)).trans (r1 18 (by decide))
  | 19, _ => exact (sv2 4 (by decide)).trans (r1 19 (by decide))
  | 20, _ => exact (sv2 5 (by decide)).trans (r1 20 (by decide))
  | 21, _ => exact (sv2 6 (by decide)).trans (r1 21 (by decide))
  | 22, _ => exact (sv2 7 (by decide)).trans (r1 22 (by decide))
  | 23, _ => exact (sv2 8 (by decide)).trans (r1 23 (by decide))
  | 24, _ => exact (sv2 9 (by decide)).trans (r1 24 (by decide))
  | 25, _ => exact (sv2 10 (by decide)).trans (r1 25 (by decide))

def rpA : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFF80, .sw sp ra 0x7C, .sw sp (8 : Fin 32) 0x78, .sw sp (9 : Fin 32) 0x74,
   .alu .add (8 : Fin 32) x0 a0, .aluImm .add a0 sp 0xC, .aluImm .add a2 x0 0x61]
def rpL : List BInstr := [.lw (9 : Fin 32) sp 0xC]
def rpN : List BInstr := [.lw a0 sp 0x10, .aluImm .add a0 a0 0xFFFFFF9F]
def rpT : List BInstr := [.lbu a0 (9 : Fin 32) 0x0, .aluImm .add a1 x0 0x4]
def rpC : List BInstr := [.aluImm .add a0 sp 0xC, .alu .add a1 x0 (9 : Fin 32)]
def rpR : List BInstr := [.lw a0 sp 0xC]
def rpE : List BInstr := [.aluImm .add a0 x0 0xE]
def rpZ : List BInstr := [.lbu a0 sp 0x10]
def rpO : List BInstr := [.sw (8 : Fin 32) (9 : Fin 32) 0x4]
def rpE1 : List BInstr :=
  [.sb (8 : Fin 32) a0 0x1, .aluImm .add a0 x0 0x1, .sb (8 : Fin 32) a0 0x0, .lw ra sp 0x7C, .lw (8 : Fin 32) sp 0x78,
   .lw (9 : Fin 32) sp 0x74, .aluImm .add sp sp 0x80]
def rpE2 : List BInstr :=
  [.sb (8 : Fin 32) a0 0x0, .lw ra sp 0x7C, .lw (8 : Fin 32) sp 0x78, .lw (9 : Fin 32) sp 0x74, .aluImm .add sp sp 0x80]
theorem rpA_end : blockEnd readP384PointCode 0 rpA = some 0x10 := by decide
theorem rpL_end : blockEnd readP384PointCode 0x18 rpL = some 0x1A := by decide
theorem rpN_end : blockEnd readP384PointCode 0x1C rpN = some 0x22 := by decide
theorem rpT_end : blockEnd readP384PointCode 0x24 rpT = some 0x2A := by decide
theorem rpC_end : blockEnd readP384PointCode 0x2E rpC = some 0x32 := by decide
theorem rpR_end : blockEnd readP384PointCode 0x3A rpR = some 0x3C := by decide
theorem rpE_end : blockEnd readP384PointCode 0x3E rpE = some 0x40 := by decide
theorem rpZ_end : blockEnd readP384PointCode 0x42 rpZ = some 0x46 := by decide
theorem rpO_end : blockEnd readP384PointCode 0x5E rpO = some 0x60 := by decide
theorem rpE1_end : blockEnd readP384PointCode 0x4A rpE1 = some 0x5C := by decide
theorem rpE2_end : blockEnd readP384PointCode 0x50 rpE2 = some 0x5C := by decide

/-- What `read_p384_point` stores at `out` for the reader at `self` in `M`:
`Ok` and the slice when `Reader::bytes` gives 97 bytes that `from_sec1_bytes`
accepts; `Err` with code 0 when the reader runs out, or 0xE otherwise. -/
def RpOut (M : Word → BitVec 8) (self : Word) (M' : Word → BitVec 8) (out : Word) : Prop :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 0x61 with
  | none => M' out = 1 ∧ M' (out + 1) = 0 ∧ memLoad32 M' (self + 8) = memLoad32 M (self + 8)
  | some (p, e) => memLoad32 M' (self + 8) = e ∧
      (if FsOk M p then M' out = 0 ∧ memLoad32 M' (out + 4) = p else M' out = 1 ∧ M' (out + 1) = 0xE)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The error return, from 0x4A with the code in `a0`. -/
theorem rp_epi1 {Mx : Word → BitVec 8} {nx : Machine} {S out v w0 w1 w2 : Word} (C : RpCode Mx)
    (s : St Mx RP nx 0x4A (reg nx)) (rsp : reg nx sp = S) (r8 : reg nx (8 : Fin 32) = out) (ra0 : reg nx a0 = v)
    (hS : S.toNat % 4 = 0) (hSh : S.toNat + 0x80 ≤ 0x40000000) (hO : out.toNat + 8 ≤ 0x40000000)
    (sOS : Sep out 2 (S + BitVec.ofNat 32 0x74) 12)
    (h0 : memLoad32 Mx (S + BitVec.ofNat 32 0x7C) = w0) (h1 : memLoad32 Mx (S + BitVec.ofNat 32 0x78) = w1)
    (h2 : memLoad32 Mx (S + BitVec.ofNat 32 0x74) = w2) (hret : w0 &&& ~~~1 = w0) :
    ∃ n', Steps nx n' ∧ n'.pc = w0 ∧ reg n' sp = S + 0x80 ∧ reg n' ra = w0 ∧ reg n' (8 : Fin 32) = w1 ∧
      reg n' (9 : Fin 32) = w2 ∧ (∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg nx q) ∧
      n'.mem = memStore8 (memStore8 Mx (out + 1) (v.extractLsb' 0 8)) out 1 := by
  have hz := s.zero
  have hc : ∀ c, c + 4 ≤ 0x80 → (S + BitVec.ofNat 32 c).toNat = S.toNat + c := fun c h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have oc : ∀ c, c ≤ 8 → (out + BitVec.ofNat 32 c).toNat = out.toNat + c := fun c h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hRP : 0x40000000 ≤ RP.toNat := by decide
  have sOne : Sep (out + 1) 1 RP readP384PointCode.length :=
    sep_of_le (by rw [show (out + 1 : Word) = out + BitVec.ofNat 32 1 from rfl, oc 1 (by decide)]; omega) (by decide)
  have sOut : Sep (out + 0) 1 RP readP384PointCode.length :=
    sep_of_le (by rw [show (out + 0 : Word) = out + BitVec.ofNat 32 0 from rfl, oc 0 (by decide)]; omega) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block rpE1 C.self rpE1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, rpE1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [r8, rsp]
    exact ⟨sOne, sOut, by show (S + BitVec.ofNat 32 0x7C).toNat % 4 = 0; rw [hc _ (by decide)]; omega,
      by show (S + BitVec.ofNat 32 0x78).toNat % 4 = 0; rw [hc _ (by decide)]; omega,
      by show (S + BitVec.ofNat 32 0x74).toNat % 4 = 0; rw [hc _ (by decide)]; omega⟩)
  have o0 : out + (0 : Word) = out := BitVec.add_zero out
  have e1 : (BitVec.extractLsb' 0 8 (aluEval AluOp.add (0 : Word) 1)) = (1 : BitVec 8) := rfl
  have mm : (runBlock rpE1 (Mx, reg nx)).1 = memStore8 (memStore8 Mx (out + 1) (v.extractLsb' 0 8)) out 1 := by
    simp only [runBlock, BInstr.run, rpE1]; simp +decide only [upd, ↓reduceIte]; rw [r8, ra0, o0, hz, e1]
  have ld : ∀ c, 0x74 ≤ c → c + 4 ≤ 0x80 → memLoad32 (memStore8 (memStore8 Mx (out + 1) (v.extractLsb' 0 8)) out 1)
      (S + BitVec.ofNat 32 c) = memLoad32 Mx (S + BitVec.ofNat 32 c) := fun c h1 h2 => by
    have hs : Sep out 2 (S + BitVec.ofNat 32 c) 4 := by
      have := sOS.subR (c := c - 0x74) (l := 4) (by omega); rwa [add_ofNat_assoc, show 0x74 + (c - 0x74) = c by omega] at this
    rw [memLoad32_store8_sep ((hs.sub (c := 0) (l := 1) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h),
      memLoad32_store8_sep (show Sep (out + 1) 1 (S + BitVec.ofNat 32 c) 4 from hs.sub (c := 1) (l := 1) (by decide))]
  have C1 : RpCode (runBlock rpE1 (Mx, reg nx)).1 := by
    rw [mm]; exact C.hi fun x hx => by
      rw [dq_st8 (sep_of_le (by omega) (by have := x.isLt; omega)),
        dq_st8 (sep_of_le (by rw [show (out + 1 : Word) = out + BitVec.ofNat 32 1 from rfl, oc 1 (by decide)]; omega)
          (by have := x.isLt; omega))]
  obtain ⟨n2, st2, pc2, mem2, regs2⟩ := u1.jalr C1.self rp_at_5c
  refine ⟨n2, c1.trans (.single st2), ?_, ?_, ?_, ?_, ?_, fun q hq => ?_, by rw [mem2, mm]⟩
  · rw [pc2]; simp +decide only [runBlock, BInstr.run, rpE1, upd, ↓reduceIte]; rw [rsp, r8, ra0, o0, hz, e1]
    show memLoad32 _ (S + BitVec.ofNat 32 0x7C) + 0 &&& ~~~1 = w0
    rw [ld _ (by decide) (by decide), h0, show w0 + (0 : Word) = w0 from BitVec.add_zero w0]; exact hret
  · rw [regs2]; simp +decide only [runBlock, BInstr.run, rpE1, upd, ↓reduceIte]; rw [rsp]; rfl
  · rw [regs2]; simp +decide only [runBlock, BInstr.run, rpE1, upd, ↓reduceIte]; rw [rsp, r8, ra0, o0, hz, e1]
    show memLoad32 _ (S + BitVec.ofNat 32 0x7C) = w0; rw [ld _ (by decide) (by decide), h0]
  · rw [regs2]; simp +decide only [runBlock, BInstr.run, rpE1, upd, ↓reduceIte]; rw [rsp, r8, ra0, o0, hz, e1]
    show memLoad32 _ (S + BitVec.ofNat 32 0x78) = w1; rw [ld _ (by decide) (by decide), h1]
  · rw [regs2]; simp +decide only [runBlock, BInstr.run, rpE1, upd, ↓reduceIte]; rw [rsp, r8, ra0, o0, hz, e1]
    show memLoad32 _ (S + BitVec.ofNat 32 0x74) = w2; rw [ld _ (by decide) (by decide), h2]
  · rw [regs2, runBlock_reg _ _ _ q hz (by simp only [rpE1]; revert hq; revert q; decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The return from 0x50, with the result byte in `a0`. -/
theorem rp_epi2 {Mx : Word → BitVec 8} {nx : Machine} {S out v w0 w1 w2 : Word} (C : RpCode Mx)
    (s : St Mx RP nx 0x50 (reg nx)) (rsp : reg nx sp = S) (r8 : reg nx (8 : Fin 32) = out) (ra0 : reg nx a0 = v)
    (hS : S.toNat % 4 = 0) (hSh : S.toNat + 0x80 ≤ 0x40000000) (hO : out.toNat + 8 ≤ 0x40000000)
    (sOS : Sep out 2 (S + BitVec.ofNat 32 0x74) 12)
    (h0 : memLoad32 Mx (S + BitVec.ofNat 32 0x7C) = w0) (h1 : memLoad32 Mx (S + BitVec.ofNat 32 0x78) = w1)
    (h2 : memLoad32 Mx (S + BitVec.ofNat 32 0x74) = w2) (hret : w0 &&& ~~~1 = w0) :
    ∃ n', Steps nx n' ∧ n'.pc = w0 ∧ reg n' sp = S + 0x80 ∧ reg n' ra = w0 ∧ reg n' (8 : Fin 32) = w1 ∧
      reg n' (9 : Fin 32) = w2 ∧ (∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg nx q) ∧
      n'.mem = memStore8 Mx out (v.extractLsb' 0 8) := by
  have hz := s.zero
  have hc : ∀ c, c + 4 ≤ 0x80 → (S + BitVec.ofNat 32 c).toNat = S.toNat + c := fun c h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have oc : ∀ c, c ≤ 8 → (out + BitVec.ofNat 32 c).toNat = out.toNat + c := fun c h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hRP : 0x40000000 ≤ RP.toNat := by decide
  have sOne : Sep (out + 1) 1 RP readP384PointCode.length :=
    sep_of_le (by rw [show (out + 1 : Word) = out + BitVec.ofNat 32 1 from rfl, oc 1 (by decide)]; omega) (by decide)
  have sOut : Sep (out + 0) 1 RP readP384PointCode.length :=
    sep_of_le (by rw [show (out + 0 : Word) = out + BitVec.ofNat 32 0 from rfl, oc 0 (by decide)]; omega) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block rpE2 C.self rpE2_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, rpE2]; simp +decide only [upd, ↓reduceIte, and_true]
    rw [r8, rsp]
    exact ⟨sOut, by show (S + BitVec.ofNat 32 0x7C).toNat % 4 = 0; rw [hc _ (by decide)]; omega,
      by show (S + BitVec.ofNat 32 0x78).toNat % 4 = 0; rw [hc _ (by decide)]; omega,
      by show (S + BitVec.ofNat 32 0x74).toNat % 4 = 0; rw [hc _ (by decide)]; omega⟩)
  have o0 : out + (0 : Word) = out := BitVec.add_zero out
  have e1 : (BitVec.extractLsb' 0 8 (aluEval AluOp.add (0 : Word) 1)) = (1 : BitVec 8) := rfl
  have mm : (runBlock rpE2 (Mx, reg nx)).1 = memStore8 Mx out (v.extractLsb' 0 8) := by
    simp only [runBlock, BInstr.run, rpE2]; rw [r8, ra0, o0]
  have ld : ∀ c, 0x74 ≤ c → c + 4 ≤ 0x80 → memLoad32 (memStore8 Mx out (v.extractLsb' 0 8))
      (S + BitVec.ofNat 32 c) = memLoad32 Mx (S + BitVec.ofNat 32 c) := fun c h1 h2 => by
    have hs : Sep out 2 (S + BitVec.ofNat 32 c) 4 := by
      have := sOS.subR (c := c - 0x74) (l := 4) (by omega); rwa [add_ofNat_assoc, show 0x74 + (c - 0x74) = c by omega] at this
    rw [memLoad32_store8_sep ((hs.sub (c := 0) (l := 1) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h)]
  have C1 : RpCode (runBlock rpE2 (Mx, reg nx)).1 := by
    rw [mm]; exact C.hi fun x hx => by
      rw [dq_st8 (sep_of_le (by omega) (by have := x.isLt; omega))]
  obtain ⟨n2, st2, pc2, mem2, regs2⟩ := u1.jalr C1.self rp_at_5c
  refine ⟨n2, c1.trans (.single st2), ?_, ?_, ?_, ?_, ?_, fun q hq => ?_, by rw [mem2, mm]⟩
  · rw [pc2]; simp +decide only [runBlock, BInstr.run, rpE2, upd, ↓reduceIte]; rw [rsp, r8, ra0, o0]
    show memLoad32 _ (S + BitVec.ofNat 32 0x7C) + 0 &&& ~~~1 = w0
    rw [ld _ (by decide) (by decide), h0, show w0 + (0 : Word) = w0 from BitVec.add_zero w0]; exact hret
  · rw [regs2]; simp +decide only [runBlock, BInstr.run, rpE2, upd, ↓reduceIte]; rw [rsp]; rfl
  · rw [regs2]; simp +decide only [runBlock, BInstr.run, rpE2, upd, ↓reduceIte]; rw [rsp, r8, ra0, o0]
    show memLoad32 _ (S + BitVec.ofNat 32 0x7C) = w0; rw [ld _ (by decide) (by decide), h0]
  · rw [regs2]; simp +decide only [runBlock, BInstr.run, rpE2, upd, ↓reduceIte]; rw [rsp, r8, ra0, o0]
    show memLoad32 _ (S + BitVec.ofNat 32 0x78) = w1; rw [ld _ (by decide) (by decide), h1]
  · rw [regs2]; simp +decide only [runBlock, BInstr.run, rpE2, upd, ↓reduceIte]; rw [rsp, r8, ra0, o0]
    show memLoad32 _ (S + BitVec.ofNat 32 0x74) = w2; rw [ld _ (by decide) (by decide), h2]
  · rw [regs2, runBlock_reg _ _ _ q hz (by simp only [rpE2]; revert hq; revert q; decide)]

theorem fsOk_congr {M M' : Word → BitVec 8} {p : Word} (h : ∀ j, j < 0x61 → M' (p + BitVec.ofNat 32 j) = M (p + BitVec.ofNat 32 j)) :
    FsOk M' p ↔ FsOk M p := by
  have v : ∀ o, o + 48 ≤ 0x61 → fsVal M' p o = fsVal M p o := fun o ho => by
    unfold fsVal
    exact congrArg beNat (memBytes_eq fun i hi => by rw [add_ofNat_assoc]; exact h _ (by omega))
  have h0 : M' p = M p := by have := h 0 (by decide); rwa [add_ofNat_zero] at this
  unfold FsOk; rw [h0, v 1 (by decide), v 0x31 (by decide)]

/-- The constants survive changes to memory apart from them. -/
theorem _root_.C3.RV32.P3.P3Data.ofR {M M' : Word → BitVec 8} (D : P3Data M)
    (h : ∀ i, i < 0xC60 → M' ((0x3FCC4200 : Word) + BitVec.ofNat 32 i) = M ((0x3FCC4200 : Word) + BitVec.ofNat 32 i)) :
    P3Data M' := by
  have cd : ∀ (b : Word) (d : List Nat), CodeIn M b d → 0x3FCC4200 ≤ b.toNat → b.toNat + d.length ≤ 0x3FCC4E60 →
      CodeIn M' b d := fun b d hc h1 h2 i hi => by
    have e : b + BitVec.ofNat 32 i = (0x3FCC4200 : Word) + BitVec.ofNat 32 (b.toNat - 0x3FCC4200 + i) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show (0x3FCC4200 : Word).toNat = 0x3FCC4200 from rfl]
      omega
    rw [e, h _ (by omega), ← e]
    exact hc i hi
  exact ⟨cd _ _ D.params (by decide) (by decide), cd _ _ D.ca (by decide) (by decide), cd _ _ D.cb (by decide) (by decide)⟩

/-- The prologue's saves of `ra`, `s0`, and `s1`. -/
def rpSaves (M : Word → BitVec 8) (S : Word) (n : Machine) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 M (S + BitVec.ofNat 32 0x49C) (reg n ra)) (S + BitVec.ofNat 32 0x498)
    (reg n (8 : Fin 32))) (S + BitVec.ofNat 32 0x494) (reg n (9 : Fin 32))

theorem rpSaves_out {M : Word → BitVec 8} {S : Word} {n : Machine} {x : Word}
    (h : Sep (S + BitVec.ofNat 32 0x494) 12 x 1) : rpSaves M S n x = M x := by
  have hs : ∀ c, 0x494 ≤ c → c + 4 ≤ 0x4A0 → Sep (S + BitVec.ofNat 32 c) 4 x 1 := fun c h1 h2 => by
    have := h.sub (c := c - 0x494) (l := 4) (by omega)
    rwa [add_ofNat_assoc, show 0x494 + (c - 0x494) = c by omega] at this
  unfold rpSaves
  rw [memStore32_get_sep (hs 0x494 (by decide) (by decide)), memStore32_get_sep (hs 0x498 (by decide) (by decide)),
    memStore32_get_sep (hs 0x49C (by decide) (by decide))]

theorem rp_tail {Mx : Word → BitVec 8} {nx : Machine} {S out w0 w1 w2 : Word} (C : RpCode Mx)
    (s : St Mx RP nx 0x3E (reg nx)) (rsp : reg nx sp = S) (r8 : reg nx (8 : Fin 32) = out)
    (hS : S.toNat % 4 = 0) (hSh : S.toNat + 0x80 ≤ 0x40000000) (hO : out.toNat + 8 ≤ 0x40000000)
    (sOS : Sep out 2 (S + BitVec.ofNat 32 0x74) 12)
    (h0 : memLoad32 Mx (S + BitVec.ofNat 32 0x7C) = w0) (h1 : memLoad32 Mx (S + BitVec.ofNat 32 0x78) = w1)
    (h2 : memLoad32 Mx (S + BitVec.ofNat 32 0x74) = w2) (hret : w0 &&& ~~~1 = w0) :
    ∃ n', Steps nx n' ∧ n'.pc = w0 ∧ reg n' sp = S + 0x80 ∧ reg n' ra = w0 ∧ reg n' (8 : Fin 32) = w1 ∧
      reg n' (9 : Fin 32) = w2 ∧ (∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg nx q) ∧
      n'.mem = memStore8 (memStore8 Mx (out + 1) 0xE) out 1 := by
  obtain ⟨n1, c1, u1⟩ := s.block rpE C.self rpE_end ⟨trivial, trivial⟩
  have r1 : ∀ q, q ≠ a0 → reg n1 q = reg nx q := fun q hq => by
    rw [u1.regs]; simp only [runBlock, BInstr.run, rpE]; exact updz s.zero hq
  obtain ⟨n2, d2, u2⟩ := u1.self.jump C.self rp_at_40 (off' := 0x4A) (by decide) (by rw [u1.pc]; decide)
  obtain ⟨n3, c3, pc3, sp3, ra3, s03, s13, k3, m3⟩ := rp_epi1 (v := 0xE) C u2.self
    (by rw [u2.regs, r1 sp (by decide)]; exact rsp) (by rw [u2.regs, r1 8 (by decide)]; exact r8)
    (by rw [u2.regs, u1.regs]; simp +decide only [runBlock, BInstr.run, rpE, upd, ↓reduceIte]; (try rw [s.zero]); try rfl)
    hS hSh hO sOS h0 h1 h2 hret
  exact ⟨n3, c1.trans (.cons d2 c3), pc3, sp3, ra3, s03, s13,
    fun q hq => by rw [k3 q hq, u2.regs, r1 q (by revert hq; revert q; decide)], by rw [m3]; rfl⟩

theorem rpSaves_read {M : Word → BitVec 8} {S : Word} {n : Machine} :
    memLoad32 (rpSaves M S n) (S + BitVec.ofNat 32 0x49C) = reg n ra ∧
    memLoad32 (rpSaves M S n) (S + BitVec.ofNat 32 0x498) = reg n (8 : Fin 32) ∧
    memLoad32 (rpSaves M S n) (S + BitVec.ofNat 32 0x494) = reg n (9 : Fin 32) := by
  unfold rpSaves
  refine ⟨?_, ?_, ?_⟩
  · rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide),
      ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide),
      ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]
  · rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide),
      ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]
  · rw [ld_st_frame (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **The compiled `read_p384_point`**, for a reader at `self` over a buffer
apart from the frame, `out`, and the reader's position: it stores `RpOut` at
`out`, advances the reader past the 97 bytes when there are enough, and
returns with `ra`, `s0`, `s1`, and the other callee-saved registers as they
were. -/
theorem readP384Point_correct (m : Machine) {S out self : Word} (C : RpCode m.mem) (D : P3Data m.mem) (F : Fr S 0x4A0)
    (hpc : m.pc = RP) (hsp : reg m sp = S + 0x4A0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = self)
    (hret : reg m ra &&& ~~~1 = reg m ra) (hoa : out.toNat % 4 = 0) (hO : out.toNat + 8 ≤ 0x40000000)
    (sO : Sep out 8 (S + 0xFFFFFE60) 0x640) (hsa : self.toNat % 4 = 0) (hSf : self.toNat + 12 ≤ 0x40000000)
    (sS : Sep self 12 (S + 0xFFFFFE60) 0x640) (sOS : Sep out 8 self 12)
    (hp0 : 0 < (memLoad32 m.mem self).toNat)
    (hbuf : (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 0x40000000)
    (sB : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (S + 0xFFFFFE60) 0x640)
    (sBO : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat out 8)
    (sBS : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (self + 8) 4)
    (sSD : Sep self 12 (0x3FCC4200 : Word) 0xC60) :
    ∃ m', Steps m m' ∧ m'.pc = reg m ra ∧ reg m' sp = S + 0x4A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ x, Sep (S + 0xFFFFFE60) 0x640 x 1 → Sep out 8 x 1 → Sep (self + 8) 4 x 1 → m'.mem x = m.mem x) ∧
      RpOut m.mem self m'.mem out := by
  have hz := (⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩ : St m.mem RP m 0 (reg m)).zero
  have s0 : St m.mem RP m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have F' : Fr S 0x420 := F.shrink (by decide)
  have hS' : aluEval .add (S + 0x4A0) 0xFFFFFF80 = S + BitVec.ofNat 32 0x420 := by
    show S + 0x4A0 + 0xFFFFFF80 = _; rw [BitVec.add_assoc]; rfl
  have fa : ∀ c, c ≤ 0x4A0 → (S + BitVec.ofNat 32 c).toNat = S.toNat + c := fun c h => F.at c h
  have lit : ∀ (c : Nat) (k : Word), c + k.toNat < 2 ^ 32 → S + BitVec.ofNat 32 c + k = S + BitVec.ofNat 32 (c + k.toNat) :=
    fun c k h => frame_lit k h
  -- the prologue
  obtain ⟨n1, c1, u1⟩ := s0.block rpA C.self rpA_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, rpA]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [hsp, hS']
    simp (disch := decide) only [lit]
    simp only [show ((0x7C : Word).toNat) = 0x7C from rfl, show ((0x78 : Word).toNat) = 0x78 from rfl,
      show ((0x74 : Word).toNat) = 0x74 from rfl]
    exact ⟨⟨by rw [fa _ (by decide)]; omega, F.sepHi (by decide) (by decide) (by decide)⟩,
      ⟨by rw [fa _ (by decide)]; omega, F.sepHi (by decide) (by decide) (by decide)⟩,
      ⟨by rw [fa _ (by decide)]; omega, F.sepHi (by decide) (by decide) (by decide)⟩⟩)
  have m1 : n1.mem = rpSaves m.mem S m := by
    rw [u1.mem]; simp only [runBlock, BInstr.run, rpA]; simp +decide only [upd, ↓reduceIte]
    rw [hsp, hS']; simp (disch := decide) only [lit]; rfl
  have r1 : ∀ q, reg n1 q = (runBlock rpA (m.mem, reg m)).2 q := fun q => by rw [u1.regs]
  have sp1 : reg n1 sp = S + BitVec.ofNat 32 0x420 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, rpA, upd, ↓reduceIte]; rw [hsp, hS']
  have hsv : ∀ x, Sep (S + BitVec.ofNat 32 0x494) 12 x 1 → rpSaves m.mem S m x = m.mem x := fun x h => rpSaves_out h
  have fIn : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x4A0 → Sep (S + 0xFFFFFE60) 0x640 x 1 → Sep (S + BitVec.ofNat 32 c) l x 1 :=
    fun h hx => fr_inFrame (N := 0x4A0) h hx
  have C1 : RpCode (rpSaves m.mem S m) := C.hi fun x hx => hsv x (F.hiOut (by decide) hx)
  -- Reader::bytes
  have t1 : St (rpSaves m.mem S m) RP n1 0x10 (reg n1) := ⟨u1.pc, m1, fun _ => rfl⟩
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := t1.callRa (cb := RB) C1.self rp_at_10 rp_at_14 (by decide) (by decide)
  have r2 : ∀ r, r ≠ ra → reg n2 r = reg n1 r := fun r h => by rw [regs2]; exact updz t1.zero h
  have e1 : ∀ q : Fin 32, q.val ∈ [3, 4, 9, 11, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n1 q = reg m q := fun q hq => by
    rw [r1, runBlock_reg _ _ _ q hz (by simp only [rpA]; revert hq; revert q; decide)]
  have hRBc : 0x40000000 ≤ RB.toNat := by decide
  obtain ⟨n3, c3, pc3, mem3, fr3⟩ := readerBytes_correct n2 RB (RP + BitVec.ofNat 32 0x18) (S + BitVec.ofNat 32 0x42C) self
    0x61 (fun i hi => by rw [mem2]; exact C1.rb i hi) pc2
    (by rw [r2 a0 (by decide), r1]; simp +decide only [runBlock, BInstr.run, rpA, upd, ↓reduceIte]; rw [hsp, hS']
        show S + BitVec.ofNat 32 0x420 + 0xC = _; rw [BitVec.add_assoc]; rfl)
    (by rw [r2 a1 (by decide), e1 a1 (by decide)]; exact ha1)
    (by rw [r2 a2 (by decide), r1]; simp +decide only [runBlock, BInstr.run, rpA, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    (by rw [regs2]; simp +decide only [upd, ↓reduceIte]) (even_clear _ (by decide))
    (by rw [fa _ (by decide)]; omega) hsa (F.sepHi (by decide) (by decide) (by decide))
    (sep_of_le (by rw [BitVec.toNat_add, show (8 : Word).toNat = 8 from rfl]; omega) (by decide))
  rw [mem2] at mem3
  have t3 : St n3.mem RP n3 0x18 (reg n3) := ⟨pc3, rfl, fun _ => rfl⟩
  have r3 : ∀ q, q ≠ a3 → q ≠ a4 → q ≠ a5 → reg n3 q = reg n2 q := fr3
  have K3 : ∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg m q := fun q hq => by
    rw [r3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      r2 q (by revert hq; revert q; decide), e1 q (by revert hq; revert q; decide)]
  have sp3 : reg n3 sp = S + BitVec.ofNat 32 0x420 := by
    rw [r3 sp (by decide) (by decide) (by decide), r2 sp (by decide)]; exact sp1
  have e38 : reg n3 (8 : Fin 32) = out := by
    rw [r3 8 (by decide) (by decide) (by decide), r2 8 (by decide), r1]
    simp +decide only [runBlock, BInstr.run, rpA, upd, ↓reduceIte]; rw [ha0]; exact BitVec.zero_add _
  -- the reader's words survive the saves
  have sSv : ∀ c, c < 12 → Sep (S + BitVec.ofNat 32 0x494) 12 (self + BitVec.ofNat 32 c) 1 := fun c hc =>
    fIn (by decide) ((sS.sub (c := c) (l := 1) (by omega)).symm)
  have rw0 : ∀ c, c + 4 ≤ 12 → memLoad32 (rpSaves m.mem S m) (self + BitVec.ofNat 32 c) = memLoad32 m.mem (self + BitVec.ofNat 32 c) :=
    fun c hc => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hsv _ (sSv _ (by omega))
  have hBR : bytesResult (memLoad32 (rpSaves m.mem S m) self) (memLoad32 (rpSaves m.mem S m) (self + 4))
      (memLoad32 (rpSaves m.mem S m) (self + 8)) 0x61 =
      bytesResult (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)) (memLoad32 m.mem (self + 8)) 0x61 := by
    have a := rw0 0 (by decide); rw [add_ofNat_zero] at a
    rw [a, show self + 4 = self + BitVec.ofNat 32 4 from rfl, rw0 4 (by decide),
      show self + 8 = self + BitVec.ofNat 32 8 from rfl, rw0 8 (by decide)]
  have hsvS : ∀ k, 0x494 ≤ k → k + 4 ≤ 0x4A0 → memLoad32 (rpSaves m.mem S m) (S + BitVec.ofNat 32 k) =
      memLoad32 (rpSaves m.mem S m) (S + BitVec.ofNat 32 k) := fun _ _ _ => rfl
  have hb1A : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have sv := rpSaves_read (M := m.mem) (S := S) (n := m)
  -- facts every return needs
  have o2 : Sep out 2 (S + BitVec.ofNat 32 0x420 + BitVec.ofNat 32 0x74) 12 := by
    rw [add_ofNat_assoc]
    have := (sO.sub (c := 0) (l := 2) (by decide)).subR (c := 0x1A0 + 0x494) (l := 12) (by decide)
    rwa [add_ofNat_zero, BitVec.add_assoc,
      show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x494) = BitVec.ofNat 32 0x494 from rfl] at this
  have hS4 : (S + BitVec.ofNat 32 0x420).toNat % 4 = 0 := by rw [fa _ (by decide)]; omega
  have hS8 : (S + BitVec.ofNat 32 0x420).toNat + 0x80 ≤ 0x40000000 := by rw [fa _ (by decide)]; omega
  have spF : S + BitVec.ofNat 32 0x420 + 0x80 = S + 0x4A0 := by rw [BitVec.add_assoc]; rfl
  have a74 : ∀ c, S + BitVec.ofNat 32 0x420 + BitVec.ofNat 32 c = S + BitVec.ofNat 32 (0x420 + c) := fun c => add_ofNat_assoc _ _ _
  -- the stack slot of the result, apart from everything outside the frame
  have sF : ∀ {x : Word}, Sep (S + 0xFFFFFE60) 0x640 x 1 → Sep (S + BitVec.ofNat 32 0x42C) 8 x 1 := fun hx => fIn (by decide) hx
  have sSav : ∀ {x : Word}, Sep (S + 0xFFFFFE60) 0x640 x 1 → Sep (S + BitVec.ofNat 32 0x494) 12 x 1 := fun hx => fIn (by decide) hx
  have nO : ∀ {x : Word}, Sep out 8 x 1 → Sep out 1 x 1 ∧ Sep (out + 1) 1 x 1 := fun hx =>
    ⟨(hx.sub (c := 0) (l := 1) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h,
     show Sep (out + 1) 1 _ 1 from hx.sub (c := 1) (l := 1) (by decide)⟩
  have C3 : RpCode n3.mem := C1.hi fun x hx => by
    rw [mem3, bytesMem_outside (F.hiOut (by decide) hx)]
    rcases bytesResult (memLoad32 (rpSaves m.mem S m) self) (memLoad32 (rpSaves m.mem S m) (self + 4))
      (memLoad32 (rpSaves m.mem S m) (self + 8)) 0x61 with _ | ⟨q, e'⟩
    · rfl
    · exact memStore32_get_sep (sep_of_le (by rw [BitVec.toNat_add, show (8 : Word).toNat = 8 from rfl]; omega)
        (by have := x.isLt; omega))
  obtain ⟨n4, c4, u4⟩ := t3.block rpL C3.self rpL_end (by
    simp only [BlockOk, BInstr.ok, rpL]; simp +decide only [and_true]
    rw [sp3]; show (S + BitVec.ofNat 32 0x420 + 0xC).toNat % 4 = 0
    rw [BitVec.add_assoc, show (BitVec.ofNat 32 0x420 + 0xC : Word) = BitVec.ofNat 32 0x42C from rfl, fa _ (by decide)]; omega)
  have r4 : ∀ q, q ≠ (9 : Fin 32) → reg n4 q = reg n3 q := fun q hq => by
    rw [u4.regs]; simp only [runBlock, BInstr.run, rpL]; exact updz t3.zero hq
  have e42C : S + BitVec.ofNat 32 0x420 + 0xC = S + BitVec.ofNat 32 0x42C := by rw [BitVec.add_assoc]; rfl
  have e430 : S + BitVec.ofNat 32 0x42C + 4 = S + BitVec.ofNat 32 0x430 := by rw [BitVec.add_assoc]; rfl
  have e49 : reg n4 (9 : Fin 32) = memLoad32 n3.mem (S + BitVec.ofNat 32 0x42C) := by
    rw [u4.regs]; simp +decide only [runBlock, BInstr.run, rpL, upd, ↓reduceIte]; rw [sp3, e42C]
  have K4 : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg m q := fun q hq => by
    rw [r4 q (by revert hq; revert q; decide), K3 q (by revert hq; revert q; decide)]
  have sp4 : reg n4 sp = S + BitVec.ofNat 32 0x420 := by rw [r4 sp (by decide)]; exact sp3
  have o4 : reg n4 (8 : Fin 32) = out := by rw [r4 8 (by decide)]; exact e38
  have sav3 : ∀ c, 0x494 ≤ c → c + 4 ≤ 0x4A0 → memLoad32 n3.mem (S + BitVec.ofNat 32 c) =
      memLoad32 (rpSaves m.mem S m) (S + BitVec.ofNat 32 c) := fun c h1 h2 => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc, mem3, bytesMem_outside (sepS S (.inl (by omega)) (by decide) (by omega))]
    rcases bytesResult (memLoad32 (rpSaves m.mem S m) self) (memLoad32 (rpSaves m.mem S m) (self + 4))
      (memLoad32 (rpSaves m.mem S m) (self + 8)) 0x61 with _ | ⟨q, e'⟩
    · rfl
    · exact memStore32_get_sep (((sS.sub (c := 8) (l := 4) (by decide)).subR (c := 0x1A0 + (c + j)) (l := 1) (by omega)) |>
        fun h => by
          rwa [show self + BitVec.ofNat 32 8 = self + 8 from rfl, BitVec.add_assoc,
            show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + (c + j)) = BitVec.ofNat 32 (c + j) by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
              omega] at h)
  have w0 : memLoad32 n3.mem (S + BitVec.ofNat 32 0x420 + BitVec.ofNat 32 0x7C) = reg m ra := by
    rw [a74, sav3 _ (by decide) (by decide)]; exact sv.1
  have w1 : memLoad32 n3.mem (S + BitVec.ofNat 32 0x420 + BitVec.ofNat 32 0x78) = reg m (8 : Fin 32) := by
    rw [a74, sav3 _ (by decide) (by decide)]; exact sv.2.1
  have w2 : memLoad32 n3.mem (S + BitVec.ofNat 32 0x420 + BitVec.ofNat 32 0x74) = reg m (9 : Fin 32) := by
    rw [a74, sav3 _ (by decide) (by decide)]; exact sv.2.2
  unfold RpOut
  rcases hres : bytesResult (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)) (memLoad32 m.mem (self + 8)) 0x61
    with _ | ⟨p, e⟩
  · -- Reader::bytes runs out
    have hres' := hBR.trans hres
    obtain ⟨bw, bb⟩ := bytesMem_none (out := S + BitVec.ofNat 32 0x42C) (n := 0x61) hres'
    rw [← mem3] at bw bb
    obtain ⟨n5, d5, u5⟩ := u4.self.taken C3.self 0x42 rp_at_1a (by decide) (by
      show branchTaken .beq (reg n4 (9 : Fin 32)) 0 = true; rw [e49, bw]; decide)
    obtain ⟨n6, c6, u6⟩ := u5.self.block rpZ C3.self rpZ_end ⟨trivial, trivial⟩
    have r6 : ∀ q, q ≠ a0 → reg n6 q = reg n4 q := fun q hq => by
      rw [u6.regs]; simp only [runBlock, BInstr.run, rpZ]; rw [updz u5.self.zero hq, u5.regs]
    have a6 : reg n6 a0 = 0 := by
      rw [u6.regs]; simp +decide only [runBlock, BInstr.run, rpZ, upd, ↓reduceIte]; rw [u5.regs, sp4]
      show (n3.mem (S + BitVec.ofNat 32 0x420 + 0x10)).zeroExtend 32 = 0
      rw [show S + BitVec.ofNat 32 0x420 + 0x10 = S + BitVec.ofNat 32 0x42C + 4 by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl, bb]
      rfl
    obtain ⟨n7, d7, u7⟩ := u6.self.jump C3.self rp_at_46 (off' := 0x4A) (by decide) (by rw [u6.pc]; decide)
    obtain ⟨n8, c8, pc8, sp8, ra8, s08, s18, k8, m8⟩ := rp_epi1 (v := 0) C3 u7.self
      (by rw [u7.regs, r6 sp (by decide)]; exact sp4) (by rw [u7.regs, r6 8 (by decide)]; exact o4)
      (by rw [u7.regs]; exact a6) hS4 hS8 (by omega) o2 w0 w1 w2 hret
    refine ⟨n8, c1.trans (c2.trans (c3.trans (c4.trans (.cons d5 (c6.trans (.cons d7 c8)))))), pc8, by rw [sp8, spF],
      fun q hq => ?_, fun x hx ho hs => ?_, ?_, ?_, ?_⟩
    · match q, hq with
      | 8, _ => exact s08
      | 9, _ => exact s18
      | 3, _ => rw [k8 3 (by decide), u7.regs, r6 3 (by decide), K4 3 (by decide)]
      | 4, _ => rw [k8 4 (by decide), u7.regs, r6 4 (by decide), K4 4 (by decide)]
      | 18, _ => rw [k8 18 (by decide), u7.regs, r6 18 (by decide), K4 18 (by decide)]
      | 19, _ => rw [k8 19 (by decide), u7.regs, r6 19 (by decide), K4 19 (by decide)]
      | 20, _ => rw [k8 20 (by decide), u7.regs, r6 20 (by decide), K4 20 (by decide)]
      | 21, _ => rw [k8 21 (by decide), u7.regs, r6 21 (by decide), K4 21 (by decide)]
      | 22, _ => rw [k8 22 (by decide), u7.regs, r6 22 (by decide), K4 22 (by decide)]
      | 23, _ => rw [k8 23 (by decide), u7.regs, r6 23 (by decide), K4 23 (by decide)]
      | 24, _ => rw [k8 24 (by decide), u7.regs, r6 24 (by decide), K4 24 (by decide)]
      | 25, _ => rw [k8 25 (by decide), u7.regs, r6 25 (by decide), K4 25 (by decide)]
      | 26, _ => rw [k8 26 (by decide), u7.regs, r6 26 (by decide), K4 26 (by decide)]
      | 27, _ => rw [k8 27 (by decide), u7.regs, r6 27 (by decide), K4 27 (by decide)]
    · rw [m8, dq_st8 (nO ho).1, dq_st8 (nO ho).2, mem3, bytesMem_outside (sF hx), hres']
      exact rpSaves_out (sSav hx)
    · rw [m8]; exact memStore8_same _ _ _
    · rw [m8, dq_st8 (show Sep out 1 (out + 1) 1 by
        have := sep_offsets out (c := 0) (n := 1) (d := 1) (k := 1) (.inl (by decide)) (by decide) (by decide)
        rwa [add_ofNat_zero] at this), memStore8_same]; rfl
    · refine memLoad32_congr fun j hj => ?_
      have hx : Sep (S + 0xFFFFFE60) 0x640 (self + 8 + BitVec.ofNat 32 j) 1 := by
        rw [show self + 8 + BitVec.ofNat 32 j = self + BitVec.ofNat 32 (8 + j) from add_ofNat_assoc self 8 j]
        exact (sS.sub (c := 8 + j) (l := 1) (by omega)).symm
      have ho : Sep out 8 (self + 8 + BitVec.ofNat 32 j) 1 := by
        rw [show self + 8 + BitVec.ofNat 32 j = self + BitVec.ofNat 32 (8 + j) from add_ofNat_assoc self 8 j]
        exact sOS.subR (c := 8 + j) (l := 1) (by omega)
      rw [m8, dq_st8 (nO ho).1, dq_st8 (nO ho).2, mem3, bytesMem_outside (sF hx), hres', rpSaves_out (sSav hx)]
  · -- 97 bytes at `p`
    have hres' := hBR.trans hres
    obtain ⟨bw, b4⟩ := bytesMem_some (out := S + BitVec.ofNat 32 0x42C) (n := 0x61) hres'
    rw [← mem3] at bw b4
    have hcd : (memLoad32 m.mem (self + 8)).toNat + 0x61 ≤ (memLoad32 m.mem (self + 4)).toNat ∧
        memLoad32 m.mem self + memLoad32 m.mem (self + 8) = p ∧ memLoad32 m.mem (self + 8) + 0x61 = e := by
      rw [bytesResult_eq] at hres
      by_cases hc : (memLoad32 m.mem (self + 8)).toNat + (0x61 : Word).toNat ≤ (memLoad32 m.mem (self + 4)).toNat
      · rw [ite_eq_left hc] at hres
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hres)
        exact ⟨hc, h1, h2⟩
      · rw [ite_eq_right hc] at hres; exact absurd hres (by simp)
    obtain ⟨hcd, hp, he⟩ := hcd
    have pT : p.toNat = (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 8)).toNat := by
      rw [← hp, BitVec.toNat_add]; omega
    have pj : ∀ j, j < 0x61 → p + BitVec.ofNat 32 j = memLoad32 m.mem self +
        BitVec.ofNat 32 ((memLoad32 m.mem (self + 8)).toNat + j) := fun j hj => by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, pT]; omega
    have bF : ∀ j, j < 0x61 → Sep (S + 0xFFFFFE60) 0x640 (p + BitVec.ofNat 32 j) 1 := fun j hj => by
      rw [pj j hj]; exact (sB.sub (c := (memLoad32 m.mem (self + 8)).toNat + j) (l := 1) (by omega)).symm
    have bO : ∀ j, j < 0x61 → Sep out 8 (p + BitVec.ofNat 32 j) 1 := fun j hj => by
      rw [pj j hj]; exact (sBO.sub (c := (memLoad32 m.mem (self + 8)).toNat + j) (l := 1) (by omega)).symm
    have bS : ∀ j, j < 0x61 → Sep (self + 8) 4 (p + BitVec.ofNat 32 j) 1 := fun j hj => by
      rw [pj j hj]; exact (sBS.sub (c := (memLoad32 m.mem (self + 8)).toNat + j) (l := 1) (by omega)).symm
    have n3x : ∀ x, Sep (S + BitVec.ofNat 32 0x42C) 8 x 1 → Sep (self + 8) 4 x 1 → n3.mem x = rpSaves m.mem S m x :=
      fun x h1 h2 => by rw [mem3, bytesMem_outside h1, hres']; exact memStore32_get_sep h2
    have n3b : ∀ j, j < 0x61 → n3.mem (p + BitVec.ofNat 32 j) = m.mem (p + BitVec.ofNat 32 j) := fun j hj => by
      rw [n3x _ (sF (bF j hj)) (bS j hj), rpSaves_out (sSav (bF j hj))]
    have dR : ∀ i, i < 0xC60 → ((0x3FCC4200 : Word) + BitVec.ofNat 32 i).toNat = 0x3FCC4200 + i := fun i hi => by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x3FCC4200 : Word).toNat = 0x3FCC4200 from rfl]; omega
    have D3 : P3Data n3.mem := D.ofR fun i hi => by
      rw [n3x _ (F.bufData (by decide) (by rw [dR i hi]; omega) (by rw [dR i hi]; omega))
        (sSD.sub (c := 8) (l := 4) (by decide) |>.subR (c := i) (l := 1) hi),
        rpSaves_out (F.bufData (by decide) (by rw [dR i hi]; omega) (by rw [dR i hi]; omega))]
    have hp0' : p ≠ 0 := fun h => by have := pT; rw [h] at this; simp at this; omega
    obtain ⟨n5, d5, u5⟩ := u4.self.notTaken C3.self 0x1C rp_at_1a (by decide) (by
      show branchTaken .beq (reg n4 (9 : Fin 32)) 0 = false; rw [e49, bw]
      simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; exact hp0')
    obtain ⟨n6, c6, u6⟩ := u5.self.block rpN C3.self rpN_end (by
      simp only [BlockOk, BInstr.ok, rpN]; simp +decide only [and_true]
      rw [u5.regs, sp4]; show (S + BitVec.ofNat 32 0x420 + 0x10).toNat % 4 = 0
      rw [BitVec.add_assoc, show (BitVec.ofNat 32 0x420 + 0x10 : Word) = BitVec.ofNat 32 0x430 from rfl, fa _ (by decide)]; omega)
    have a6 : reg n6 a0 = 0 := by
      rw [u6.regs]; simp +decide only [runBlock, BInstr.run, rpN, upd, ↓reduceIte]; rw [u5.regs, sp4]
      show memLoad32 n3.mem (S + BitVec.ofNat 32 0x420 + 0x10) + 0xFFFFFF9F = 0
      rw [show S + BitVec.ofNat 32 0x420 + 0x10 = S + BitVec.ofNat 32 0x42C + 4 by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl, b4]
      rfl
    have r6 : ∀ q, q ≠ a0 → reg n6 q = reg n4 q := fun q hq => by
      rw [u6.regs, runBlock_reg _ _ _ q u5.self.zero (by simp only [rpN]; revert hq; revert q; decide), u5.regs]
    have sOS1 : ∀ c, c < 2 → Sep (out + BitVec.ofNat 32 c) 1 (self + 8) 4 := fun c hc => by
      have := (sOS.sub (c := c) (l := 1) (by omega)).subR (c := 8) (l := 4) (by decide); exact this
    have o01 : Sep out 1 (out + 1) 1 := by
      have := sep_offsets out (c := 0) (n := 1) (d := 1) (k := 1) (.inl (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    have n3e : memLoad32 n3.mem (self + 8) = e := by
      have s1 : Sep (S + BitVec.ofNat 32 0x42C) 8 (self + 8) 4 :=
        (fIn (c := 0x42C) (l := 8) (by decide) ((sS.sub (c := 8) (l := 1) (by decide)).symm) |> fun _ =>
          (sS.sub (c := 8) (l := 4) (by decide)).subR (c := 0x1A0 + 0x42C) (l := 8) (by decide) |> fun h => by
            rw [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x42C) = BitVec.ofNat 32 0x42C from rfl] at h
            exact h.symm)
      rw [mem3]; unfold bytesMem; rw [hres']
      dsimp only
      rw [memLoad32_store32_sep (show Sep (S + BitVec.ofNat 32 0x42C + 4) 4 (self + 8) 4 from s1.sub (c := 4) (l := 4) (by decide)),
        memLoad32_store32_sep ((s1.sub (c := 0) (l := 4) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h),
        memLoad32_store32_same]
    obtain ⟨n7, d7, u7⟩ := u6.self.notTaken C3.self 0x24 rp_at_22 (by decide) (by
      show branchTaken .bne (reg n6 a0) 0 = false; rw [a6]; decide)
    obtain ⟨n8, c8, u8⟩ := u7.self.block rpT C3.self rpT_end ⟨trivial, trivial, trivial⟩
    have a8 : reg n8 a0 = (m.mem p).zeroExtend 32 := by
      rw [u8.regs]; simp +decide only [runBlock, BInstr.run, rpT, upd, ↓reduceIte]; rw [u7.regs, r6 9 (by decide), e49, bw]
      show (n3.mem (p + 0)).zeroExtend 32 = _
      have := n3b 0 (by decide); rw [add_ofNat_zero] at this
      rw [show p + (0 : Word) = p from BitVec.add_zero p, this]
    have r8 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n8 q = reg n4 q := fun q hq => by
      rw [u8.regs, runBlock_reg _ _ _ q u7.self.zero (by simp only [rpT]; revert hq; revert q; decide), u7.regs,
        r6 q (by revert hq; revert q; decide)]
    have u8' : St n3.mem RP n8 0x2A (reg n8) := ⟨u8.pc, u8.mem, fun _ => rfl⟩
    by_cases h4 : m.mem p ≠ 4
    · -- not tag 4
      have nf : ¬ FsOk m.mem p := fun h => h4 h.1
      obtain ⟨n9, d9, u9⟩ := u8'.taken C3.self 0x3E rp_at_2a (by decide) (by
        show branchTaken .bne (reg n8 a0) (reg n8 a1) = true
        rw [a8, u8.regs]; simp +decide only [runBlock, BInstr.run, rpT, upd, ↓reduceIte]
        rw [show aluEval .add (0 : Word) 4 = 4 from rfl]
        have : (m.mem p).zeroExtend 32 ≠ (4 : Word) := fun h => h4 (by
          have := congrArg BitVec.toNat h; rw [zext8_toNat] at this; exact BitVec.eq_of_toNat_eq this)
        simp only [branchTaken, bne_iff_ne, ne_eq]; exact this)
      obtain ⟨n10, c10, pc10, sp10, ra10, s010, s110, k10, m10⟩ := rp_tail C3 u9.self
        (by rw [u9.regs, r8 sp (by decide)]; exact sp4) (by rw [u9.regs, r8 8 (by decide)]; exact o4)
        hS4 hS8 (by omega) o2 w0 w1 w2 hret
      refine ⟨n10, c1.trans (c2.trans (c3.trans (c4.trans (.cons d5 (c6.trans (.cons d7 (c8.trans (.cons d9 c10)))))))),
        pc10, by rw [sp10, spF], fun q hq => ?_, fun x hx ho hs => ?_, ?_, ?_⟩
      · match q, hq with
        | 8, _ => exact s010
        | 9, _ => exact s110
        | 3, _ => rw [k10 3 (by decide), u9.regs, r8 3 (by decide), K4 3 (by decide)]
        | 4, _ => rw [k10 4 (by decide), u9.regs, r8 4 (by decide), K4 4 (by decide)]
        | 18, _ => rw [k10 18 (by decide), u9.regs, r8 18 (by decide), K4 18 (by decide)]
        | 19, _ => rw [k10 19 (by decide), u9.regs, r8 19 (by decide), K4 19 (by decide)]
        | 20, _ => rw [k10 20 (by decide), u9.regs, r8 20 (by decide), K4 20 (by decide)]
        | 21, _ => rw [k10 21 (by decide), u9.regs, r8 21 (by decide), K4 21 (by decide)]
        | 22, _ => rw [k10 22 (by decide), u9.regs, r8 22 (by decide), K4 22 (by decide)]
        | 23, _ => rw [k10 23 (by decide), u9.regs, r8 23 (by decide), K4 23 (by decide)]
        | 24, _ => rw [k10 24 (by decide), u9.regs, r8 24 (by decide), K4 24 (by decide)]
        | 25, _ => rw [k10 25 (by decide), u9.regs, r8 25 (by decide), K4 25 (by decide)]
        | 26, _ => rw [k10 26 (by decide), u9.regs, r8 26 (by decide), K4 26 (by decide)]
        | 27, _ => rw [k10 27 (by decide), u9.regs, r8 27 (by decide), K4 27 (by decide)]
      · rw [m10, dq_st8 (nO ho).1, dq_st8 (nO ho).2, n3x _ (sF hx) hs, rpSaves_out (sSav hx)]
      · rw [m10, memLoad32_store8_sep ((sOS1 0 (by decide)) |> fun h => by rwa [add_ofNat_zero] at h),
          memLoad32_store8_sep (show Sep (out + 1) 1 (self + 8) 4 from sOS1 1 (by decide))]; exact n3e
      · rw [ite_eq_right nf, m10]
        exact ⟨memStore8_same _ _ _, by rw [dq_st8 o01, memStore8_same]⟩
    · -- tag 4: from_sec1_bytes
      have h4' : m.mem p = 4 := Decidable.of_not_not h4
      obtain ⟨n9, d9, u9⟩ := u8'.notTaken C3.self 0x2E rp_at_2a (by decide) (by
        show branchTaken .bne (reg n8 a0) (reg n8 a1) = false
        rw [a8, u8.regs]; simp +decide only [runBlock, BInstr.run, rpT, upd, ↓reduceIte]; rw [h4']; decide)
      obtain ⟨n10, c10, u10⟩ := u9.self.block rpC C3.self rpC_end ⟨trivial, trivial, trivial⟩
      have r10 : ∀ q, reg n10 q = (runBlock rpC (n3.mem, reg n9)).2 q := fun q => by rw [u10.regs]
      have sIp : Sep p 0x61 (S + 0xFFFFFE60) 0x5C0 := by
        have := (sB.sub (c := (memLoad32 m.mem (self + 8)).toNat) (l := 0x61) (by omega)).subR (c := 0) (l := 0x5C0) (by decide)
        rw [add_ofNat_zero] at this
        have e0 := pj 0 (by decide); rw [add_ofNat_zero, Nat.add_zero] at e0
        rw [e0]; exact this
      have hb1A' : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := hb1A
      obtain ⟨n11, c11, u11, sp11, k11, fr11, ok11, bad11⟩ := c_fs (S := S) (out := S + BitVec.ofNat 32 0x42C) (inp := p)
        (⟨u10.pc, u10.mem, fun _ => rfl⟩ : St n3.mem RP n10 0x32 (reg n10)) C3.self C3.fs D3 F' rp_at_32 rp_at_36
        (by decide) (by decide)
        (by rw [r10, runBlock_reg _ _ _ sp u9.self.zero (by decide), u9.regs, r8 sp (by decide)]; exact sp4)
        (by rw [r10]; simp +decide only [runBlock, BInstr.run, rpC, upd, ↓reduceIte]; rw [u9.regs, r8 sp (by decide), sp4]
            exact e42C)
        (by rw [r10]; simp +decide only [runBlock, BInstr.run, rpC, upd, ↓reduceIte]; rw [u9.regs, r8 9 (by decide), e49, bw]
            exact BitVec.zero_add _)
        sIp (by rw [pT]; omega) (by rw [fa _ (by decide)]; omega) (by rw [fa _ (by decide)]; omega)
        (sep_of_le (by rw [hb1A', fa _ (by decide)]; omega) (by rw [fa _ (by decide)]; omega)).symm
      have hFs : FsOk n3.mem p ↔ FsOk m.mem p := fsOk_congr n3b
      have hbF : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := hb1A
      have hiF : ∀ {x : Word}, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFE60) 0x5C0 x 1 := fun {x} hx =>
        sep_of_le (by rw [hbF]; omega) (by have := x.isLt; omega)
      have C11 : RpCode n11.mem := C3.hi fun x hx => fr11 x (hiF hx) (F.hiOut (by decide) hx)
      have up : ∀ d, 0x494 ≤ d → d + 1 ≤ 0x4A0 → n11.mem (S + BitVec.ofNat 32 d) = n3.mem (S + BitVec.ofNat 32 d) := fun d h1 h2 =>
        fr11 _ (sep_of_le (by rw [hbF, fa _ (by omega)]; omega) (by rw [fa _ (by omega)]; omega))
          (sepS S (.inl (by omega)) (by decide) (by omega))
      have wS : ∀ c, 0x74 ≤ c → c + 4 ≤ 0x80 → memLoad32 n11.mem (S + BitVec.ofNat 32 0x420 + BitVec.ofNat 32 c) =
          memLoad32 n3.mem (S + BitVec.ofNat 32 0x420 + BitVec.ofNat 32 c) := fun c h1 h2 => memLoad32_congr fun j hj => by
        rw [a74, add_ofNat_assoc]; exact up _ (by omega) (by omega)
      have n11e : memLoad32 n11.mem (self + 8) = e := by
        rw [← n3e]
        exact memLoad32_congr fun j hj => by
          have hx : Sep (S + 0xFFFFFE60) 0x640 (self + 8 + BitVec.ofNat 32 j) 1 := by
            rw [show self + 8 + BitVec.ofNat 32 j = self + BitVec.ofNat 32 (8 + j) from add_ofNat_assoc self 8 j]
            exact (sS.sub (c := 8 + j) (l := 1) (by omega)).symm
          exact fr11 _ (hx.sub (c := 0) (l := 0x5C0) (by decide) |> fun h => by rwa [add_ofNat_zero] at h) (fIn (by decide) hx)
      obtain ⟨n12, c12, u12⟩ := u11.block rpR C11.self rpR_end (by
        simp only [BlockOk, BInstr.ok, rpR]; simp +decide only [and_true]
        rw [sp11]; show (S + 0x420 + 0xC).toNat % 4 = 0
        rw [show (S + 0x420 + 0xC : Word) = S + BitVec.ofNat 32 0x42C by rw [BitVec.add_assoc]; rfl, fa _ (by decide)]; omega)
      have a12 : reg n12 a0 = memLoad32 n11.mem (S + BitVec.ofNat 32 0x42C) := by
        rw [u12.regs]; simp +decide only [runBlock, BInstr.run, rpR, upd, ↓reduceIte]; rw [sp11]
        rw [show (S + 0x420 + 0xC : Word) = S + BitVec.ofNat 32 0x42C by rw [BitVec.add_assoc]; rfl]
      have r12 : ∀ q, q ≠ a0 → reg n12 q = reg n11 q := fun q hq => by
        rw [u12.regs]; simp only [runBlock, BInstr.run, rpR]; exact updz u11.zero hq
      have u12' : St n11.mem RP n12 0x3C (reg n12) := ⟨u12.pc, u12.mem, fun _ => rfl⟩
      have s8 : reg n12 (8 : Fin 32) = out := by
        rw [r12 8 (by decide), k11 8 (by decide), r10, runBlock_reg _ _ _ 8 u9.self.zero (by decide), u9.regs, r8 8 (by decide)]
        exact o4
      have sp12 : reg n12 sp = S + BitVec.ofNat 32 0x420 := by rw [r12 sp (by decide)]; exact sp11
      by_cases hok : FsOk m.mem p
      · -- Ok
        have z := ok11 (hFs.2 hok)
        obtain ⟨n13, d13, u13⟩ := u12'.taken C11.self 0x5E rp_at_3c (by decide) (by
          show branchTaken .beq (reg n12 a0) 0 = true; rw [a12, z]; decide)
        have s9 : reg n13 (9 : Fin 32) = p := by
          rw [u13.regs, r12 9 (by decide), k11 9 (by decide), r10, runBlock_reg _ _ _ 9 u9.self.zero (by decide), u9.regs,
            r8 9 (by decide), e49, bw]
        have o4' : (out + 4).toNat = out.toNat + 4 := by
          rw [BitVec.toNat_add, show (4 : Word).toNat = 4 from rfl]; omega
        have hRPn : 0x40000000 ≤ RP.toNat := by decide
        have sO4 : Sep (out + 4) 4 RP readP384PointCode.length := sep_of_le (by rw [o4']; omega) (by decide)
        obtain ⟨n14, c14, u14⟩ := u13.self.block rpO C11.self rpO_end (by
          simp only [BlockOk, BInstr.ok, rpO]; simp +decide only [and_true]
          rw [u13.regs, s8]
          exact ⟨by rw [o4']; omega, sO4⟩)
        obtain ⟨M14, hM14⟩ : ∃ M14, memStore32 n11.mem (out + 4) p = M14 := ⟨_, rfl⟩
        have m14 : n14.mem = M14 := by
          have s8' : reg n13 (8 : Fin 32) = out := by rw [u13.regs, s8]
          rw [u14.mem, ← hM14]; simp only [runBlock, BInstr.run, rpO]; rw [s8', s9]
        have s4x : ∀ {x : Word}, Sep out 8 x 1 → Sep (out + 4) 4 x 1 := fun {x} h => h.sub (c := 4) (l := 4) (by decide)
        have h14 : ∀ x, Sep (out + 4) 4 x 1 → M14 x = n11.mem x := fun x h => by rw [← hM14]; exact memStore32_get_sep h
        have C14 : RpCode M14 := C11.hi fun x hx => h14 x (sep_of_le (by rw [o4']; omega) (by have := x.isLt; omega))
        have u14' : St M14 RP n14 0x60 (reg n14) := ⟨u14.pc, m14, fun _ => rfl⟩
        obtain ⟨n15, d15, u15⟩ := u14'.jump C14.self rp_at_60 (off' := 0x50) (by decide) (by rw [u14.pc]; decide)
        have rr : ∀ q, reg n15 q = reg n12 q := fun q => by
          rw [u15.regs, u14.regs]; simp only [runBlock, BInstr.run, rpO]; rw [u13.regs]
        have oS : ∀ c, 0x74 ≤ c → c + 4 ≤ 0x80 → Sep (out + 4) 4 (S + BitVec.ofNat 32 0x420 + BitVec.ofNat 32 c) 4 := fun c h1 h2 => by
          rw [a74]
          have := (sO.sub (c := 4) (l := 4) (by decide)).subR (c := 0x1A0 + (0x420 + c)) (l := 4) (by omega)
          rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + (0x420 + c)) = BitVec.ofNat 32 (0x420 + c) by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
            omega] at this
        have wM : ∀ c, 0x74 ≤ c → c + 4 ≤ 0x80 → memLoad32 M14 (S + BitVec.ofNat 32 0x420 + BitVec.ofNat 32 c) =
            memLoad32 n3.mem (S + BitVec.ofNat 32 0x420 + BitVec.ofNat 32 c) := fun c h1 h2 => by
          rw [← hM14, memLoad32_store32_sep (oS c h1 h2), wS c h1 h2]
        obtain ⟨n16, c16, pc16, sp16, ra16, s016, s116, k16, m16⟩ := rp_epi2 (v := 0) (w0 := reg m ra) (w1 := reg m (8 : Fin 32)) (w2 := reg m (9 : Fin 32)) C14 u15.self
          (by rw [rr]; exact sp12) (by rw [rr]; exact s8) (by rw [rr, a12, z]) hS4 hS8 (by omega) o2
          (by rw [wM _ (by decide) (by decide)]; exact w0) (by rw [wM _ (by decide) (by decide)]; exact w1)
          (by rw [wM _ (by decide) (by decide)]; exact w2) hret
        refine ⟨n16, c1.trans (c2.trans (c3.trans (c4.trans (.cons d5 (c6.trans (.cons d7 (c8.trans (.cons d9 (c10.trans
          (c11.trans (c12.trans (.cons d13 (c14.trans (.cons d15 c16)))))))))))))), pc16, by rw [sp16, spF],
          fun q hq => ?_, fun x hx ho hs => ?_, ?_, ?_⟩
        · match q, hq with
          | 8, _ => exact s016
          | 9, _ => exact s116
          | 3, _ => rw [k16 3 (by decide), u15.regs, u14.regs, runBlock_reg _ _ _ 3 u13.self.zero (by decide), u13.regs, r12 3 (by decide), k11 3 (by decide), r10, runBlock_reg _ _ _ 3 u9.self.zero (by decide), u9.regs, r8 3 (by decide), K4 3 (by decide)]
          | 4, _ => rw [k16 4 (by decide), u15.regs, u14.regs, runBlock_reg _ _ _ 4 u13.self.zero (by decide), u13.regs, r12 4 (by decide), k11 4 (by decide), r10, runBlock_reg _ _ _ 4 u9.self.zero (by decide), u9.regs, r8 4 (by decide), K4 4 (by decide)]
          | 18, _ => rw [k16 18 (by decide), u15.regs, u14.regs, runBlock_reg _ _ _ 18 u13.self.zero (by decide), u13.regs, r12 18 (by decide), k11 18 (by decide), r10, runBlock_reg _ _ _ 18 u9.self.zero (by decide), u9.regs, r8 18 (by decide), K4 18 (by decide)]
          | 19, _ => rw [k16 19 (by decide), u15.regs, u14.regs, runBlock_reg _ _ _ 19 u13.self.zero (by decide), u13.regs, r12 19 (by decide), k11 19 (by decide), r10, runBlock_reg _ _ _ 19 u9.self.zero (by decide), u9.regs, r8 19 (by decide), K4 19 (by decide)]
          | 20, _ => rw [k16 20 (by decide), u15.regs, u14.regs, runBlock_reg _ _ _ 20 u13.self.zero (by decide), u13.regs, r12 20 (by decide), k11 20 (by decide), r10, runBlock_reg _ _ _ 20 u9.self.zero (by decide), u9.regs, r8 20 (by decide), K4 20 (by decide)]
          | 21, _ => rw [k16 21 (by decide), u15.regs, u14.regs, runBlock_reg _ _ _ 21 u13.self.zero (by decide), u13.regs, r12 21 (by decide), k11 21 (by decide), r10, runBlock_reg _ _ _ 21 u9.self.zero (by decide), u9.regs, r8 21 (by decide), K4 21 (by decide)]
          | 22, _ => rw [k16 22 (by decide), u15.regs, u14.regs, runBlock_reg _ _ _ 22 u13.self.zero (by decide), u13.regs, r12 22 (by decide), k11 22 (by decide), r10, runBlock_reg _ _ _ 22 u9.self.zero (by decide), u9.regs, r8 22 (by decide), K4 22 (by decide)]
          | 23, _ => rw [k16 23 (by decide), u15.regs, u14.regs, runBlock_reg _ _ _ 23 u13.self.zero (by decide), u13.regs, r12 23 (by decide), k11 23 (by decide), r10, runBlock_reg _ _ _ 23 u9.self.zero (by decide), u9.regs, r8 23 (by decide), K4 23 (by decide)]
          | 24, _ => rw [k16 24 (by decide), u15.regs, u14.regs, runBlock_reg _ _ _ 24 u13.self.zero (by decide), u13.regs, r12 24 (by decide), k11 24 (by decide), r10, runBlock_reg _ _ _ 24 u9.self.zero (by decide), u9.regs, r8 24 (by decide), K4 24 (by decide)]
          | 25, _ => rw [k16 25 (by decide), u15.regs, u14.regs, runBlock_reg _ _ _ 25 u13.self.zero (by decide), u13.regs, r12 25 (by decide), k11 25 (by decide), r10, runBlock_reg _ _ _ 25 u9.self.zero (by decide), u9.regs, r8 25 (by decide), K4 25 (by decide)]
          | 26, _ => rw [k16 26 (by decide), u15.regs, u14.regs, runBlock_reg _ _ _ 26 u13.self.zero (by decide), u13.regs, r12 26 (by decide), k11 26 (by decide), r10, runBlock_reg _ _ _ 26 u9.self.zero (by decide), u9.regs, r8 26 (by decide), K4 26 (by decide)]
          | 27, _ => rw [k16 27 (by decide), u15.regs, u14.regs, runBlock_reg _ _ _ 27 u13.self.zero (by decide), u13.regs, r12 27 (by decide), k11 27 (by decide), r10, runBlock_reg _ _ _ 27 u9.self.zero (by decide), u9.regs, r8 27 (by decide), K4 27 (by decide)]
        · rw [m16, dq_st8 (nO ho).1, h14 x (s4x ho),
            fr11 x (hx.sub (c := 0) (l := 0x5C0) (by decide) |> fun h => by rwa [add_ofNat_zero] at h) (fIn (by decide) hx),
            n3x _ (sF hx) hs, rpSaves_out (sSav hx)]
        · rw [m16, memLoad32_store8_sep ((sOS1 0 (by decide)) |> fun h => by rwa [add_ofNat_zero] at h), ← hM14,
            memLoad32_store32_sep (show Sep (out + 4) 4 (self + 8) 4 from
              (sOS.sub (c := 4) (l := 4) (by decide)).subR (c := 8) (l := 4) (by decide)), n11e]
        · rw [ite_eq_left hok, m16]
          refine ⟨by rw [memStore8_same]; rfl, ?_⟩
          rw [memLoad32_store8_sep (by
            have := sep_offsets out (c := 0) (n := 1) (d := 4) (k := 4) (.inl (by decide)) (by decide) (by decide)
            rwa [add_ofNat_zero] at this), ← hM14, memLoad32_store32_same]
      · -- Err: from_sec1_bytes rejects the point
        have o1 := bad11 (fun h => hok (hFs.1 h))
        obtain ⟨n13, d13, u13⟩ := u12'.notTaken C11.self 0x3E rp_at_3c (by decide) (by
          show branchTaken .beq (reg n12 a0) 0 = false; rw [a12, o1]; decide)
        obtain ⟨n14, c14, pc14, sp14, ra14, s014, s114, k14, m14⟩ := rp_tail (w0 := reg m ra) (w1 := reg m (8 : Fin 32))
          (w2 := reg m (9 : Fin 32)) C11 u13.self
          (by rw [u13.regs]; exact sp12) (by rw [u13.regs]; exact s8) hS4 hS8 (by omega) o2
          (by rw [wS _ (by decide) (by decide)]; exact w0) (by rw [wS _ (by decide) (by decide)]; exact w1)
          (by rw [wS _ (by decide) (by decide)]; exact w2) hret
        refine ⟨n14, c1.trans (c2.trans (c3.trans (c4.trans (.cons d5 (c6.trans (.cons d7 (c8.trans (.cons d9 (c10.trans
          (c11.trans (c12.trans (.cons d13 c14)))))))))))), pc14, by rw [sp14, spF],
          fun q hq => ?_, fun x hx ho hs => ?_, ?_, ?_⟩
        · match q, hq with
          | 8, _ => exact s014
          | 9, _ => exact s114
          | 3, _ => rw [k14 3 (by decide), u13.regs, r12 3 (by decide), k11 3 (by decide), r10, runBlock_reg _ _ _ 3 u9.self.zero (by decide), u9.regs, r8 3 (by decide), K4 3 (by decide)]
          | 4, _ => rw [k14 4 (by decide), u13.regs, r12 4 (by decide), k11 4 (by decide), r10, runBlock_reg _ _ _ 4 u9.self.zero (by decide), u9.regs, r8 4 (by decide), K4 4 (by decide)]
          | 18, _ => rw [k14 18 (by decide), u13.regs, r12 18 (by decide), k11 18 (by decide), r10, runBlock_reg _ _ _ 18 u9.self.zero (by decide), u9.regs, r8 18 (by decide), K4 18 (by decide)]
          | 19, _ => rw [k14 19 (by decide), u13.regs, r12 19 (by decide), k11 19 (by decide), r10, runBlock_reg _ _ _ 19 u9.self.zero (by decide), u9.regs, r8 19 (by decide), K4 19 (by decide)]
          | 20, _ => rw [k14 20 (by decide), u13.regs, r12 20 (by decide), k11 20 (by decide), r10, runBlock_reg _ _ _ 20 u9.self.zero (by decide), u9.regs, r8 20 (by decide), K4 20 (by decide)]
          | 21, _ => rw [k14 21 (by decide), u13.regs, r12 21 (by decide), k11 21 (by decide), r10, runBlock_reg _ _ _ 21 u9.self.zero (by decide), u9.regs, r8 21 (by decide), K4 21 (by decide)]
          | 22, _ => rw [k14 22 (by decide), u13.regs, r12 22 (by decide), k11 22 (by decide), r10, runBlock_reg _ _ _ 22 u9.self.zero (by decide), u9.regs, r8 22 (by decide), K4 22 (by decide)]
          | 23, _ => rw [k14 23 (by decide), u13.regs, r12 23 (by decide), k11 23 (by decide), r10, runBlock_reg _ _ _ 23 u9.self.zero (by decide), u9.regs, r8 23 (by decide), K4 23 (by decide)]
          | 24, _ => rw [k14 24 (by decide), u13.regs, r12 24 (by decide), k11 24 (by decide), r10, runBlock_reg _ _ _ 24 u9.self.zero (by decide), u9.regs, r8 24 (by decide), K4 24 (by decide)]
          | 25, _ => rw [k14 25 (by decide), u13.regs, r12 25 (by decide), k11 25 (by decide), r10, runBlock_reg _ _ _ 25 u9.self.zero (by decide), u9.regs, r8 25 (by decide), K4 25 (by decide)]
          | 26, _ => rw [k14 26 (by decide), u13.regs, r12 26 (by decide), k11 26 (by decide), r10, runBlock_reg _ _ _ 26 u9.self.zero (by decide), u9.regs, r8 26 (by decide), K4 26 (by decide)]
          | 27, _ => rw [k14 27 (by decide), u13.regs, r12 27 (by decide), k11 27 (by decide), r10, runBlock_reg _ _ _ 27 u9.self.zero (by decide), u9.regs, r8 27 (by decide), K4 27 (by decide)]
        · rw [m14, dq_st8 (nO ho).1, dq_st8 (nO ho).2,
            fr11 x (hx.sub (c := 0) (l := 0x5C0) (by decide) |> fun h => by rwa [add_ofNat_zero] at h) (fIn (by decide) hx),
            n3x _ (sF hx) hs, rpSaves_out (sSav hx)]
        · rw [m14, memLoad32_store8_sep ((sOS1 0 (by decide)) |> fun h => by rwa [add_ofNat_zero] at h),
            memLoad32_store8_sep (show Sep (out + 1) 1 (self + 8) 4 from sOS1 1 (by decide)), n11e]
        · rw [ite_eq_right hok, m14]
          exact ⟨memStore8_same _ _ _, by rw [dq_st8 o01, memStore8_same]⟩

end C3.RV32.Rp
