import C3BootProofs.Proofs.Sha512Rounds

/-!
# `compress512`: loading a block

The loop from 0x94 to 0xF8 slices the 128-byte block at `s5` with
`RangeFrom::index` 16 times and stores each big-endian 64-bit word, low half
first, in the buffer at `F + 0x58`.
-/

namespace C3.RV32

open C3.Image

theorem lo64_ofNat (N : Nat) : lo64 (BitVec.ofNat 64 N) = BitVec.ofNat 32 N := by
  apply BitVec.eq_of_toNat_eq
  rw [lo64_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem hi64_ofNat {N : Nat} (h : N < 2 ^ 64) : hi64 (BitVec.ofNat 64 N) = BitVec.ofNat 32 (N / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [hi64_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  omega

theorem wordAt512 (block : Bytes) (i : Nat) :
    Sha512.wordAt block i = BitVec.ofNat 64 ((((((((0 * 256 + block.getD (8 * i + 0) 0) * 256 +
      block.getD (8 * i + 1) 0) * 256 + block.getD (8 * i + 2) 0) * 256 + block.getD (8 * i + 3) 0) * 256 +
      block.getD (8 * i + 4) 0) * 256 + block.getD (8 * i + 5) 0) * 256 + block.getD (8 * i + 6) 0) * 256 +
      block.getD (8 * i + 7) 0) := rfl

theorem memBytes_lt (M : Word → BitVec 8) (p : Word) {n i : Nat} (hi : i < n) : (memBytes M p n).getD i 0 < 256 := by
  rw [memBytes_getD hi]; exact (M (p + BitVec.ofNat 32 i)).isLt

theorem be64_wordAt (M : Word → BitVec 8) (cur : Word) {i : Nat} (hi : i < 16) :
    let p := cur + BitVec.ofNat 32 (8 * i)
    (((M (p + 5)).zeroExtend 32 <<< 16 ||| (M (p + 4)).zeroExtend 32 <<< 24) |||
        ((M (p + 6)).zeroExtend 32 <<< 8 ||| (M (p + 7)).zeroExtend 32)) =
      lo64 (Sha512.schedule (memBytes M cur 128))[i]! ∧
    (((M (p + 3)).zeroExtend 32 ||| ((M (p + 2)).zeroExtend 32 <<< 8)) |||
        (((M (p + 0)).zeroExtend 32 <<< 24) ||| ((M (p + 1)).zeroExtend 32 <<< 16))) =
      hi64 (Sha512.schedule (memBytes M cur 128))[i]! := by
  intro p
  have e : ∀ c, c < 8 → M (p + BitVec.ofNat 32 c) = M (cur + BitVec.ofNat 32 (8 * i + c)) := fun c _ => by
    rw [add_ofNat_assoc]
  have g : ∀ c, c < 8 → (memBytes M cur 128).getD (8 * i + c) 0 = (M (p + BitVec.ofNat 32 c)).toNat :=
    fun c hc => by rw [e c hc, memBytes_getD (by omega)]
  have b : ∀ c, c < 8 → (memBytes M cur 128).getD (8 * i + c) 0 < 256 := fun c _ => memBytes_lt M cur (by omega)
  rw [Sha512.sched_lt _ hi, wordAt512]
  have b0 := b 0 (by omega); have b1 := b 1 (by omega); have b2 := b 2 (by omega); have b3 := b 3 (by omega)
  have b4 := b 4 (by omega); have b5 := b 5 (by omega); have b6 := b 6 (by omega); have b7 := b 7 (by omega)
  have h0 : (memBytes M cur 128).getD (8 * i + 0) 0 = (M (p + 0)).toNat := g 0 (by omega)
  have h1 : (memBytes M cur 128).getD (8 * i + 1) 0 = (M (p + 1)).toNat := g 1 (by omega)
  have h2 : (memBytes M cur 128).getD (8 * i + 2) 0 = (M (p + 2)).toNat := g 2 (by omega)
  have h3 : (memBytes M cur 128).getD (8 * i + 3) 0 = (M (p + 3)).toNat := g 3 (by omega)
  have h4 : (memBytes M cur 128).getD (8 * i + 4) 0 = (M (p + 4)).toNat := g 4 (by omega)
  have h5 : (memBytes M cur 128).getD (8 * i + 5) 0 = (M (p + 5)).toNat := g 5 (by omega)
  have h6 : (memBytes M cur 128).getD (8 * i + 6) 0 = (M (p + 6)).toNat := g 6 (by omega)
  have h7 : (memBytes M cur 128).getD (8 * i + 7) 0 = (M (p + 7)).toNat := g 7 (by omega)
  constructor
  · rw [lo64_ofNat, BitVec.or_comm, BitVec.or_comm ((M (p + 6)).zeroExtend 32 <<< 8),
      BitVec.or_comm ((M (p + 5)).zeroExtend 32 <<< 16), be32_assemble]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [hi64_ofNat (by omega), be32_assemble]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega


/-- `RangeFrom::index` on an `L`-byte slice. -/
theorem rangeFromIndex_okL {B cur retAddr : Word} {off L : Nat} {m : Machine}
    (hc : CodeIn m.mem B rangeFromIndexCode) (hpc : m.pc = B) (hoff : off ≤ L) (hL : L < 2 ^ 32)
    (ha0 : reg m a0 = BitVec.ofNat 32 off) (ha1 : reg m a1 = cur) (ha2 : reg m a2 = BitVec.ofNat 32 L)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = m.mem ∧
      reg m' a0 = cur + BitVec.ofNat 32 off ∧ reg m' a1 = BitVec.ofNat 32 (L - off) ∧
      reg m' a2 = BitVec.ofNat 32 (L - off) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m' q = reg m q := by
  have s0 : St m.mem B m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hnb : branchTaken .bltu (reg m a2) (reg m a0) = false := by
    unfold branchTaken; rw [ha2, ha0]
    simp only [BitVec.ult, BitVec.toNat_ofNat]
    have ho : off % 2 ^ 32 = off := Nat.mod_eq_of_lt (by omega)
    rw [Nat.mod_eq_of_lt hL, ho]; exact decide_eq_false (by omega)
  obtain ⟨m1, d1, u1⟩ := s0.notTaken hc 4 rfi_at_0 (by decide) hnb
  obtain ⟨m2, d2, u2⟩ := u1.alu hc rfi_at_4 (off' := 6) (by decide)
  obtain ⟨m3, d3, u3⟩ := u2.alu hc rfi_at_6 (off' := 8) (by decide)
  obtain ⟨m4, d4, u4⟩ := u3.alu hc rfi_at_8 (off' := 0xA) (by decide)
  obtain ⟨m5, d5, pc5, mem5, regs5⟩ := u4.jalr hc rfi_at_a
  have sub_eq : BitVec.ofNat 32 L - BitVec.ofNat 32 off = BitVec.ofNat 32 (L - off) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  refine ⟨m5, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5)))), ?_, mem5, ?_, ?_, ?_, ?_⟩
  · rw [pc5]; simp +decide only [upd, ↓reduceIte]; rw [add_lit_zero, hra, hret]
  · rw [regs5]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [ha0, ha1, BitVec.add_comm]
  · rw [regs5]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [ha2, ha0, sub_eq]; exact BitVec.zero_add _
  · rw [regs5]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [ha2, ha0, sub_eq]
  · intro q q0 q1 q2
    rw [regs5]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, s0.zero]
    · simp only [upd, h0, q0, q1, q2, ite_false]

/-- The block's schedule as a function. -/
abbrev s5W (M0 : Word → BitVec 8) (cur : Word) : Nat → Sha512.W64 :=
  fun t => (Sha512.schedule (memBytes M0 cur 128))[t]!

/-- The address of word `k`'s low half in the buffer at `F + 0x58`. -/
def bslot (F : Word) (k : Nat) : Word := F + BitVec.ofNat 32 (0x58 + 8 * k)

/-- The registers the load loop never writes. -/
def s5LdKeep (q : Fin 32) : Bool := q.val ∉ [0, 1, 8, 9, 10, 11, 12, 13, 14, 15, 16]

/-- What holds at 0x94 before word `i` of the block at `cur`: `Mb` and `g`
are the memory and registers when the loop starts. -/
structure S5L (P F cur : Word) (M0 Mb : Word → BitVec 8) (g : Fin 32 → Word) (i : Nat)
    (M : Word → BitVec 8) (m : Machine) : Prop where
  st : St M P m 0x94 (reg m)
  code : CodeIn M P sha512CompressCode
  idx : CodeIn M (P + 0xFFFFFFEA) rangeFromIndexCode
  r8 : reg m 8 = BitVec.ofNat 32 (8 * i)
  r21 : reg m 21 = cur
  r25 : reg m 25 = F + BitVec.ofNat 32 0x58
  buf : ∀ k, k < i → memLoad32 M (bslot F k) = lo64 (s5W M0 cur k) ∧
    memLoad32 M (bslot F k + 4) = hi64 (s5W M0 cur k)
  fr : ∀ x, Sep (F + BitVec.ofNat 32 0x58) 0x80 x 1 → M x = Mb x
  keep : ∀ q, s5LdKeep q = true → reg m q = g q

/-- What the load loop needs and doesn't change: the buffer is aligned, apart
from the code, `RangeFrom::index`, and the block, whose bytes are `M0`'s. -/
structure S5LS (P F cur : Word) (M0 Mb : Word → BitVec 8) : Prop where
  hP : P.toNat % 2 = 0
  hF : F.toNat % 4 = 0
  hFw : F.toNat + 0x390 ≤ 2 ^ 32
  sC : Sep (F + BitVec.ofNat 32 0x58) 0x80 P sha512CompressCode.length
  sI : Sep (F + BitVec.ofNat 32 0x58) 0x80 (P + 0xFFFFFFEA) rangeFromIndexCode.length
  sB : Sep (F + BitVec.ofNat 32 0x58) 0x80 cur 128
  blk : ∀ j, j < 128 → Mb (cur + BitVec.ofNat 32 j) = M0 (cur + BitVec.ofNat 32 j)

def s5LdA : List BInstr := [.aluImm .add a0 (8 : Fin 32) 0xFFFFFF80]

def s5LdB : List BInstr := [.aluImm .add a2 x0 0x80, .alu .add a0 x0 (8 : Fin 32), .alu .add a1 x0 (21 : Fin 32)]

def s5LdR : List BInstr := [.alu .add a2 x0 a1, .aluImm .add a1 x0 0x7]

/-- One big-endian word from the slice at `a0` into the buffer at `s9 + s0`. -/
def s5LdC : List BInstr :=
  [.lbu a1 a0 0x5, .lbu a2 a0 0x6, .lbu a3 a0 0x4, .lbu a4 a0 0x7, .lbu a6 a0 0x0, .lbu (9 : Fin 32) a0 0x2,
   .lbu a5 a0 0x1, .lbu a0 a0 0x3, .aluImm .sll a2 a2 0x8, .aluImm .sll a1 a1 0x10, .aluImm .sll a3 a3 0x18,
   .alu .or a2 a2 a4, .alu .or a1 a1 a3, .aluImm .sll (9 : Fin 32) (9 : Fin 32) 0x8, .alu .or a1 a1 a2,
   .alu .or a0 a0 (9 : Fin 32), .aluImm .sll a5 a5 0x10, .aluImm .sll a6 a6 0x18, .alu .or a2 a6 a5,
   .alu .add a3 (25 : Fin 32) (8 : Fin 32), .alu .or a0 a0 a2, .sw a3 a1 0x0, .sw a3 a0 0x4,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x8]

section
set_option maxRecDepth 100000
theorem s5LdA_end : blockEnd sha512CompressCode 0x94 s5LdA = some 0x98 := by decide
theorem s5LdB_end : blockEnd sha512CompressCode 0x9A s5LdB = some 0xA2 := by decide
theorem s5LdR_end : blockEnd sha512CompressCode 0xAA s5LdR = some 0xAE := by decide
theorem s5LdC_end : blockEnd sha512CompressCode 0xB2 s5LdC = some 0xF6 := by decide
end

set_option maxRecDepth 100000 in
theorem s5LdC_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock s5LdC (M, f)).1 = memStore32 (memStore32 M (f 25 + f 8 + 0)
      ((((M (f a0 + 5)).zeroExtend 32 <<< 16 ||| (M (f a0 + 4)).zeroExtend 32 <<< 24) |||
        ((M (f a0 + 6)).zeroExtend 32 <<< 8 ||| (M (f a0 + 7)).zeroExtend 32))))
      (f 25 + f 8 + 4)
      ((((M (f a0 + 3)).zeroExtend 32 ||| ((M (f a0 + 2)).zeroExtend 32 <<< 8)) |||
        (((M (f a0 + 0)).zeroExtend 32 <<< 24) ||| ((M (f a0 + 1)).zeroExtend 32 <<< 16)))) ∧
    (runBlock s5LdC (M, f)).2 8 = f 8 + 0x8 ∧
    ∀ q, s5LdKeep q = true → (runBlock s5LdC (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, s5LdC, upd_app, ↓reduceIte]
  refine ⟨?_, rfl, fun q hq => ?_⟩
  · simp only [ev_sll8, ev_sll16, ev_sll24, ev_or, ev_add]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [hz]
    · simp only [h0, ite_false, pkeep_ne (r := 8) hq rfl, pkeep_ne (r := 9) hq rfl, pkeep_ne (r := a0) hq rfl,
        pkeep_ne (r := a1) hq rfl, pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a3) hq rfl,
        pkeep_ne (r := a4) hq rfl, pkeep_ne (r := a5) hq rfl, pkeep_ne (r := a6) hq rfl]

theorem beq_ld8 {i : Nat} (hi : i < 16) : branchTaken .beq (BitVec.ofNat 32 (8 * i) + 0xFFFFFF80) 0 = false := by
  unfold branchTaken
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0xFFFFFF80 : Word).toNat = 0xFFFFFF80 from rfl,
    show (0 : Word).toNat = 0 from rfl] at this
  omega

theorem bgeu7 {i : Nat} (hi : i < 16) : branchTaken .bgeu 7 (BitVec.ofNat 32 (0x80 - 8 * i)) = false := by
  unfold branchTaken
  simp only [BitVec.ult, BitVec.toNat_ofNat, show (7 : Word).toNat = 7 from rfl]
  rw [Nat.mod_eq_of_lt (by omega)]
  simp only [Bool.not_eq_false', decide_eq_true_eq]
  omega

theorem bslot_addr (F : Word) (i : Nat) : F + BitVec.ofNat 32 0x58 + BitVec.ofNat 32 (8 * i) = bslot F i := by
  unfold bslot; rw [add_ofNat_assoc]

theorem bslot_sep {F : Word} (_hFw : F.toNat + 0x390 ≤ 2 ^ 32) {k k' : Nat} (h : k ≠ k') (hk : k < 16) (hk' : k' < 16)
    {a b : Nat} (ha : a ≤ 4) (hb : b ≤ 4) :
    Sep (bslot F k + BitVec.ofNat 32 a) 4 (bslot F k' + BitVec.ofNat 32 b) 4 := by
  unfold bslot
  rw [add_ofNat_assoc, add_ofNat_assoc]
  exact sep_offsets F (by omega) (by omega) (by omega)

theorem bslot_lohi {F : Word} (_hFw : F.toNat + 0x390 ≤ 2 ^ 32) {k : Nat} (hk : k < 16) :
    Sep (bslot F k) 4 (bslot F k + 4) 4 := by
  unfold bslot
  rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  exact sep_offsets F (by omega) (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- One word of the block into the buffer. -/
theorem s5_load_step {P F cur : Word} {M0 Mb M : Word → BitVec 8} {g : Fin 32 → Word} {i : Nat} {m : Machine}
    (S : S5LS P F cur M0 Mb) (I : S5L P F cur M0 Mb g i M m) (hi : i < 16) :
    ∃ m' M', Steps m m' ∧ S5L P F cur M0 Mb g (i + 1) M' m' := by
  have hFw := S.hFw
  obtain ⟨m1, c1, u1⟩ := St.block s5LdA I.st I.code s5LdA_end (by simp [BlockOk, BInstr.ok, s5LdA])
  simp only [runBlock, BInstr.run, s5LdA] at u1
  have x10 : reg m1 a0 = BitVec.ofNat 32 (8 * i) + 0xFFFFFF80 := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [I.r8]; rfl
  have k1' : ∀ q, q.val ≠ 0 → q ≠ a0 → reg m1 q = reg m q := fun q h0 h1 => by
    rw [u1.regs]; simp only [upd_app, h0, h1, ite_false]
  obtain ⟨m2, d2, u2⟩ := u1.self.notTaken I.code 0x9A s5_at_98 (by decide)
    (by rw [x10, u1.self.zero]; exact beq_ld8 hi)
  obtain ⟨m3, c3, u3⟩ := St.block s5LdB u2 I.code s5LdB_end (by simp [BlockOk, BInstr.ok, s5LdB])
  simp only [runBlock, BInstr.run, s5LdB] at u3
  have z1 : reg m1 0 = 0 := u1.self.zero
  have k3 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m3 q = reg m q := fun q h0 h1 h2 h3 => by
    rw [u3.regs]; simp only [upd_app, h0, h1, h2, h3, ite_false]; exact k1' q h0 h1
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa I.code s5_at_a2 s5_at_a6
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P S.hP 0xFFFFFFEA (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  obtain ⟨m5, c5, pc5, mem5, a05, a15, a25, k5⟩ := rangeFromIndex_okL (B := P + 0xFFFFFFEA) (cur := cur)
    (retAddr := P + BitVec.ofNat 32 (0xA2 + 8)) (off := 8 * i) (L := 0x80) (m := m4)
    (by rw [mem4]; exact I.idx) pc4 (by omega) (by decide)
    (by rw [r4 a0 (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [k1' _ (by decide) (by decide), I.r8]; exact BitVec.zero_add _)
    (by rw [r4 a1 (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [k1' _ (by decide) (by decide), I.r21]; exact BitVec.zero_add _)
    (by rw [r4 a2 (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [show reg m1 x0 = 0 from z1]; exact BitVec.zero_add _)
    (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P S.hP (0xA2 + 8) (by decide)))
  rw [mem4] at mem5
  have s5 : St M P m5 0xAA (reg m5) := ⟨by rw [pc5], mem5, fun _ => rfl⟩
  have k5' : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ ra → reg m5 q = reg m q :=
    fun q h0 h1 h2 h3 hr => by rw [k5 q h1 h2 h3, r4 q hr, k3 q h0 h1 h2 h3]
  obtain ⟨m6, c6, u6⟩ := St.block s5LdR s5 I.code s5LdR_end (by simp [BlockOk, BInstr.ok, s5LdR])
  simp only [runBlock, BInstr.run, s5LdR] at u6
  obtain ⟨m7, d7, u7⟩ := u6.self.notTaken I.code 0xB2 s5_at_ae (by decide) (by
    rw [u6.regs, u6.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [show reg m5 x0 = 0 from s5.zero, a15]
    simp only [show ∀ x : Word, aluEval .add 0 x = x from fun x => BitVec.zero_add x]; exact bgeu7 hi)
  have k6 : ∀ q, q.val ≠ 0 → q ≠ a1 → q ≠ a2 → reg m6 q = reg m5 q := fun q h0 h1 h2 => by
    rw [u6.regs]; simp only [upd_app, h0, h1, h2, ite_false]
  have f25 : reg m6 25 = F + BitVec.ofNat 32 0x58 := by
    rw [k6 _ (by decide) (by decide) (by decide), k5' _ (by decide) (by decide) (by decide) (by decide) (by decide),
      I.r25]
  have f8 : reg m6 8 = BitVec.ofNat 32 (8 * i) := by
    rw [k6 _ (by decide) (by decide) (by decide), k5' _ (by decide) (by decide) (by decide) (by decide) (by decide),
      I.r8]
  have fa0 : reg m6 a0 = cur + BitVec.ofNat 32 (8 * i) := by
    rw [k6 _ (by decide) (by decide) (by decide), a05]
  have hal : (bslot F i).toNat % 4 = 0 := aligned_add S.hF (by omega)
  have hal4 : (bslot F i + 4).toNat % 4 = 0 := by
    unfold bslot; rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]; exact aligned_add S.hF (by omega)
  have sC : Sep (bslot F i) 4 P sha512CompressCode.length := by
    rw [← bslot_addr]; exact S.sC.sub (c := 8 * i) (by omega)
  have sC4 : Sep (bslot F i + 4) 4 P sha512CompressCode.length := by
    rw [← bslot_addr, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
    exact S.sC.sub (c := 8 * i + 4) (by omega)
  have sI : Sep (bslot F i) 4 (P + 0xFFFFFFEA) rangeFromIndexCode.length := by
    rw [← bslot_addr]; exact S.sI.sub (c := 8 * i) (by omega)
  have sI4 : Sep (bslot F i + 4) 4 (P + 0xFFFFFFEA) rangeFromIndexCode.length := by
    rw [← bslot_addr, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
    exact S.sI.sub (c := 8 * i + 4) (by omega)
  obtain ⟨E1, E8, E2⟩ := s5LdC_run (M := M) (f := reg m6) u6.self.zero
  obtain ⟨m8, c8, u8⟩ := St.block s5LdC u7 I.code s5LdC_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, s5LdC, upd_app, ↓reduceIte, and_true, true_and]
    simp only [ev_add]
    rw [f25, f8, bslot_addr, add_lit_zero]; exact ⟨⟨hal, sC⟩, hal4, sC4⟩)
  rw [E1, f25, f8, bslot_addr, add_lit_zero, fa0] at u8
  have byte : ∀ c, c < 8 → M (cur + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 c) =
      M0 (cur + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 c) := fun c hc => by
    rw [add_ofNat_assoc, I.fr _ (S.sB.subR (c := 8 * i + c) (l := 1) (by omega)), S.blk _ (by omega)]
  have hb : ∀ c, c < 8 → ∀ x, x = cur + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 c → M x = M0 x :=
    fun c hc x hx => by rw [hx]; exact byte c hc
  rw [hb 0 (by omega) (cur + BitVec.ofNat 32 (8 * i) + 0) rfl, hb 1 (by omega) (cur + BitVec.ofNat 32 (8 * i) + 1) rfl,
    hb 2 (by omega) (cur + BitVec.ofNat 32 (8 * i) + 2) rfl, hb 3 (by omega) (cur + BitVec.ofNat 32 (8 * i) + 3) rfl,
    hb 4 (by omega) (cur + BitVec.ofNat 32 (8 * i) + 4) rfl, hb 5 (by omega) (cur + BitVec.ofNat 32 (8 * i) + 5) rfl,
    hb 6 (by omega) (cur + BitVec.ofNat 32 (8 * i) + 6) rfl, hb 7 (by omega) (cur + BitVec.ofNat 32 (8 * i) + 7) rfl]
    at u8
  obtain ⟨hwl, hwh⟩ := be64_wordAt M0 cur hi
  rw [hwl, hwh] at u8
  obtain ⟨M8, hM8⟩ : ∃ M8, memStore32 (memStore32 M (bslot F i) (lo64 (s5W M0 cur i))) (bslot F i + 4)
      (hi64 (s5W M0 cur i)) = M8 := ⟨_, rfl⟩
  rw [hM8] at u8
  obtain ⟨m9, d9, u9⟩ := u8.jump (by rw [← hM8]; exact (I.code.store32 sC).store32 sC4) s5_at_f6 (off' := 0x94)
    (by decide) (pc_even (off' := 0x94) S.hP u8.pc (by decide) (by decide))
  have k9 : ∀ q, s5LdKeep q = true → reg m9 q = reg m q := fun q hq => by
    rw [u9.regs, E2 q hq, k6 q (fun e => pkeep_ne hq (r := 0) rfl (Fin.ext e)) (pkeep_ne hq rfl) (pkeep_ne hq rfl),
      k5' q (fun e => pkeep_ne hq (r := 0) rfl (Fin.ext e)) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)
        (pkeep_ne hq rfl)]
  refine ⟨m9, M8, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (c6.trans (.cons d7 (c8.trans (.cons d9
    (.refl _))))))))), ⟨u9.self, by rw [← hM8]; exact (I.code.store32 sC).store32 sC4,
    by rw [← hM8]; exact (I.idx.store32 sI).store32 sI4, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [u9.regs, E8, f8, show (0x8 : Word) = BitVec.ofNat 32 8 from rfl, ofNat_add_ofNat]; congr 1
  · rw [k9 _ rfl, I.r21]
  · rw [k9 _ rfl, I.r25]
  · intro k hk
    by_cases h : k = i
    · subst h
      refine ⟨?_, ?_⟩
      · rw [← hM8, memLoad32_store32_sep (bslot_lohi hFw hi).symm]; exact memLoad32_store32_same _ _ _
      · rw [← hM8]; exact memLoad32_store32_same _ _ _
    · have hk' : k < i := by omega
      have e0 : Sep (bslot F k) 4 (bslot F i) 4 := by
        have := bslot_sep hFw h (by omega) hi (a := 0) (b := 0) (by omega) (by omega)
        rw [add_ofNat_zero, add_ofNat_zero] at this; exact this
      have e1 : Sep (bslot F k) 4 (bslot F i + 4) 4 := by
        have := bslot_sep hFw h (by omega) hi (a := 0) (b := 4) (by omega) (by omega)
        rw [add_ofNat_zero] at this; exact this
      have e2 : Sep (bslot F k + 4) 4 (bslot F i) 4 := by
        have := bslot_sep hFw h (by omega) hi (a := 4) (b := 0) (by omega) (by omega)
        rw [add_ofNat_zero] at this; exact this
      have e3 : Sep (bslot F k + 4) 4 (bslot F i + 4) 4 :=
        bslot_sep hFw h (by omega) hi (a := 4) (b := 4) (by omega) (by omega)
      refine ⟨?_, ?_⟩
      · rw [← hM8, memLoad32_store32_sep e1.symm, memLoad32_store32_sep e0.symm]; exact (I.buf k hk').1
      · rw [← hM8, memLoad32_store32_sep e3.symm, memLoad32_store32_sep e2.symm]; exact (I.buf k hk').2
  · intro x hx
    rw [← hM8, memStore32_get_sep, memStore32_get_sep, I.fr x hx]
    · rw [← bslot_addr]; exact hx.sub (c := 8 * i) (l := 4) (by omega)
    · rw [← bslot_addr, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
      exact hx.sub (c := 8 * i + 4) (l := 4) (by omega)
  · intro q hq; rw [k9 q hq, I.keep q hq]

/-- With the buffer full, the loop exits to 0xF8. -/
theorem s5_load_exit {P F cur : Word} {M0 Mb M : Word → BitVec 8} {g : Fin 32 → Word} {m : Machine}
    (I : S5L P F cur M0 Mb g 16 M m) :
    ∃ m', Steps m m' ∧ St M P m' 0xF8 (reg m') ∧ ∀ q, s5LdKeep q = true → reg m' q = g q := by
  obtain ⟨m1, c1, u1⟩ := St.block s5LdA I.st I.code s5LdA_end (by simp [BlockOk, BInstr.ok, s5LdA])
  simp only [runBlock, BInstr.run, s5LdA] at u1
  have x10 : reg m1 a0 = BitVec.ofNat 32 (8 * 16) + 0xFFFFFF80 := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [I.r8]; rfl
  obtain ⟨m2, d2, u2⟩ := u1.self.taken I.code 0xF8 s5_at_98 (by decide)
    (by rw [x10, u1.self.zero]; decide)
  exact ⟨m2, c1.trans (.cons d2 (.refl _)), u2.self, fun q hq => by
    rw [u2.regs, u1.regs, upd_kp hq rfl rfl, I.keep q hq]⟩

/-- The load loop from word `i` to its exit. -/
theorem s5_load_from {P F cur : Word} {M0 Mb : Word → BitVec 8} {g : Fin 32 → Word}
    (S : S5LS P F cur M0 Mb) :
    ∀ k i (M : Word → BitVec 8) (m : Machine), i + k = 16 → S5L P F cur M0 Mb g i M m →
      ∃ m' M', Steps m m' ∧ S5L P F cur M0 Mb g 16 M' m'
  | 0, i, M, m, h, I => ⟨m, M, .refl _, by rw [Nat.add_zero] at h; subst h; exact I⟩
  | k + 1, i, M, m, h, I => by
    obtain ⟨m1, M1, c1, J⟩ := s5_load_step S I (by omega)
    obtain ⟨m2, M2, c2, J2⟩ := s5_load_from S k (i + 1) M1 m1 (by omega) J
    exact ⟨m2, M2, c1.trans c2, J2⟩

end C3.RV32
