import C3BootProofs.Proofs.Sha256LoopRounds

/-!
# `compress256`, compact backend: loading a block

The loop from 0x60 to 0xA0 slices the block at `s1` with `RangeFrom::index`
16 times and stores its big-endian words in the 16-word buffer at
`F + 0x6C`.
-/

namespace C3.RV32

open C3.Image

/-- The registers the load loop never writes. -/
def kcLoadKeep (q : Fin 32) : Bool := q.val ∉ [0, 1, 8, 10, 11, 12, 13]

/-- What holds at 0x60 before word `i` of the block at `cur`: `Mb` and `g`
are the memory and registers when the loop starts. -/
structure KCL (P F cur : Word) (M0 Mb : Word → BitVec 8) (g : Fin 32 → Word) (i : Nat)
    (M : Word → BitVec 8) (m : Machine) : Prop where
  st : St M P m 0x60 (reg m)
  code : CodeIn M P sha256CompressCode
  idx : CodeIn M (P + 0x25A) rangeFromIndexCode
  r8 : reg m 8 = BitVec.ofNat 32 (4 * i)
  r9 : reg m 9 = cur
  r21 : reg m 21 = 3
  r27 : reg m 27 = F + BitVec.ofNat 32 0x6C
  buf : ∀ k, k < i →
    memLoad32 M (F + BitVec.ofNat 32 (0x6C + 4 * k)) = (Sha256.schedule (memBytes M0 cur 64))[k]!
  fr : ∀ x, Sep (F + BitVec.ofNat 32 0x6C) 0x40 x 1 → M x = Mb x
  keep : ∀ q, kcLoadKeep q = true → reg m q = g q

/-- What the load loop needs and doesn't change: the buffer is aligned, apart
from the code, `RangeFrom::index`, and the block, whose bytes are `M0`'s. -/
structure KCLStatic (P F cur : Word) (M0 Mb : Word → BitVec 8) : Prop where
  hP : P.toNat % 2 = 0
  hF : F.toNat % 4 = 0
  sC : Sep (F + BitVec.ofNat 32 0x6C) 0x40 P sha256CompressCode.length
  sI : Sep (F + BitVec.ofNat 32 0x6C) 0x40 (P + 0x25A) rangeFromIndexCode.length
  sB : Sep (F + BitVec.ofNat 32 0x6C) 0x40 cur 64
  blk : ∀ j, j < 64 → Mb (cur + BitVec.ofNat 32 j) = M0 (cur + BitVec.ofNat 32 j)

def kcLdA : List BInstr := [.aluImm .add a0 (8 : Fin 32) 0xFFFFFFC0]

def kcLdB : List BInstr := [.aluImm .add a2 x0 0x40, .alu .add a0 x0 (8 : Fin 32), .alu .add a1 x0 (9 : Fin 32)]

/-- One big-endian word from the slice at `a0` into the buffer at `s11 + s0`. -/
def kcLdC : List BInstr :=
  [.lbu a1 a0 0x2, .lbu a2 a0 0x0, .lbu a3 a0 0x1, .lbu a0 a0 0x3, .aluImm .sll a1 a1 0x8,
   .aluImm .sll a3 a3 0x10, .aluImm .sll a2 a2 0x18, .alu .or a0 a0 a1, .alu .or a2 a2 a3, .alu .or a0 a0 a2,
   .alu .add a1 (27 : Fin 32) (8 : Fin 32), .sw a1 a0 0x0]

section
set_option maxRecDepth 20000
theorem kcLdA_end : blockEnd sha256CompressCode 0x60 kcLdA = some 0x64 := by decide
theorem kcLdB_end : blockEnd sha256CompressCode 0x66 kcLdB = some 0x6E := by decide
theorem kcLdC_end : blockEnd sha256CompressCode 0x7A kcLdC = some 0x9C := by decide
end

theorem ev_or (a b : Word) : aluEval .or a b = a ||| b := rfl
theorem ev_sll8 (x : Word) : aluEval .sll x 0x8 = x <<< 8 := rfl
theorem ev_sll16 (x : Word) : aluEval .sll x 0x10 = x <<< 16 := rfl
theorem ev_sll24 (x : Word) : aluEval .sll x 0x18 = x <<< 24 := rfl

set_option maxRecDepth 20000 in
theorem kcLdC_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock kcLdC (M, f)).1 = memStore32 M (f 27 + f 8 + 0)
      ((((M (f a0 + 3)).zeroExtend 32 ||| ((M (f a0 + 2)).zeroExtend 32 <<< 8)) |||
        (((M (f a0 + 0)).zeroExtend 32 <<< 24) ||| ((M (f a0 + 1)).zeroExtend 32 <<< 16)))) ∧
    (runBlock kcLdC (M, f)).2 8 = f 8 ∧ ∀ q, kcLoadKeep q = true → (runBlock kcLdC (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, kcLdC, upd_app, ↓reduceIte]
  refine ⟨?_, trivial, fun q hq => ?_⟩
  · simp only [ev_sll8, ev_sll16, ev_sll24, ev_or, ev_add]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [hz]
    · simp only [h0, ite_false, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl, pkeep_ne (r := a2) hq rfl,
        pkeep_ne (r := a3) hq rfl]

theorem beq_ld {i : Nat} (hi : i < 16) : branchTaken .beq (BitVec.ofNat 32 (4 * i) + 0xFFFFFFC0) 0 = false := by
  unfold branchTaken
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0xFFFFFFC0 : Word).toNat = 0xFFFFFFC0 from rfl,
    show (0 : Word).toNat = 0 from rfl] at this
  omega

theorem bgeu3 {i : Nat} (hi : i < 16) : branchTaken .bgeu 3 (BitVec.ofNat 32 (0x40 - 4 * i)) = false := by
  unfold branchTaken
  simp only [BitVec.ult, BitVec.toNat_ofNat, show (3 : Word).toNat = 3 from rfl]
  rw [Nat.mod_eq_of_lt (by omega)]
  simp only [Bool.not_eq_false', decide_eq_true_eq]
  omega

theorem buf_addr (F : Word) (i : Nat) : F + BitVec.ofNat 32 0x6C + BitVec.ofNat 32 (4 * i) + 0 =
    F + BitVec.ofNat 32 (0x6C + 4 * i) := by
  rw [add_lit_zero, add_ofNat_assoc]

set_option maxHeartbeats 4000000 in
/-- One word of the block into the buffer. -/
theorem kc_load_step {P F cur : Word} {M0 Mb M : Word → BitVec 8} {g : Fin 32 → Word} {i : Nat} {m : Machine}
    (S : KCLStatic P F cur M0 Mb) (I : KCL P F cur M0 Mb g i M m) (hi : i < 16) :
    ∃ m' M', Steps m m' ∧ KCL P F cur M0 Mb g (i + 1) M' m' := by
  obtain ⟨m1, c1, u1⟩ := St.block kcLdA I.st I.code kcLdA_end (by simp [BlockOk, BInstr.ok, kcLdA])
  simp only [runBlock, BInstr.run, kcLdA] at u1
  have x10 : reg m1 a0 = BitVec.ofNat 32 (4 * i) + 0xFFFFFFC0 := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [I.r8]; rfl
  have k1 : ∀ q, kcLoadKeep q = true → reg m1 q = reg m q := fun q hq => by
    rw [u1.regs, upd_kp hq rfl rfl]
  have k1' : ∀ q, q.val ≠ 0 → q ≠ a0 → reg m1 q = reg m q := fun q h0 h1 => by
    rw [u1.regs]; simp only [upd_app, h0, h1, ite_false]
  obtain ⟨m2, d2, u2⟩ := u1.self.notTaken I.code 0x66 kc_at_64 (by decide)
    (by rw [x10, u1.self.zero]; exact beq_ld hi)
  obtain ⟨m3, c3, u3⟩ := St.block kcLdB u2 I.code kcLdB_end (by simp [BlockOk, BInstr.ok, kcLdB])
  simp only [runBlock, BInstr.run, kcLdB] at u3
  have z1 : reg m1 0 = 0 := u1.self.zero
  have k3 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m3 q = reg m q := fun q h0 h1 h2 h3 => by
    rw [u3.regs]; simp only [upd_app, h0, h1, h2, h3, ite_false]; exact k1' q h0 h1
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa I.code kc_at_6e kc_at_72
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P S.hP 0x25A (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  obtain ⟨m5, c5, pc5, mem5, a05, a15, a25, k5⟩ := rangeFromIndex_ok (B := P + 0x25A) (cur := cur)
    (retAddr := P + BitVec.ofNat 32 (0x6E + 8)) (off := 4 * i) (m := m4)
    (by rw [mem4]; exact I.idx) pc4 (by omega)
    (by rw [r4 a0 (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [k1' _ (by decide) (by decide), I.r8]; exact BitVec.zero_add _)
    (by rw [r4 a1 (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [k1' _ (by decide) (by decide), I.r9]; exact BitVec.zero_add _)
    (by rw [r4 a2 (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [show reg m1 x0 = 0 from z1]; exact BitVec.zero_add _)
    (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P S.hP (0x6E + 8) (by decide)))
  rw [mem4] at mem5
  have s5 : St M P m5 0x76 (reg m5) := ⟨by rw [pc5], mem5, fun _ => rfl⟩
  have k5' : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ ra → reg m5 q = reg m q :=
    fun q h0 h1 h2 h3 hr => by rw [k5 q h1 h2 h3, r4 q hr, k3 q h0 h1 h2 h3]
  obtain ⟨m6, d6, u6⟩ := s5.notTaken I.code 0x7A kc_at_76 (by decide)
    (by rw [a15, k5' _ (by decide) (by decide) (by decide) (by decide) (by decide), I.r21]; exact bgeu3 hi)
  have f27 : reg m5 27 = F + BitVec.ofNat 32 0x6C := by
    rw [k5' _ (by decide) (by decide) (by decide) (by decide) (by decide), I.r27]
  have f8 : reg m5 8 = BitVec.ofNat 32 (4 * i) := by
    rw [k5' _ (by decide) (by decide) (by decide) (by decide) (by decide), I.r8]
  have hal : (F + BitVec.ofNat 32 (0x6C + 4 * i)).toNat % 4 = 0 := aligned_add S.hF (by omega)
  have sC : Sep (F + BitVec.ofNat 32 (0x6C + 4 * i)) 4 P sha256CompressCode.length := by
    rw [← add_ofNat_assoc]; exact S.sC.sub (c := 4 * i) (by omega)
  have sI : Sep (F + BitVec.ofNat 32 (0x6C + 4 * i)) 4 (P + 0x25A) rangeFromIndexCode.length := by
    rw [← add_ofNat_assoc]; exact S.sI.sub (c := 4 * i) (by omega)
  obtain ⟨E1, E8, E2⟩ := kcLdC_run (M := M) (f := reg m5) s5.zero
  obtain ⟨m7, c7, u7⟩ := St.block kcLdC u6 I.code kcLdC_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, kcLdC, upd_app, ↓reduceIte, and_true, true_and]
    simp only [ev_add]
    rw [f27, f8, buf_addr]; exact ⟨hal, sC⟩)
  rw [E1, f27, f8, buf_addr, a05] at u7
  have byte : ∀ c, c < 4 → M (cur + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 c) =
      M0 (cur + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 c) := fun c hc => by
    rw [add_ofNat_assoc, I.fr _ (S.sB.subR (c := 4 * i + c) (l := 1) (by omega)), S.blk _ (by omega)]
  have hb0 : M (cur + BitVec.ofNat 32 (4 * i) + 0) = M0 (cur + BitVec.ofNat 32 (4 * i) + 0) := byte 0 (by decide)
  have hb1 : M (cur + BitVec.ofNat 32 (4 * i) + 1) = M0 (cur + BitVec.ofNat 32 (4 * i) + 1) := byte 1 (by decide)
  have hb2 : M (cur + BitVec.ofNat 32 (4 * i) + 2) = M0 (cur + BitVec.ofNat 32 (4 * i) + 2) := byte 2 (by decide)
  have hb3 : M (cur + BitVec.ofNat 32 (4 * i) + 3) = M0 (cur + BitVec.ofNat 32 (4 * i) + 3) := byte 3 (by decide)
  have hw := be32_wordAt M0 cur hi
  simp only at hw
  rw [hb0, hb1, hb2, hb3, hw] at u7
  obtain ⟨m8, d8, u8⟩ := u7.aluImm (I.code.store32 sC) kc_at_9c (off' := 0x9E) (by decide)
  obtain ⟨m9, d9, u9⟩ := u8.jump (I.code.store32 sC) kc_at_9e (off' := 0x60) (by decide)
    (pc_even (off' := 0x60) S.hP u8.pc (by decide) (by decide))
  have k9 : ∀ q, kcLoadKeep q = true → reg m9 q = reg m q := fun q hq => by
    rw [u9.regs, upd_kp hq rfl rfl, E2 q hq,
      k5' q (fun e => pkeep_ne hq (r := 0) rfl (Fin.ext e)) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)
        (pkeep_ne hq rfl)]
  refine ⟨m9, _, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (.cons d6 (c7.trans (.cons d8
    (.cons d9 (.refl _))))))))), ⟨u9.self, I.code.store32 sC, I.idx.store32 sI, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [E8, f8]
    exact (ofNat_add_ofNat _ 4).trans (by rw [show 4 * i + 4 = 4 * (i + 1) by omega])
  · rw [k9 _ rfl, I.r9]
  · rw [k9 _ rfl, I.r21]
  · rw [k9 _ rfl, I.r27]
  · intro k hk
    by_cases h : k = i
    · subst h; exact memLoad32_store32_same _ _ _
    · rw [memLoad32_store32_sep (sep_offsets F (by omega) (by omega) (by omega))]
      exact I.buf k (by omega)
  · intro x hx
    rw [memStore32_get_sep (by rw [← add_ofNat_assoc]; exact hx.sub (c := 4 * i) (l := 4) (by omega))]
    exact I.fr x hx
  · intro q hq; rw [k9 q hq, I.keep q hq]

/-- With the buffer full, the loop exits to 0xA0. -/
theorem kc_load_exit {P F cur : Word} {M0 Mb M : Word → BitVec 8} {g : Fin 32 → Word} {m : Machine}
    (I : KCL P F cur M0 Mb g 16 M m) :
    ∃ m', Steps m m' ∧ St M P m' 0xA0 (reg m') ∧ ∀ q, kcLoadKeep q = true → reg m' q = g q := by
  obtain ⟨m1, c1, u1⟩ := St.block kcLdA I.st I.code kcLdA_end (by simp [BlockOk, BInstr.ok, kcLdA])
  simp only [runBlock, BInstr.run, kcLdA] at u1
  have x10 : reg m1 a0 = BitVec.ofNat 32 (4 * 16) + 0xFFFFFFC0 := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [I.r8]; rfl
  obtain ⟨m2, d2, u2⟩ := u1.self.taken I.code 0xA0 kc_at_64 (by decide)
    (by rw [x10, u1.self.zero]; decide)
  exact ⟨m2, c1.trans (.cons d2 (.refl _)), u2.self, fun q hq => by
    rw [u2.regs, u1.regs, upd_kp hq rfl rfl, I.keep q hq]⟩

/-- The load loop from word `i` to its exit. -/
theorem kc_load_from {P F cur : Word} {M0 Mb : Word → BitVec 8} {g : Fin 32 → Word}
    (S : KCLStatic P F cur M0 Mb) :
    ∀ k i (M : Word → BitVec 8) (m : Machine), i + k = 16 → KCL P F cur M0 Mb g i M m →
      ∃ m' M', Steps m m' ∧ KCL P F cur M0 Mb g 16 M' m'
  | 0, i, M, m, h, I => ⟨m, M, .refl _, by rw [Nat.add_zero] at h; subst h; exact I⟩
  | k + 1, i, M, m, h, I => by
    obtain ⟨m1, M1, c1, J⟩ := kc_load_step S I (by omega)
    obtain ⟨m2, M2, c2, J2⟩ := kc_load_from S k (i + 1) M1 m1 (by omega) J
    exact ⟨m2, M2, c1.trans c2, J2⟩

end C3.RV32
