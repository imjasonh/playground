import C3BootProofs.Proofs.FeCall
import C3BootProofs.Proofs.FeLoad
import C3BootProofs.Proofs.ParseSpec
import C3BootProofs.Proofs.MemcpyAny
import C3BootProofs.Proofs.Sha2Final

/-!
# `LimbBuffer::increment_limb`, as compiled

`wnaf`'s `LimbBuffer` reads a byte slice as little-endian `u64` limbs. The
struct holds the slice pointer and length, then `cur_limb`, `next_limb`, and
`cur_idx`, one word or two each. `increment_limb` moves `next_limb` to
`cur_limb`, adds 1 to `cur_idx`, and reads the next limb from the slice:
zero when it is empty, the bytes zero-extended through `memcpy` into a stack
buffer when it holds fewer than 8, and the first 8 bytes otherwise. Every
case reads the same `u64`: the first 8 bytes of the slice with zeros past
its end.
-/

namespace C3.RV32

open C3.Image

/-- Byte `k` of the `n`-byte slice at `p`, zero past its end. -/
def ilByte (M : Word → BitVec 8) (p : Word) (n k : Nat) : BitVec 8 :=
  if k < n then M (p + BitVec.ofNat 32 k) else 0

/-- Word `j` of the little-endian `u64` that `increment_limb` reads from
the `n`-byte slice at `p`. -/
def ilWord (M : Word → BitVec 8) (p : Word) (n j : Nat) : Word :=
  ilByte M p n (4 * j + 3) ++ ilByte M p n (4 * j + 2) ++ ilByte M p n (4 * j + 1) ++ ilByte M p n (4 * j)

theorem ilWord_toNat (M : Word → BitVec 8) (p : Word) (n j : Nat) :
    (ilWord M p n j).toNat = le32 (ilByte M p n (4 * j)).toNat (ilByte M p n (4 * j + 1)).toNat
      (ilByte M p n (4 * j + 2)).toNat (ilByte M p n (4 * j + 3)).toNat := by
  unfold ilWord
  have h0 := (ilByte M p n (4 * j)).isLt; have h1 := (ilByte M p n (4 * j + 1)).isLt
  have h2 := (ilByte M p n (4 * j + 2)).isLt
  simp only [BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt h0, ← Nat.shiftLeft_add_eq_or_of_lt h1,
    ← Nat.shiftLeft_add_eq_or_of_lt h2]
  simp only [Nat.shiftLeft_eq, le32]
  omega

/-- `((b3 << 24) | (b2 << 16)) | ((b1 << 8) | b0)` on zero-extended bytes. -/
theorem le4_hiLo (b0 b1 b2 b3 : BitVec 8) :
    (aluEval .or (aluEval .or (aluEval .sll (b3.zeroExtend 32) 0x18) (aluEval .sll (b2.zeroExtend 32) 0x10))
      (aluEval .or (aluEval .sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32))).toNat =
      le32 b0.toNat b1.toNat b2.toNat b3.toNat := by
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have v1 : (aluEval .sll (b1.zeroExtend 32) 8).toNat = b1.toNat * 2 ^ 8 := by rw [sll_byte _ (by decide)]; rfl
  have v2 : (aluEval .sll (b2.zeroExtend 32) 0x10).toNat = b2.toNat * 2 ^ 16 := by rw [sll_byte _ (by decide)]; rfl
  have v3 : (aluEval .sll (b3.zeroExtend 32) 0x18).toNat = b3.toNat * 2 ^ 24 := by rw [sll_byte _ (by decide)]; rfl
  have lo : (aluEval .or (aluEval .sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32)).toNat =
      b1.toNat * 2 ^ 8 + b0.toNat := by
    rw [or_nat _ _ (i := 8) (by rw [v1]; exact Nat.mul_mod_left _ _) (by rw [zext_tn]; exact h0), v1, zext_tn]
  have hi : (aluEval .or (aluEval .sll (b3.zeroExtend 32) 0x18) (aluEval .sll (b2.zeroExtend 32) 0x10)).toNat =
      b3.toNat * 2 ^ 24 + b2.toNat * 2 ^ 16 := by
    rw [or_nat _ _ (i := 24) (by rw [v3]; exact Nat.mul_mod_left _ _) (by rw [v2]; omega), v3, v2]
  rw [or_nat _ _ (i := 16) (by rw [hi]; omega) (by rw [lo]; omega), hi, lo]
  simp only [le32]; omega

/-- `((b2 << 16) | (b3 << 24)) | (b0 | (b1 << 8))` on zero-extended bytes. -/
theorem le4_loHi (b0 b1 b2 b3 : BitVec 8) :
    (aluEval .or (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18))
      (aluEval .or (b0.zeroExtend 32) (aluEval .sll (b1.zeroExtend 32) 8))).toNat =
      le32 b0.toNat b1.toNat b2.toNat b3.toNat := by
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have v1 : (aluEval .sll (b1.zeroExtend 32) 8).toNat = b1.toNat * 2 ^ 8 := by rw [sll_byte _ (by decide)]; rfl
  have v2 : (aluEval .sll (b2.zeroExtend 32) 0x10).toNat = b2.toNat * 2 ^ 16 := by rw [sll_byte _ (by decide)]; rfl
  have v3 : (aluEval .sll (b3.zeroExtend 32) 0x18).toNat = b3.toNat * 2 ^ 24 := by rw [sll_byte _ (by decide)]; rfl
  have lo : (aluEval .or (b0.zeroExtend 32) (aluEval .sll (b1.zeroExtend 32) 8)).toNat =
      b0.toNat + b1.toNat * 2 ^ 8 := by
    rw [or_nat' _ _ (i := 8) (by rw [zext_tn]; exact h0) (by rw [v1]; exact Nat.mul_mod_left _ _), v1, zext_tn]
  have hi : (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18)).toNat =
      b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 := by
    rw [or_nat' _ _ (i := 24) (by rw [v2]; omega) (by rw [v3]; exact Nat.mul_mod_left _ _), v3, v2]
  rw [or_nat _ _ (i := 16) (by rw [hi]; omega) (by rw [lo]; omega), hi, lo]
  simp only [le32]; omega

/-- A byte past the first `k` bytes of a copy to `dst` keeps its value. -/
theorem copyBytes_past {M : Word → BitVec 8} {dst src : Word} {j k : Nat} (hj : k ≤ j) (hj' : j < 2 ^ 32) :
    copyBytes M dst src k (dst + BitVec.ofNat 32 j) = M (dst + BitVec.ofNat 32 j) := by
  unfold copyBytes
  rw [add_sub_toNat dst hj', ite_eq_right (by omega)]

/-- A word store at one offset from `b` leaves the word at another. -/
theorem ld_st_off {M : Word → BitVec 8} {b v : Word} (c d : Word) (h : (c.toNat == d.toNat) = false)
    (hc : c.toNat % 4 = 0) (hd : d.toNat % 4 = 0) :
    memLoad32 (memStore32 M (b + c) v) (b + d) = memLoad32 M (b + d) := by
  have := c.isLt; have := d.isLt
  rw [← ofNat_toNat_self c, ← ofNat_toNat_self d]
  exact memLoad32_store32_off h hc hd (by omega) (by omega)

section
set_option maxRecDepth 20000
theorem il_at_18 : fetchRel incrementLimbCode 0x18 = some (.branch .beq a2 x0 0x2A, 2) := by decide
theorem il_at_1a : fetchRel incrementLimbCode 0x1A = some (.aluImm .add a0 x0 0x7, 2) := by decide
theorem il_at_1c : fetchRel incrementLimbCode 0x1C = some (.branch .bltu a0 a2 0x2E, 4) := by decide
theorem il_at_28 : fetchRel incrementLimbCode 0x28 = some (.auipc ra 0x0, 4) := by decide
theorem il_at_2c : fetchRel incrementLimbCode 0x2C = some (.jalr ra ra 0x100, 4) := by decide
theorem il_at_40 : fetchRel incrementLimbCode 0x40 = some (.jal x0 0x58, 2) := by decide
theorem il_at_48 : fetchRel incrementLimbCode 0x48 = some (.jal x0 0x50, 2) := by decide
theorem il_at_98 : fetchRel incrementLimbCode 0x98 = some (.load .lw ra sp 0xC, 2) := by decide
theorem il_at_9a : fetchRel incrementLimbCode 0x9A = some (.load .lw (8 : Fin 32) sp 0x8, 2) := by decide
theorem il_at_9c : fetchRel incrementLimbCode 0x9C = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem il_at_9e : fetchRel incrementLimbCode 0x9E = some (.jalr x0 ra 0x0, 2) := by decide

def ilProA : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFF0, .sw sp ra 0xC, .sw sp (8 : Fin 32) 0x8, .alu .add (8 : Fin 32) x0 a0]

def ilProB : List BInstr :=
  [.lw a0 a0 0x18, .lw a1 (8 : Fin 32) 0x10, .lw a3 (8 : Fin 32) 0x14, .lw a2 (8 : Fin 32) 0x4,
    .aluImm .add a0 a0 0x1]

def ilProC : List BInstr :=
  [.sw (8 : Fin 32) a1 0x8, .sw (8 : Fin 32) a3 0xC, .sw (8 : Fin 32) a0 0x18]

def ilZero : List BInstr :=
  [.aluImm .add a0 x0 0x0, .sw (8 : Fin 32) a0 0x10, .sw (8 : Fin 32) a0 0x14]

def ilCp : List BInstr :=
  [.lw a1 (8 : Fin 32) 0x0, .sw sp x0 0x0, .sw sp x0 0x4, .alu .add a0 x0 sp]

def ilCpEnd : List BInstr :=
  [.lw a0 sp 0x0, .lw a1 sp 0x4, .aluImm .add a2 x0 0x1, .sw (8 : Fin 32) a2 0x0, .sw (8 : Fin 32) x0 0x4,
    .sw (8 : Fin 32) a0 0x10, .sw (8 : Fin 32) a1 0x14]

def ilRdA : List BInstr :=
  [.lw a0 (8 : Fin 32) 0x0, .lbu (17 : Fin 32) a0 0x5, .lbu a3 a0 0x6, .lbu a4 a0 0x7, .lbu a6 a0 0x0,
    .lbu (5 : Fin 32) a0 0x1, .lbu a1 a0 0x3, .lbu a5 a0 0x2, .lbu (6 : Fin 32) a0 0x4,
    .aluImm .add (7 : Fin 32) a2 0xFFFFFFF8, .aluImm .add a0 a0 0x8]

def ilRdB : List BInstr :=
  [.aluImm .sll a4 a4 0x18, .aluImm .sll a3 a3 0x10, .aluImm .sll (17 : Fin 32) (17 : Fin 32) 0x8,
    .aluImm .sll a1 a1 0x18, .aluImm .sll a5 a5 0x10, .aluImm .sll (5 : Fin 32) (5 : Fin 32) 0x8,
    .alu .or a2 (5 : Fin 32) a6, .alu .or a1 a1 a5, .alu .or a5 (6 : Fin 32) (17 : Fin 32), .alu .or a3 a3 a4,
    .alu .or a1 a1 a2, .alu .or a3 a3 a5]

def ilRdC : List BInstr :=
  [.sw (8 : Fin 32) a0 0x0, .sw (8 : Fin 32) (7 : Fin 32) 0x4, .sw (8 : Fin 32) a1 0x10,
    .sw (8 : Fin 32) a3 0x14]

theorem ilProA_end : blockEnd incrementLimbCode 0 ilProA = some 0x8 := by decide
theorem ilProB_end : blockEnd incrementLimbCode 0x8 ilProB = some 0x12 := by decide
theorem ilProC_end : blockEnd incrementLimbCode 0x12 ilProC = some 0x18 := by decide
theorem ilZero_end : blockEnd incrementLimbCode 0x42 ilZero = some 0x48 := by decide
theorem ilCp_end : blockEnd incrementLimbCode 0x20 ilCp = some 0x28 := by decide
theorem ilCpEnd_end : blockEnd incrementLimbCode 0x30 ilCpEnd = some 0x40 := by decide
theorem ilRdA_end : blockEnd incrementLimbCode 0x4A ilRdA = some 0x72 := by decide
theorem ilRdB_end : blockEnd incrementLimbCode 0x72 ilRdB = some 0x8E := by decide
theorem ilRdC_end : blockEnd incrementLimbCode 0x8E ilRdC = some 0x98 := by decide
end

/-- The return through the saved `ra` and `s0`. -/
theorem il_epilogue {m : Machine} {M : Word → BitVec 8} {f : Fin 32 → Word} {P F r0 r8 : Word}
    (hc : CodeIn M P incrementLimbCode) (t : St M P m 0x98 f) (hsp : f sp = F)
    (hF : F.toNat % 4 = 0) (h1 : memLoad32 M (F + 0xC) = r0) (h2 : memLoad32 M (F + 8) = r8)
    (hret : r0 &&& ~~~1 = r0) :
    ∃ m', Steps m m' ∧ m'.pc = r0 ∧ m'.mem = M ∧ reg m' sp = F + 0x10 ∧ reg m' ra = r0 ∧
      reg m' s0 = r8 ∧ ∀ r, r ≠ sp → r ≠ ra → r ≠ s0 → reg m' r = f r := by
  have hz := t.zero
  obtain ⟨m1, e1, t1⟩ := t.lw hc il_at_98 (off' := 0x9A) (by decide)
    (by rw [hsp]; exact aligned_add hF (k := 0xC) (by decide))
  rw [hsp, h1] at t1
  have u1 : upd f ra r0 sp = F := by simp +decide [upd, hsp]
  obtain ⟨m2, e2, t2⟩ := t1.lw hc il_at_9a (off' := 0x9C) (by decide)
    (by rw [u1]; exact aligned_add hF (k := 8) (by decide))
  rw [u1, h2] at t2
  obtain ⟨m3, e3, t3⟩ := t2.aluImm hc il_at_9c (off' := 0x9E) (by decide)
  obtain ⟨m4, e4, pc4, mem4, regs4⟩ := t3.jalr hc il_at_9e
  refine ⟨m4, .cons e1 (.cons e2 (.cons e3 (.single e4))), ?_, mem4, ?_, ?_, ?_, ?_⟩
  · rw [pc4]; simp +decide only [upd]; simpa using hret
  · rw [regs4]; simp +decide [upd, aluEval, hsp]
  · rw [regs4]; simp +decide [upd]
  · rw [regs4]; simp +decide [upd]
  · intro r h1' h2' h3'
    rw [regs4]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [hz]
    · simp [upd, hr, h1', h2', h3']

/-- What `increment_limb` needs: its code and `memcpy`'s, aligned stack and
struct, and the slice's first `min n 8` bytes, the 32 bytes below `sp`, and
the 28-byte struct apart from each other and from the code. -/
structure ILEnv (M : Word → BitVec 8) (P sp0 s p n : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P incrementLimbCode
  mcS : CodeIn M (P + 0x128) memcpyStubCode
  mcB : CodeIn M (P + 0x128 + 8) memcpyBodyCode
  hp : memLoad32 M s = p
  hn : memLoad32 M (s + 4) = n
  hsa : sp0.toNat % 4 = 0
  hS : 0x20 ≤ sp0.toNat
  hs : s.toNat % 4 = 0
  sGC : Sep (sp0 + 0xFFFFFFE0) 0x20 P incrementLimbCode.length
  sGS : Sep (sp0 + 0xFFFFFFE0) 0x20 (P + 0x128) memcpyStubCode.length
  sGB : Sep (sp0 + 0xFFFFFFE0) 0x20 (P + 0x128 + 8) memcpyBodyCode.length
  sSC : Sep s 28 P incrementLimbCode.length
  sSS : Sep s 28 (P + 0x128) memcpyStubCode.length
  sSB : Sep s 28 (P + 0x128 + 8) memcpyBodyCode.length
  sSG : Sep s 28 (sp0 + 0xFFFFFFE0) 0x20
  sPG : Sep p (min n.toNat 8) (sp0 + 0xFFFFFFE0) 0x20
  sPS : Sep p (min n.toNat 8) s 28
  hpw : p.toNat + min n.toNat 8 < 2 ^ 32

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `LimbBuffer::increment_limb`**: for the struct at `s`,
whose slice is `n` bytes at `p`, it moves `next_limb` to `cur_limb`, adds 1
to `cur_idx`, sets `next_limb` to the slice's first 8 bytes with zeros past
its end, and drops those bytes from the slice. It changes nothing else but
32 bytes of stack. -/
theorem incrementLimb_correct (m : Machine) {P sp0 s p n retAddr : Word} (env : ILEnv m.mem P sp0 s p n)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = s)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      memLoad32 m'.mem (s + 8) = memLoad32 m.mem (s + 0x10) ∧
      memLoad32 m'.mem (s + 0xC) = memLoad32 m.mem (s + 0x14) ∧
      memLoad32 m'.mem (s + 0x18) = memLoad32 m.mem (s + 0x18) + 1 ∧
      memLoad32 m'.mem (s + 0x10) = ilWord m.mem p n.toNat 0 ∧
      memLoad32 m'.mem (s + 0x14) = ilWord m.mem p n.toNat 1 ∧
      memLoad32 m'.mem (s + 0x0) = (if n = 0 then p else if n.toNat < 8 then 1 else p + 8) ∧
      memLoad32 m'.mem (s + 0x4) = (if n.toNat < 8 then 0 else n - 8) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 → Sep s 28 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFFE0 = G := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFF0 = F := ⟨_, rfl⟩
  have hS := env.hS
  have eGF : G + 0x10 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have eFs : F + 0x10 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have hGn : G.toNat + 0x20 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFFE0 : Word).toNat = 4294967264 from rfl]
    have := sp0.isLt; omega
  have hFn : F.toNat = G.toNat + 0x10 := by
    rw [← eGF, BitVec.toNat_add, show (0x10 : Word).toNat = 16 from rfl]; have := sp0.isLt; omega
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsa (k := 0xFFFFFFE0) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hsa (k := 0xFFFFFFF0) (by decide)
  have sGC := env.sGC; have sGS := env.sGS; have sGB := env.sGB; have sSG := env.sSG; have sPG := env.sPG
  rw [hG] at sGC sGS sGB sSG sPG ⊢
  have sFC : Sep F 16 P incrementLimbCode.length := by rw [← eGF]; exact sGC.sub (c := 0x10) (by decide)
  have sSF : Sep s 28 F 16 := by rw [← eGF]; exact sSG.subR (c := 0x10) (by decide)
  have sFS : ∀ a b : Nat, a + 4 ≤ 16 → b + 4 ≤ 28 → Sep (F + BitVec.ofNat 32 a) 4 (s + BitVec.ofNat 32 b) 4 :=
    fun a b ha hb => by
      have h1 : Sep F 16 s 28 := sSF.symm
      exact (h1.sub (c := a) (l := 4) ha).subR (c := b) (l := 4) hb
  have hc := env.cod
  have st0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := st0.zero
  -- the prologue: save `ra` and `s0`, then `s0 = self`
  obtain ⟨mA, cA, uA⟩ := St.block ilProA st0 hc ilProA_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ilProA, upd_app, ↓reduceIte, and_true]
    rw [ev_add, hsp, hF]
    repeat' apply And.intro
    all_goals first | exact True.intro | exact aligned_add hFa (by decide) | exact sFC.sub (by decide))
  simp only [runBlock, BInstr.run, ilProA] at uA
  have spA : reg mA sp = F := by rw [uA.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  have s0A : reg mA (8 : Fin 32) = s := by
    rw [uA.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, ha0]; exact BitVec.zero_add s
  have kA : ∀ q : Fin 32, q.val ≠ 0 → q ≠ sp → q ≠ (8 : Fin 32) → reg mA q = reg m q := fun q h0 h1 h2 => by
    rw [uA.regs, upd_ne h0 h2, upd_ne h0 h1]
  have MA := uA.mem
  simp +decide only [upd_app, ↓reduceIte] at MA
  rw [ev_add, hsp, hF] at MA
  have frA : ∀ x, Sep F 16 x 1 → mA.mem x = m.mem x := fun x hx => by
    rw [MA, memStore32_get_sep (a := F + 0x8) (hx.sub (c := 8) (by decide)),
      memStore32_get_sep (a := F + 0xC) (hx.sub (c := 0xC) (by decide))]
  have ldA : ∀ k, k + 4 ≤ 28 → memLoad32 mA.mem (s + BitVec.ofNat 32 k) = memLoad32 m.mem (s + BitVec.ofNat 32 k) :=
    fun k h => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact frA _ (sSF.symm.subR (c := k + j) (l := 1) (by omega))
  have hcA : CodeIn mA.mem P incrementLimbCode := by
    rw [MA]; exact (hc.store32 (sFC.sub (c := 0xC) (by decide))).store32 (sFC.sub (c := 8) (by decide))
  have uA' : St mA.mem P mA 0x8 (reg mA) := ⟨uA.pc, rfl, fun _ => rfl⟩
  have a0A : reg mA a0 = s := by rw [kA a0 (by decide) (by decide) (by decide), ha0]
  -- read `cur_idx`, `next_limb`, and the slice length
  obtain ⟨mB, cB, uB⟩ := St.block ilProB uA' hcA ilProB_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ilProB, upd_app, ↓reduceIte, and_true]
    rw [a0A, s0A]
    repeat' apply And.intro
    all_goals exact aligned_add env.hs (by decide))
  simp only [runBlock, BInstr.run, ilProB] at uB
  have L18 : memLoad32 mA.mem (s + 0x18) = memLoad32 m.mem (s + 0x18) := ldA 0x18 (by decide)
  have L10 : memLoad32 mA.mem (s + 0x10) = memLoad32 m.mem (s + 0x10) := ldA 0x10 (by decide)
  have L14 : memLoad32 mA.mem (s + 0x14) = memLoad32 m.mem (s + 0x14) := ldA 0x14 (by decide)
  have L4 : memLoad32 mA.mem (s + 0x4) = n := (ldA 4 (by decide)).trans env.hn
  have L0 : memLoad32 mA.mem (s + 0x0) = p := (ldA 0 (by decide)).trans (by rw [add_ofNat_zero]; exact env.hp)
  have kB : ∀ q : Fin 32, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg mB q = reg mA q :=
    fun q h0 h1 h2 h3 h4 => by rw [uB.regs]; simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3, upd_ne h0 h4]
  have a0B : reg mB a0 = memLoad32 m.mem (s + 0x18) + 1 := by
    rw [uB.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [a0A, L18]; rfl
  have a1B : reg mB a1 = memLoad32 m.mem (s + 0x10) := by
    rw [uB.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [s0A, L10]
  have a3B : reg mB a3 = memLoad32 m.mem (s + 0x14) := by
    rw [uB.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [s0A, L14]
  have a2B : reg mB a2 = n := by rw [uB.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [s0A, L4]
  have s0B : reg mB (8 : Fin 32) = s := by rw [kB _ (by decide) (by decide) (by decide) (by decide) (by decide), s0A]
  have spB : reg mB sp = F := by rw [kB _ (by decide) (by decide) (by decide) (by decide) (by decide), spA]
  have uB' : St mA.mem P mB 0x12 (reg mB) := uB.self
  -- store `cur_limb` and `cur_idx`
  obtain ⟨mC, cC, uC⟩ := St.block ilProC uB' hcA ilProC_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ilProC, and_true]
    rw [s0B]
    repeat' apply And.intro
    all_goals first | exact aligned_add env.hs (by decide) | exact env.sSC.sub (by decide))
  simp only [runBlock, BInstr.run, ilProC] at uC
  have MC := uC.mem
  rw [s0B, a1B, a3B, a0B] at MC
  have rC : ∀ q, reg mC q = reg mB q := uC.regs
  have hcC : CodeIn mC.mem P incrementLimbCode := by
    rw [MC]; exact ((hcA.store32 (env.sSC.sub (c := 8) (by decide))).store32 (env.sSC.sub (c := 0xC) (by decide))).store32
      (env.sSC.sub (c := 0x18) (by decide))
  have uC' : St mC.mem P mC 0x18 (reg mC) := ⟨uC.pc, rfl, fun _ => rfl⟩
  have keepC : ∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg mC q = reg m q :=
    fun q hq => by
      obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ sp ∧
          q ≠ (8 : Fin 32) := by revert hq; revert q; decide
      rw [rC, kB q h0 h1 h2 h3 h4, kA q h0 h5 h6]
  have frC : ∀ x, Sep G 0x20 x 1 → Sep s 28 x 1 → mC.mem x = m.mem x := fun x hg hs => by
    rw [MC, memStore32_get_sep (a := s + 0x18) (hs.sub (c := 0x18) (by decide)),
      memStore32_get_sep (a := s + 0xC) (hs.sub (c := 0xC) (by decide)),
      memStore32_get_sep (a := s + 0x8) (hs.sub (c := 8) (by decide)), frA x (by rw [← eGF]; exact hg.sub (by decide))]
  have stF : ∀ k, k + 4 ≤ 16 → memLoad32 mC.mem (F + BitVec.ofNat 32 k) = memLoad32 mA.mem (F + BitVec.ofNat 32 k) :=
    fun k hk => by
      rw [MC, memLoad32_store32_sep (a := s + 0x18) (b := F + BitVec.ofNat 32 k) (sFS k 0x18 hk (by decide)).symm,
        memLoad32_store32_sep (a := s + 0xC) (b := F + BitVec.ofNat 32 k) (sFS k 0xC hk (by decide)).symm,
        memLoad32_store32_sep (a := s + 0x8) (b := F + BitVec.ofNat 32 k) (sFS k 8 hk (by decide)).symm]
  have raC : memLoad32 mC.mem (F + 0xC) = retAddr := by
    have h : memLoad32 mC.mem (F + 0xC) = memLoad32 mA.mem (F + 0xC) := stF 0xC (by decide)
    rw [h, MA,
      memLoad32_store32_sep (a := F + 0x8) (b := F + 0xC) (sep_offsets F (.inl (by decide)) (by decide) (by decide)),
      memLoad32_store32_same, hra]
  have s8C : memLoad32 mC.mem (F + 0x8) = reg m (8 : Fin 32) := by
    have h : memLoad32 mC.mem (F + 0x8) = memLoad32 mA.mem (F + 0x8) := stF 8 (by decide)
    rw [h, MA, memLoad32_store32_same]
  -- the words of the struct after the prologue
  have W8 : memLoad32 mC.mem (s + 0x8) = memLoad32 m.mem (s + 0x10) := by
    rw [MC, ld_st_off 0x18 0x8 (by decide) (by decide) (by decide), ld_st_off 0xC 0x8 (by decide) (by decide) (by decide),
      memLoad32_store32_same]
  have WC : memLoad32 mC.mem (s + 0xC) = memLoad32 m.mem (s + 0x14) := by
    rw [MC, ld_st_off 0x18 0xC (by decide) (by decide) (by decide), memLoad32_store32_same]
  have W18 : memLoad32 mC.mem (s + 0x18) = memLoad32 m.mem (s + 0x18) + 1 := by rw [MC, memLoad32_store32_same]
  have Wst : ∀ d : Word, ((0x8 : Word).toNat == d.toNat) = false → ((0xC : Word).toNat == d.toNat) = false →
      ((0x18 : Word).toNat == d.toNat) = false → d.toNat % 4 = 0 →
      memLoad32 mC.mem (s + d) = memLoad32 mA.mem (s + d) := fun d h1 h2 h3 hd => by
    rw [MC, ld_st_off 0x18 d h3 (by decide) hd, ld_st_off 0xC d h2 (by decide) hd, ld_st_off 0x8 d h1 (by decide) hd]
  have W0 : memLoad32 mC.mem (s + 0x0) = p := (Wst 0 (by decide) (by decide) (by decide) (by decide)).trans L0
  have W4 : memLoad32 mC.mem (s + 0x4) = n := (Wst 4 (by decide) (by decide) (by decide) (by decide)).trans L4
  have W10 : memLoad32 mC.mem (s + 0x10) = memLoad32 m.mem (s + 0x10) :=
    (Wst 0x10 (by decide) (by decide) (by decide) (by decide)).trans L10
  have W14 : memLoad32 mC.mem (s + 0x14) = memLoad32 m.mem (s + 0x14) :=
    (Wst 0x14 (by decide) (by decide) (by decide) (by decide)).trans L14
  -- the epilogue, for each way to reach it
  have fin : ∀ (mX : Machine) (f : Fin 32 → Word) (M : Word → BitVec 8), Steps m mX → St M P mX 0x98 f →
      CodeIn M P incrementLimbCode → f sp = F →
      (∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → f q = reg m q) →
      memLoad32 M (F + 0xC) = retAddr → memLoad32 M (F + 0x8) = reg m (8 : Fin 32) →
      memLoad32 M (s + 8) = memLoad32 m.mem (s + 0x10) →
      memLoad32 M (s + 0xC) = memLoad32 m.mem (s + 0x14) →
      memLoad32 M (s + 0x18) = memLoad32 m.mem (s + 0x18) + 1 →
      memLoad32 M (s + 0x10) = ilWord m.mem p n.toNat 0 →
      memLoad32 M (s + 0x14) = ilWord m.mem p n.toNat 1 →
      memLoad32 M (s + 0x0) = (if n = 0 then p else if n.toNat < 8 then 1 else p + 8) →
      memLoad32 M (s + 0x4) = (if n.toNat < 8 then 0 else n - 8) →
      (∀ x, Sep G 0x20 x 1 → Sep s 28 x 1 → M x = m.mem x) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        memLoad32 m'.mem (s + 8) = memLoad32 m.mem (s + 0x10) ∧
        memLoad32 m'.mem (s + 0xC) = memLoad32 m.mem (s + 0x14) ∧
        memLoad32 m'.mem (s + 0x18) = memLoad32 m.mem (s + 0x18) + 1 ∧
        memLoad32 m'.mem (s + 0x10) = ilWord m.mem p n.toNat 0 ∧
        memLoad32 m'.mem (s + 0x14) = ilWord m.mem p n.toNat 1 ∧
        memLoad32 m'.mem (s + 0x0) = (if n = 0 then p else if n.toNat < 8 then 1 else p + 8) ∧
        memLoad32 m'.mem (s + 0x4) = (if n.toNat < 8 then 0 else n - 8) ∧
        ∀ x, Sep G 0x20 x 1 → Sep s 28 x 1 → m'.mem x = m.mem x := by
    intro mX f M cX tX hcX hspX kX h1 h2 w8 wC w18 w10 w14 w0 w4 frX
    obtain ⟨m', c', pc', mem', sp', ra', s0', k'⟩ := il_epilogue hcX tX hspX hFa h1 h2 hret
    refine ⟨m', cX.trans c', pc', by rw [sp', eFs], fun q hq => ?_, by rw [mem']; exact w8, by rw [mem']; exact wC,
      by rw [mem']; exact w18, by rw [mem']; exact w10, by rw [mem']; exact w14, by rw [mem']; exact w0,
      by rw [mem']; exact w4, fun x hg hs => by rw [mem']; exact frX x hg hs⟩
    have key : q = ra ∨ q = (8 : Fin 32) ∨
        (q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q ≠ sp ∧ q ≠ ra ∧ q ≠ (8 : Fin 32)) := by
      revert hq; revert q; decide
    rcases key with rfl | rfl | ⟨h1, h2, h3, h4⟩
    · rw [ra', hra]
    · exact s0'
    · rw [k' q h2 h3 h4, kX q h1]
  have hz0 : reg mC x0 = 0 := uC'.zero
  by_cases hn0 : n = 0
  · -- an empty slice: `next_limb = 0`
    obtain ⟨n1, d1, u1⟩ := uC'.taken hcC 0x42 il_at_18 (by decide) (by
      rw [rC, a2B, hz0, hn0]; rfl)
    obtain ⟨mZ, cZ, uZ⟩ := St.block ilZero u1 hcC ilZero_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, ilZero, upd_app, ↓reduceIte, and_true]
      rw [rC, s0B]
      repeat' apply And.intro
      all_goals first | exact True.intro | exact aligned_add env.hs (by decide) | exact env.sSC.sub (by decide))
    simp only [runBlock, BInstr.run, ilZero] at uZ
    have MZ := uZ.mem
    simp +decide only [upd_app, ↓reduceIte] at MZ
    rw [rC, s0B, hz0, show aluEval .add (0 : Word) 0x0 = 0 from rfl] at MZ
    have hcZ : CodeIn mZ.mem P incrementLimbCode := by
      rw [MZ]; exact (hcC.store32 (env.sSC.sub (c := 0x10) (by decide))).store32 (env.sSC.sub (c := 0x14) (by decide))
    have uZ' : St mZ.mem P mZ 0x48 (reg mZ) := ⟨uZ.pc, rfl, fun _ => rfl⟩
    obtain ⟨n2, d2, u2⟩ := uZ'.jump hcZ il_at_48 (off' := 0x98) (by decide) (by
      rw [uZ.pc, show P + BitVec.ofNat 32 0x48 + 0x50 = P + BitVec.ofNat 32 0x98 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0x98 (by decide)))
    have ldZ : ∀ d : Word, ((0x10 : Word).toNat == d.toNat) = false → ((0x14 : Word).toNat == d.toNat) = false →
        d.toNat % 4 = 0 → memLoad32 mZ.mem (s + d) = memLoad32 mC.mem (s + d) := fun d h1 h2 hd => by
      rw [MZ, ld_st_off 0x14 d h2 (by decide) hd, ld_st_off 0x10 d h1 (by decide) hd]
    have stZ : ∀ k, k + 4 ≤ 16 → memLoad32 mZ.mem (F + BitVec.ofNat 32 k) = memLoad32 mC.mem (F + BitVec.ofNat 32 k) :=
      fun k hk => by
        rw [MZ, memLoad32_store32_sep (a := s + 0x14) (b := F + BitVec.ofNat 32 k) (sFS k 0x14 hk (by decide)).symm,
          memLoad32_store32_sep (a := s + 0x10) (b := F + BitVec.ofNat 32 k) (sFS k 0x10 hk (by decide)).symm]
    have z0 : ∀ j, j < 2 → ilWord m.mem p n.toNat j = 0 := fun j hj => by
      rw [hn0]; unfold ilWord ilByte; simp only [show (0 : Word).toNat = 0 from rfl, Nat.not_lt_zero, ite_false]; rfl
    have e1 : memLoad32 mZ.mem (F + 0xC) = retAddr := by
      have h : memLoad32 mZ.mem (F + 0xC) = memLoad32 mC.mem (F + 0xC) := stZ 0xC (by decide)
      rw [h]; exact raC
    have e2 : memLoad32 mZ.mem (F + 0x8) = reg m (8 : Fin 32) := by
      have h : memLoad32 mZ.mem (F + 0x8) = memLoad32 mC.mem (F + 0x8) := stZ 8 (by decide)
      rw [h]; exact s8C
    have e3 : memLoad32 mZ.mem (s + 8) = memLoad32 m.mem (s + 0x10) := by
      rw [ldZ 8 (by decide) (by decide) (by decide)]; exact W8
    have e4 : memLoad32 mZ.mem (s + 0xC) = memLoad32 m.mem (s + 0x14) := by
      rw [ldZ 0xC (by decide) (by decide) (by decide)]; exact WC
    have e5 : memLoad32 mZ.mem (s + 0x18) = memLoad32 m.mem (s + 0x18) + 1 := by
      rw [ldZ 0x18 (by decide) (by decide) (by decide)]; exact W18
    have e6 : memLoad32 mZ.mem (s + 0x10) = ilWord m.mem p n.toNat 0 := by
      rw [MZ, ld_st_off 0x14 0x10 (by decide) (by decide) (by decide), memLoad32_store32_same, z0 0 (by decide)]
    have e7 : memLoad32 mZ.mem (s + 0x14) = ilWord m.mem p n.toNat 1 := by
      rw [MZ, memLoad32_store32_same, z0 1 (by decide)]
    have e8 : memLoad32 mZ.mem (s + 0x0) = (if n = 0 then p else if n.toNat < 8 then 1 else p + 8) := by
      rw [ldZ 0 (by decide) (by decide) (by decide), W0, ite_eq_left hn0]
    have e9 : memLoad32 mZ.mem (s + 0x4) = (if n.toNat < 8 then 0 else n - 8) := by
      rw [ldZ 4 (by decide) (by decide) (by decide), W4, ite_eq_left (by rw [hn0]; decide), hn0]
    have e10 : ∀ x, Sep G 0x20 x 1 → Sep s 28 x 1 → mZ.mem x = m.mem x := fun x hg hs => by
      rw [MZ, memStore32_get_sep (a := s + 0x14) (hs.sub (c := 0x14) (by decide)),
        memStore32_get_sep (a := s + 0x10) (hs.sub (c := 0x10) (by decide)), frC x hg hs]
    have S : Steps m n2 := cA.trans (cB.trans (cC.trans (.cons d1 (cZ.trans (.single d2)))))
    refine fin n2 (reg mZ) mZ.mem S u2 hcZ ?_ ?_ e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    · rw [uZ.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rC, spB]
    · intro q hq
      obtain ⟨h0, h1⟩ : q.val ≠ 0 ∧ q ≠ a0 := by revert hq; revert q; decide
      rw [uZ.regs, upd_ne h0 h1]; exact keepC q hq
  · -- a nonempty slice: `7 < n` picks the 8-byte read
    obtain ⟨n1, d1, u1⟩ := uC'.notTaken hcC 0x1A il_at_18 (by decide) (by
      rw [rC, a2B, hz0]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; exact hn0)
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hcC il_at_1a (off' := 0x1C) (by decide)
    have r2 : ∀ q, reg n2 q = upd (reg mC) a0 (aluEval .add (reg mC x0) 0x7) q := u2.regs
    have a0_2 : reg n2 a0 = 7 := by rw [r2]; simp +decide only [upd_app, ↓reduceIte]; rw [hz0]; rfl
    have a2_2 : reg n2 a2 = n := by rw [r2]; simp +decide only [upd_app, ↓reduceIte]; rw [rC, a2B]
    have s0_2 : reg n2 (8 : Fin 32) = s := by rw [r2]; simp +decide only [upd_app, ↓reduceIte]; rw [rC, s0B]
    have sp_2 : reg n2 sp = F := by rw [r2]; simp +decide only [upd_app, ↓reduceIte]; rw [rC, spB]
    have k2 : ∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n2 q = reg m q :=
      fun q hq => by
        obtain ⟨h0, h1⟩ : q.val ≠ 0 ∧ q ≠ a0 := by revert hq; revert q; decide
        rw [r2, upd_ne h0 h1]; exact keepC q hq
    have u2' : St mC.mem P n2 0x1C (reg n2) := u2.self
    by_cases hlt : n.toNat < 8
    · -- 1 to 7 bytes: zero an 8-byte stack buffer and `memcpy` the slice into it
      have hN0 : n.toNat ≠ 0 := fun h => hn0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      obtain ⟨N, hNe⟩ : ∃ N, n.toNat = N := ⟨_, rfl⟩
      have pN : min n.toNat 8 = N := by omega
      have sPS := env.sPS
      have hpw := env.hpw
      rw [pN] at sPG sPS hpw
      obtain ⟨n3, d3, u3⟩ := u2'.notTaken hcC 0x20 il_at_1c (by decide) (by
        rw [a0_2, a2_2]; show decide ((7 : Word).toNat < n.toNat) = false
        exact decide_eq_false (by show ¬ 7 < n.toNat; omega))
      obtain ⟨mP, cP, uP⟩ := St.block ilCp u3 hcC ilCp_end (by
        simp +decide only [BlockOk, BInstr.ok, BInstr.run, ilCp, upd_app, ↓reduceIte, and_true]
        rw [s0_2, sp_2]
        repeat' apply And.intro
        all_goals first | exact True.intro | exact aligned_add env.hs (by decide) | exact aligned_add hFa (by decide) |
          exact sFC.sub (by decide))
      simp only [runBlock, BInstr.run, ilCp] at uP
      have MP := uP.mem
      simp +decide only [upd_app, ↓reduceIte] at MP
      rw [sp_2, show F + (0x0 : Word) = F from BitVec.add_zero F] at MP
      have Pa0 : reg mP a0 = F := by
        rw [uP.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp_2]; exact BitVec.zero_add F
      have Pa1 : reg mP a1 = p := by rw [uP.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [s0_2, W0]
      have Pa2 : reg mP a2 = n := by rw [uP.regs]; simp +decide only [upd_app, ↓reduceIte]; exact a2_2
      have kP : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg mP q = reg n2 q :=
        fun q hq => by
          obtain ⟨h0, h1, h2⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 := by revert hq; revert q; decide
          rw [uP.regs, upd_ne h0 h1, upd_ne h0 h2]
      have sepF : ∀ x, Sep G 0x20 x 1 → Sep F 16 x 1 := fun x hg => by rw [← eGF]; exact hg.sub (c := 0x10) (by decide)
      have frPs : ∀ x, Sep F 16 x 1 → mP.mem x = mC.mem x := fun x hx => by
        have h0 : Sep F 4 x 1 := fun i hi j hj => hx i (by omega) j hj
        rw [MP, memStore32_get_sep (a := F + 0x4) (hx.sub (c := 4) (by decide)), memStore32_get_sep h0]
      have cIn : ∀ (b : Word) (code : List Nat), CodeIn m.mem b code → Sep G 0x20 b code.length →
          Sep s 28 b code.length → CodeIn mP.mem b code := fun b code hcb hg hs i hi => by
        rw [frPs _ (sepF _ (hg.subR (c := i) (l := 1) (by omega))),
          frC _ (hg.subR (c := i) (l := 1) (by omega)) (hs.subR (c := i) (l := 1) (by omega))]
        exact hcb i hi
      have hcP : CodeIn mP.mem P incrementLimbCode := cIn _ _ hc sGC env.sSC
      have uP' : St mP.mem P mP 0x28 (reg mP) := ⟨uP.pc, rfl, fun _ => rfl⟩
      obtain ⟨n6, c6, pc6, mem6, regs6⟩ := uP'.callRa hcP il_at_28 il_at_2c (cb := P + 0x128)
        (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x128 (by decide))
      have r6 : ∀ q, q ≠ ra → reg n6 q = reg mP q := fun q h => by rw [regs6]; exact updz uP'.zero h
      have sp6 : reg n6 sp = F := by rw [r6 sp (by decide), kP sp (by decide), sp_2]
      have eG : F + 0xFFFFFFF0 = G := by rw [← eGF, BitVec.add_assoc]; exact BitVec.add_zero G
      have hN8 : N < 8 := by omega
      have E : McEnv n6.mem (P + 0x128 + 8) F p (reg n6 sp + 0xFFFFFFF0) N := by
        rw [sp6, eG, mem6]
        refine ⟨cIn _ _ env.mcB sGB env.sSB, ?_, fun i hi j hj => sGB i (by omega) j hj, ?_,
          fun i hi j hj => sPG i hi j (by omega), ?_, hGa, by have := sp0.isLt; omega,
          by have := sp0.isLt; omega, hpw⟩
        · rw [← eGF]; exact sGB.sub (c := 0x10) (l := N) (by omega)
        · rw [← eGF]
          have := sep_offsets G (c := 0x10) (n := N) (d := 0) (k := 16) (.inr (by omega)) (by omega) (by omega)
          rwa [add_ofNat_zero] at this
        · rw [← eGF]; exact sPG.symm.sub (c := 0x10) (l := N) (by omega)
      obtain ⟨m7, c7, pc7, sp7, _, f7, k7⟩ := memcpy_correct n6 (P + 0x128) (P + BitVec.ofNat 32 (0x28 + 8)) F p N
        (fun i hi => by rw [mem6]; exact cIn _ _ env.mcS sGS env.sSS i hi) (even_at P env.hP 0x128 (by decide)) pc6
        (by rw [r6 a0 (by decide), Pa0]) (by rw [r6 a1 (by decide), Pa1])
        (by rw [r6 a2 (by decide), Pa2, ← ofNat_toNat_self n, hNe])
        (by rw [regs6]; simp +decide only [upd_app, ↓reduceIte])
        (even_clear _ (even_at P env.hP (0x28 + 8) (by decide))) E
      rw [sp6, eG, mem6] at f7
      have fr7 : ∀ x, Sep G 0x20 x 1 → m7.mem x = mP.mem x := fun x hg => by
        rw [f7 x (fun i hi j hj => hg i (by omega) j hj),
          copyBytes_sep (n := N) (fun i hi j hj => sepF x hg i (by omega) j hj) (Nat.le_refl N)]
      have gF : ∀ j, j < 16 → Sep G 16 (F + BitVec.ofNat 32 j) 1 := fun j hj => by
        have e : F + BitVec.ofNat 32 j = G + BitVec.ofNat 32 (16 + j) := by rw [← eGF]; exact add_ofNat_assoc G 16 j
        rw [e]
        have := sep_offsets G (c := 0) (n := 16) (d := 16 + j) (k := 1) (.inl (by omega)) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
      have zF : ∀ j, j < 8 → mP.mem (F + BitVec.ofNat 32 j) = 0 := fun j hj => by
        have s4 : ∀ i, i < 4 → Sep (F + 0x4) 4 (F + BitVec.ofNat 32 i) 1 := fun i hi =>
          sep_offsets F (c := 4) (n := 4) (d := i) (k := 1) (.inr (by omega)) (by omega) (by omega)
        match j, hj with
        | 0, _ => rw [MP, memStore32_get_sep (s4 0 (by decide)), store32_byte _ F 0 0 (by decide)]; rfl
        | 1, _ => rw [MP, memStore32_get_sep (s4 1 (by decide)), store32_byte _ F 0 1 (by decide)]; rfl
        | 2, _ => rw [MP, memStore32_get_sep (s4 2 (by decide)), store32_byte _ F 0 2 (by decide)]; rfl
        | 3, _ => rw [MP, memStore32_get_sep (s4 3 (by decide)), store32_byte _ F 0 3 (by decide)]; rfl
        | 4, _ =>
          rw [MP, show F + BitVec.ofNat 32 4 = F + 0x4 + BitVec.ofNat 32 0 by rw [BitVec.add_assoc]; rfl,
            store32_byte _ _ 0 0 (by decide)]; rfl
        | 5, _ =>
          rw [MP, show F + BitVec.ofNat 32 5 = F + 0x4 + BitVec.ofNat 32 1 by rw [BitVec.add_assoc]; rfl,
            store32_byte _ _ 0 1 (by decide)]; rfl
        | 6, _ =>
          rw [MP, show F + BitVec.ofNat 32 6 = F + 0x4 + BitVec.ofNat 32 2 by rw [BitVec.add_assoc]; rfl,
            store32_byte _ _ 0 2 (by decide)]; rfl
        | 7, _ =>
          rw [MP, show F + BitVec.ofNat 32 7 = F + 0x4 + BitVec.ofNat 32 3 by rw [BitVec.add_assoc]; rfl,
            store32_byte _ _ 0 3 (by decide)]; rfl
      have bF : ∀ j, j < 8 → m7.mem (F + BitVec.ofNat 32 j) = ilByte m.mem p n.toNat j := fun j hj => by
        rw [f7 _ (gF j (by omega))]
        unfold ilByte
        by_cases hjN : j < N
        · rw [copyBytes_in hjN (by omega), ite_eq_left (by omega),
            frPs _ (sepF _ (sPG.symm.subR (c := j) (l := 1) (by omega))),
            frC _ (sPG.symm.subR (c := j) (l := 1) (by omega)) (sPS.symm.subR (c := j) (l := 1) (by omega))]
        · rw [copyBytes_past (by omega) (by omega), ite_eq_right (by omega), zF j hj]
      have w7 : ∀ k, k < 2 → memLoad32 m7.mem (F + BitVec.ofNat 32 (4 * k)) = ilWord m.mem p n.toNat k := fun k hk => by
        apply BitVec.eq_of_toNat_eq
        rw [memLoad32_toNat, ilWord_toNat,
          show F + BitVec.ofNat 32 (4 * k) + 1 = F + BitVec.ofNat 32 (4 * k + 1) from add_ofNat_assoc F _ 1,
          show F + BitVec.ofNat 32 (4 * k) + 2 = F + BitVec.ofNat 32 (4 * k + 2) from add_ofNat_assoc F _ 2,
          show F + BitVec.ofNat 32 (4 * k) + 3 = F + BitVec.ofNat 32 (4 * k + 3) from add_ofNat_assoc F _ 3,
          bF _ (by omega), bF _ (by omega), bF _ (by omega), bF _ (by omega)]
      have ldF7 : ∀ k, 8 ≤ k → k + 4 ≤ 16 → memLoad32 m7.mem (F + BitVec.ofNat 32 k) = memLoad32 mC.mem (F + BitVec.ofNat 32 k) :=
        fun k hk1 hk2 => memLoad32_congr fun j hj => by
          have s0' : Sep F 4 (F + BitVec.ofNat 32 (k + j)) 1 := by
            have := sep_offsets F (c := 0) (n := 4) (d := k + j) (k := 1) (.inl (by omega)) (by omega) (by omega)
            rwa [add_ofNat_zero] at this
          rw [add_ofNat_assoc, f7 _ (gF (k + j) (by omega)), copyBytes_past (by omega) (by omega), MP,
            memStore32_get_sep (a := F + 0x4)
              (sep_offsets F (c := 4) (n := 4) (d := k + j) (k := 1) (.inl (by omega)) (by omega) (by omega)),
            memStore32_get_sep s0']
      have ld7 : ∀ k, k + 4 ≤ 28 → memLoad32 m7.mem (s + BitVec.ofNat 32 k) = memLoad32 mC.mem (s + BitVec.ofNat 32 k) :=
        fun k hk => memLoad32_congr fun j hj => by
          rw [add_ofNat_assoc, fr7 _ (sSG.symm.subR (c := k + j) (l := 1) (by omega)),
            frPs _ (sSF.symm.subR (c := k + j) (l := 1) (by omega))]
      have s07 : reg m7 (8 : Fin 32) = s := by
        rw [k7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r6 _ (by decide), kP _ (by decide), s0_2]
      have sp7' : reg m7 sp = F := by rw [sp7, sp6]
      have hc7 : CodeIn m7.mem P incrementLimbCode := fun i hi => by
        rw [fr7 _ (sGC.subR (c := i) (l := 1) (by omega))]; exact hcP i hi
      have u7 : St m7.mem P m7 0x30 (reg m7) := ⟨pc7, rfl, fun _ => rfl⟩
      obtain ⟨mE, cE, uE⟩ := St.block ilCpEnd u7 hc7 ilCpEnd_end (by
        simp +decide only [BlockOk, BInstr.ok, BInstr.run, ilCpEnd, upd_app, ↓reduceIte, and_true]
        rw [s07, sp7']
        repeat' apply And.intro
        all_goals first | exact True.intro | exact aligned_add env.hs (by decide) | exact aligned_add hFa (by decide) |
          exact env.sSC.sub (by decide))
      simp only [runBlock, BInstr.run, ilCpEnd] at uE
      have ME := uE.mem
      simp +decide only [upd_app, ↓reduceIte] at ME
      rw [s07, sp7', show aluEval .add (0 : Word) 0x1 = 1 from rfl] at ME
      have W0' : memLoad32 m7.mem (F + 0x0) = ilWord m.mem p n.toNat 0 := w7 0 (by decide)
      have W1' : memLoad32 m7.mem (F + 0x4) = ilWord m.mem p n.toNat 1 := w7 1 (by decide)
      rw [W0', W1'] at ME
      have hcE : CodeIn mE.mem P incrementLimbCode := by
        rw [ME]; exact (((hc7.store32 (env.sSC.sub (c := 0) (by decide))).store32 (env.sSC.sub (c := 4) (by decide))).store32
          (env.sSC.sub (c := 0x10) (by decide))).store32 (env.sSC.sub (c := 0x14) (by decide))
      have uE' : St mE.mem P mE 0x40 (reg mE) := ⟨uE.pc, rfl, fun _ => rfl⟩
      obtain ⟨n8, d8, u8⟩ := uE'.jump hcE il_at_40 (off' := 0x98) (by decide) (by
        rw [uE'.pc, show P + BitVec.ofNat 32 0x40 + 0x58 = P + BitVec.ofNat 32 0x98 by rw [BitVec.add_assoc]; rfl]
        exact even_bit0 (even_at P env.hP 0x98 (by decide)))
      have ldE : ∀ d : Word, ((0x0 : Word).toNat == d.toNat) = false → ((0x4 : Word).toNat == d.toNat) = false →
          ((0x10 : Word).toNat == d.toNat) = false → ((0x14 : Word).toNat == d.toNat) = false → d.toNat % 4 = 0 →
          memLoad32 mE.mem (s + d) = memLoad32 m7.mem (s + d) := fun d h1 h2 h3 h4 hd => by
        rw [ME, ld_st_off 0x14 d h4 (by decide) hd, ld_st_off 0x10 d h3 (by decide) hd, ld_st_off 0x4 d h2 (by decide) hd,
          ld_st_off 0x0 d h1 (by decide) hd]
      have stE : ∀ k, k + 4 ≤ 16 → memLoad32 mE.mem (F + BitVec.ofNat 32 k) = memLoad32 m7.mem (F + BitVec.ofNat 32 k) :=
        fun k hk => by
          rw [ME, memLoad32_store32_sep (a := s + 0x14) (b := F + BitVec.ofNat 32 k) (sFS k 0x14 hk (by decide)).symm,
            memLoad32_store32_sep (a := s + 0x10) (b := F + BitVec.ofNat 32 k) (sFS k 0x10 hk (by decide)).symm,
            memLoad32_store32_sep (a := s + 0x4) (b := F + BitVec.ofNat 32 k) (sFS k 0x4 hk (by decide)).symm,
            memLoad32_store32_sep (a := s + 0x0) (b := F + BitVec.ofNat 32 k) (sFS k 0x0 hk (by decide)).symm]
      have e1 : memLoad32 mE.mem (F + 0xC) = retAddr := by
        have h : memLoad32 mE.mem (F + 0xC) = memLoad32 mC.mem (F + 0xC) :=
          (stE 0xC (by decide)).trans (ldF7 0xC (by decide) (by decide))
        rw [h]; exact raC
      have e2 : memLoad32 mE.mem (F + 0x8) = reg m (8 : Fin 32) := by
        have h : memLoad32 mE.mem (F + 0x8) = memLoad32 mC.mem (F + 0x8) :=
          (stE 8 (by decide)).trans (ldF7 8 (by decide) (by decide))
        rw [h]; exact s8C
      have e3 : memLoad32 mE.mem (s + 8) = memLoad32 m.mem (s + 0x10) := by
        have h : memLoad32 m7.mem (s + 0x8) = memLoad32 mC.mem (s + 0x8) := ld7 8 (by decide)
        rw [ldE 8 (by decide) (by decide) (by decide) (by decide) (by decide), h]; exact W8
      have e4 : memLoad32 mE.mem (s + 0xC) = memLoad32 m.mem (s + 0x14) := by
        have h : memLoad32 m7.mem (s + 0xC) = memLoad32 mC.mem (s + 0xC) := ld7 0xC (by decide)
        rw [ldE 0xC (by decide) (by decide) (by decide) (by decide) (by decide), h]; exact WC
      have e5 : memLoad32 mE.mem (s + 0x18) = memLoad32 m.mem (s + 0x18) + 1 := by
        have h : memLoad32 m7.mem (s + 0x18) = memLoad32 mC.mem (s + 0x18) := ld7 0x18 (by decide)
        rw [ldE 0x18 (by decide) (by decide) (by decide) (by decide) (by decide), h]; exact W18
      have e6 : memLoad32 mE.mem (s + 0x10) = ilWord m.mem p n.toNat 0 := by
        rw [ME, ld_st_off 0x14 0x10 (by decide) (by decide) (by decide), memLoad32_store32_same]
      have e7 : memLoad32 mE.mem (s + 0x14) = ilWord m.mem p n.toNat 1 := by
        rw [ME, memLoad32_store32_same]
      have e8 : memLoad32 mE.mem (s + 0x0) = (if n = 0 then p else if n.toNat < 8 then 1 else p + 8) := by
        rw [ME, ld_st_off 0x14 0x0 (by decide) (by decide) (by decide), ld_st_off 0x10 0x0 (by decide) (by decide) (by decide),
          ld_st_off 0x4 0x0 (by decide) (by decide) (by decide), memLoad32_store32_same, ite_eq_right hn0, ite_eq_left hlt]
      have e9 : memLoad32 mE.mem (s + 0x4) = (if n.toNat < 8 then 0 else n - 8) := by
        rw [ME, ld_st_off 0x14 0x4 (by decide) (by decide) (by decide), ld_st_off 0x10 0x4 (by decide) (by decide) (by decide),
          memLoad32_store32_same, ite_eq_left hlt]
      have e10 : ∀ x, Sep G 0x20 x 1 → Sep s 28 x 1 → mE.mem x = m.mem x := fun x hg hs => by
        rw [ME, memStore32_get_sep (a := s + 0x14) (hs.sub (c := 0x14) (by decide)),
          memStore32_get_sep (a := s + 0x10) (hs.sub (c := 0x10) (by decide)),
          memStore32_get_sep (a := s + 0x4) (hs.sub (c := 0x4) (by decide)),
          memStore32_get_sep (a := s + 0x0) (hs.sub (c := 0x0) (by decide)), fr7 x hg, frPs x (sepF x hg), frC x hg hs]
      have S : Steps m n8 := cA.trans (cB.trans (cC.trans (.cons d1 (.cons d2 (.cons d3 (cP.trans (c6.trans
        (c7.trans (cE.trans (.single d8))))))))))
      refine fin n8 (reg mE) mE.mem S u8 hcE ?_ ?_ e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
      · rw [uE.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp7'
      · intro q hq
        have hq' : q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
        obtain ⟨h0, h1, h2, h3, hr, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧
            q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧
            q ≠ (7 : Fin 32) ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ sp := by
          clear hq'; revert hq; revert q; decide
        rw [uE.regs]; simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3]
        rw [k7 q h2 h3 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14, r6 q hr, kP q hq']
        exact k2 q hq
    · -- at least 8 bytes: read them in place
      obtain ⟨n3, d3, u3⟩ := u2'.taken hcC 0x4A il_at_1c (by decide) (by
        rw [a0_2, a2_2]; show decide ((7 : Word).toNat < n.toNat) = true
        exact decide_eq_true (by show 7 < n.toNat; omega))
      have p8 : min n.toNat 8 = 8 := by omega
      have sPS := env.sPS
      rw [p8] at sPG sPS
      have pB : ∀ k, k < 8 → mC.mem (p + BitVec.ofNat 32 k) = m.mem (p + BitVec.ofNat 32 k) := fun k hk =>
        frC _ (sPG.symm.subR (c := k) (l := 1) (by omega)) (sPS.symm.subR (c := k) (l := 1) (by omega))
      have ilB : ∀ k, k < 8 → ilByte m.mem p n.toNat k = mC.mem (p + BitVec.ofNat 32 k) := fun k hk => by
        unfold ilByte; rw [ite_eq_left (by omega), pB k hk]
      obtain ⟨mRA, cRA, uRA⟩ := St.block ilRdA u3 hcC ilRdA_end (by
        simp +decide only [BlockOk, BInstr.ok, ilRdA, and_true]
        rw [s0_2]
        repeat' apply And.intro
        all_goals first | exact True.intro | exact aligned_add env.hs (by decide))
      simp only [runBlock, BInstr.run, ilRdA] at uRA
      have RA : ∀ (r : Fin 32) (o : Word), (r, o) ∈ [((17 : Fin 32), (0x5 : Word)), (a3, 0x6), (a4, 0x7), (a6, 0x0),
          ((5 : Fin 32), 0x1), (a1, 0x3), (a5, 0x2), ((6 : Fin 32), 0x4)] →
          reg mRA r = (mC.mem (p + o)).zeroExtend 32 := fun r o h => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ <;>
        · rw [uRA.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [s0_2, W0]
      have RA0 : reg mRA a0 = p + 8 := by
        rw [uRA.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [s0_2, W0]; rfl
      have RA7 : reg mRA (7 : Fin 32) = n - 8 := by
        rw [uRA.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [a2_2, BitVec.sub_eq_add_neg]; rfl
      have kRA : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg mRA q = reg n2 q :=
        fun q hq => by
          obtain ⟨h0, n0, n1, n2', n3', n4, n5, n6, n7, n8, n9⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ (17 : Fin 32) ∧ q ≠ a3 ∧
              q ≠ a4 ∧ q ≠ a6 ∧ q ≠ (5 : Fin 32) ∧ q ≠ a1 ∧ q ≠ a5 ∧ q ≠ (6 : Fin 32) ∧ q ≠ (7 : Fin 32) := by
            revert hq; revert q; decide
          rw [uRA.regs]; simp only [upd_ne h0 n0, upd_ne h0 n1, upd_ne h0 n2', upd_ne h0 n3', upd_ne h0 n4,
            upd_ne h0 n5, upd_ne h0 n6, upd_ne h0 n7, upd_ne h0 n8, upd_ne h0 n9]
      obtain ⟨mRB, cRB, uRB⟩ := St.block ilRdB uRA.self hcC ilRdB_end (by
        simp +decide only [BlockOk, BInstr.ok, ilRdB, and_true])
      simp only [runBlock, BInstr.run, ilRdB] at uRB
      have RB1 : reg mRB a1 = ilWord m.mem p n.toNat 0 := by
        rw [uRB.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [RA a1 0x3 (by decide), RA a5 0x2 (by decide), RA (5 : Fin 32) 0x1 (by decide), RA a6 0x0 (by decide)]
        apply BitVec.eq_of_toNat_eq
        rw [le4_hiLo, ilWord_toNat, ilB (4 * 0) (by decide), ilB (4 * 0 + 1) (by decide), ilB (4 * 0 + 2) (by decide),
          ilB (4 * 0 + 3) (by decide)]
        rfl
      have RB3 : reg mRB a3 = ilWord m.mem p n.toNat 1 := by
        rw [uRB.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [RA a3 0x6 (by decide), RA a4 0x7 (by decide), RA (6 : Fin 32) 0x4 (by decide),
          RA (17 : Fin 32) 0x5 (by decide)]
        apply BitVec.eq_of_toNat_eq
        rw [le4_loHi, ilWord_toNat, ilB (4 * 1) (by decide), ilB (4 * 1 + 1) (by decide), ilB (4 * 1 + 2) (by decide),
          ilB (4 * 1 + 3) (by decide)]
        rfl
      have kRB : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg mRB q = reg mRA q :=
        fun q hq => by
          obtain ⟨h0, n0, n1, n2', n3', n4, n5, n6⟩ : q.val ≠ 0 ∧ q ≠ a4 ∧ q ≠ a3 ∧ q ≠ (17 : Fin 32) ∧ q ≠ a1 ∧
              q ≠ a5 ∧ q ≠ (5 : Fin 32) ∧ q ≠ a2 := by
            revert hq; revert q; decide
          rw [uRB.regs]; simp only [upd_ne h0 n0, upd_ne h0 n1, upd_ne h0 n2', upd_ne h0 n3', upd_ne h0 n4,
            upd_ne h0 n5, upd_ne h0 n6]
      have RB0 : reg mRB a0 = p + 8 := by rw [uRB.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RA0
      have RB7 : reg mRB (7 : Fin 32) = n - 8 := by rw [uRB.regs]; simp +decide only [upd_app, ↓reduceIte]; exact RA7
      have RB8 : reg mRB (8 : Fin 32) = s := by rw [kRB _ (by decide), kRA _ (by decide), s0_2]
      have RBsp : reg mRB sp = F := by rw [kRB _ (by decide), kRA _ (by decide), sp_2]
      obtain ⟨mRC, cRC, uRC⟩ := St.block ilRdC uRB.self hcC ilRdC_end (by
        simp +decide only [BlockOk, BInstr.ok, BInstr.run, ilRdC, and_true]
        rw [RB8]
        repeat' apply And.intro
        all_goals first | exact True.intro | exact aligned_add env.hs (by decide) | exact env.sSC.sub (by decide))
      simp only [runBlock, BInstr.run, ilRdC] at uRC
      have MR := uRC.mem
      rw [RB8, RB0, RB7, RB1, RB3] at MR
      have hcR : CodeIn mRC.mem P incrementLimbCode := by
        rw [MR]; exact (((hcC.store32 (env.sSC.sub (c := 0) (by decide))).store32 (env.sSC.sub (c := 4) (by decide))).store32
          (env.sSC.sub (c := 0x10) (by decide))).store32 (env.sSC.sub (c := 0x14) (by decide))
      have uR' : St mRC.mem P mRC 0x98 (reg mRC) := ⟨uRC.pc, rfl, fun _ => rfl⟩
      have ldR : ∀ d : Word, ((0x0 : Word).toNat == d.toNat) = false → ((0x4 : Word).toNat == d.toNat) = false →
          ((0x10 : Word).toNat == d.toNat) = false → ((0x14 : Word).toNat == d.toNat) = false → d.toNat % 4 = 0 →
          memLoad32 mRC.mem (s + d) = memLoad32 mC.mem (s + d) := fun d h1 h2 h3 h4 hd => by
        rw [MR, ld_st_off 0x14 d h4 (by decide) hd, ld_st_off 0x10 d h3 (by decide) hd, ld_st_off 0x4 d h2 (by decide) hd,
          ld_st_off 0x0 d h1 (by decide) hd]
      have stR : ∀ k, k + 4 ≤ 16 → memLoad32 mRC.mem (F + BitVec.ofNat 32 k) = memLoad32 mC.mem (F + BitVec.ofNat 32 k) :=
        fun k hk => by
          rw [MR, memLoad32_store32_sep (a := s + 0x14) (b := F + BitVec.ofNat 32 k) (sFS k 0x14 hk (by decide)).symm,
            memLoad32_store32_sep (a := s + 0x10) (b := F + BitVec.ofNat 32 k) (sFS k 0x10 hk (by decide)).symm,
            memLoad32_store32_sep (a := s + 0x4) (b := F + BitVec.ofNat 32 k) (sFS k 0x4 hk (by decide)).symm,
            memLoad32_store32_sep (a := s + 0x0) (b := F + BitVec.ofNat 32 k) (sFS k 0x0 hk (by decide)).symm]
      have e1 : memLoad32 mRC.mem (F + 0xC) = retAddr := by
        have h : memLoad32 mRC.mem (F + 0xC) = memLoad32 mC.mem (F + 0xC) := stR 0xC (by decide)
        rw [h]; exact raC
      have e2 : memLoad32 mRC.mem (F + 0x8) = reg m (8 : Fin 32) := by
        have h : memLoad32 mRC.mem (F + 0x8) = memLoad32 mC.mem (F + 0x8) := stR 8 (by decide)
        rw [h]; exact s8C
      have e3 : memLoad32 mRC.mem (s + 8) = memLoad32 m.mem (s + 0x10) := by
        rw [ldR 8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact W8
      have e4 : memLoad32 mRC.mem (s + 0xC) = memLoad32 m.mem (s + 0x14) := by
        rw [ldR 0xC (by decide) (by decide) (by decide) (by decide) (by decide)]; exact WC
      have e5 : memLoad32 mRC.mem (s + 0x18) = memLoad32 m.mem (s + 0x18) + 1 := by
        rw [ldR 0x18 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact W18
      have e6 : memLoad32 mRC.mem (s + 0x10) = ilWord m.mem p n.toNat 0 := by
        rw [MR, ld_st_off 0x14 0x10 (by decide) (by decide) (by decide), memLoad32_store32_same]
      have e7 : memLoad32 mRC.mem (s + 0x14) = ilWord m.mem p n.toNat 1 := by
        rw [MR, memLoad32_store32_same]
      have e8 : memLoad32 mRC.mem (s + 0x0) = (if n = 0 then p else if n.toNat < 8 then 1 else p + 8) := by
        rw [MR, ld_st_off 0x14 0x0 (by decide) (by decide) (by decide), ld_st_off 0x10 0x0 (by decide) (by decide) (by decide),
          ld_st_off 0x4 0x0 (by decide) (by decide) (by decide), memLoad32_store32_same, ite_eq_right hn0, ite_eq_right hlt]
      have e9 : memLoad32 mRC.mem (s + 0x4) = (if n.toNat < 8 then 0 else n - 8) := by
        rw [MR, ld_st_off 0x14 0x4 (by decide) (by decide) (by decide), ld_st_off 0x10 0x4 (by decide) (by decide) (by decide),
          memLoad32_store32_same, ite_eq_right hlt]
      have e10 : ∀ x, Sep G 0x20 x 1 → Sep s 28 x 1 → mRC.mem x = m.mem x := fun x hg hs => by
        rw [MR, memStore32_get_sep (a := s + 0x14) (hs.sub (c := 0x14) (by decide)),
          memStore32_get_sep (a := s + 0x10) (hs.sub (c := 0x10) (by decide)),
          memStore32_get_sep (a := s + 0x4) (hs.sub (c := 0x4) (by decide)),
          memStore32_get_sep (a := s + 0x0) (hs.sub (c := 0x0) (by decide)), frC x hg hs]
      have S : Steps m mRC := cA.trans (cB.trans (cC.trans (.cons d1 (.cons d2 (.cons d3 (cRA.trans (cRB.trans cRC)))))))
      refine fin mRC (reg mRC) mRC.mem S uR' hcR ?_ ?_ e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
      · rw [uRC.regs]; exact RBsp
      · intro q hq
        have hq' : q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
        rw [uRC.regs, kRB q hq', kRA q hq']; exact k2 q hq

end C3.RV32
