import C3BootProofs.Proof.Step
import C3BootProofs.Image.Bootloader
import C3BootProofs.Spec.Formats

/-!
# `c3_verify::bootstate::crc32`, as compiled

The bootloader image's `crc32` is the boot-state record's checksum,
specialized by the compiler to the record's 28-byte body: it takes the
body's address in `a0` and returns the CRC-32 in `a0`. `crc32_correct`
proves that the function's bytes, at any address, run on the RV32 model
from their first instruction to the return address, leave memory and every
register outside `a0` through `a6` unchanged, and return the CRC-32 that
`crcBits` specifies, of the 28 bytes at `a0`.
-/

namespace C3.RV32

open C3.Image

/-! ## Specification -/

/-- One bit of CRC-32 with the reflected IEEE polynomial. -/
def crcStep (c : Word) : Word := (c >>> 1) ^^^ ((c <<< 31).sshiftRight 31 &&& 0xEDB88320)

/-- `f` applied `n` times. -/
def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterate f n (f x)

/-- One byte of CRC-32. -/
def crcByte (c : Word) (b : BitVec 8) : Word := iterate crcStep 8 (c ^^^ b.zeroExtend 32)

/-- CRC-32 of a byte list. -/
def crcBits (bytes : List (BitVec 8)) : Word := bytes.foldl crcByte 0xFFFFFFFF ^^^ 0xFFFFFFFF

/-- The `n` bytes at `p`. -/
def bytesAt (m : Machine) (p : Word) (n : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => m.mem (p + BitVec.ofNat 32 i)

/-! ## The specification is `C3.crc32` -/

/-- The natural-number step of `C3.crc32`. -/
def stepN (c : Nat) : Nat := if c % 2 == 1 then (c / 2) ^^^ 0xEDB88320 else c / 2

theorem shl31 (c : Word) : c <<< 31 = if c.toNat % 2 = 1 then 0x80000000#32 else 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem crcStep_eq (c : Word) :
    crcStep c = (c >>> 1) ^^^ (if c.toNat % 2 = 1 then 0xEDB88320#32 else 0#32) := by
  unfold crcStep
  rw [shl31]
  split
  · rfl
  · rfl

theorem crcStep_toNat (c : Word) : (crcStep c).toNat = stepN c.toNat := by
  rw [crcStep_eq, BitVec.toNat_xor, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  unfold stepN
  rw [Nat.pow_one]
  split
  · rename_i h
    rw [show (c.toNat % 2 == 1) = true from beq_iff_eq.mpr h]; rfl
  · rename_i h
    rw [show (c.toNat % 2 == 1) = false from by simpa using h]
    exact Nat.xor_zero _


/-- `g` applied `n` times, as `C3.crc32` writes it: a fold over `List.range n`. -/
def rep (g : Nat → Nat) (n : Nat) (x : Nat) : Nat := (List.range n).foldl (fun c _ => g c) x

theorem rep_succ (g : Nat → Nat) (n x : Nat) : rep g (n + 1) x = g (rep g n x) := by
  simp only [rep, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem rep_front (g : Nat → Nat) : ∀ n x, rep g n (g x) = g (rep g n x) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; rw [rep_succ, ih, rep_succ]

theorem iterate_toNat : ∀ n (x : Word), (iterate crcStep n x).toNat = rep stepN n x.toNat := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    show (iterate crcStep n (crcStep x)).toNat = _
    rw [ih, crcStep_toNat, rep_front, rep_succ]

theorem crcByte_toNat (c : Word) (b : BitVec 8) :
    (crcByte c b).toNat = rep stepN 8 (c.toNat ^^^ b.toNat) := by
  unfold crcByte
  rw [iterate_toNat, BitVec.toNat_xor]
  congr 2

theorem foldl_crcByte_toNat : ∀ (bytes : List (BitVec 8)) (c : Word),
    (bytes.foldl crcByte c).toNat =
      (bytes.map BitVec.toNat).foldl (fun c b => rep stepN 8 (c ^^^ b)) c.toNat := by
  intro bytes
  induction bytes with
  | nil => intro c; rfl
  | cons b rest ih =>
    intro c
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, crcByte_toNat]

/-- `crcBits`, the specification the machine-code proof uses, is `C3.crc32`,
the specification the byte formats use and `decode-check` tests against
`c3-verify`. -/
theorem crcBits_toNat (bytes : List (BitVec 8)) :
    (crcBits bytes).toNat = C3.crc32 (bytes.map BitVec.toNat) := by
  unfold crcBits C3.crc32
  rw [BitVec.toNat_xor, foldl_crcByte_toNat]
  rfl

/-! ## The instructions, decoded from the image's bytes -/

theorem crc32_at_00 : fetchRel crc32Code 0x00 = some (.aluImm .add a1 x0 0, 2) := by decide
theorem crc32_at_02 : fetchRel crc32Code 0x02 = some (.aluImm .add a3 x0 0xFFFFFFFF, 2) := by decide
theorem crc32_at_04 : fetchRel crc32Code 0x04 = some (.lui a4 0xEDB88000, 4) := by decide
theorem crc32_at_08 : fetchRel crc32Code 0x08 = some (.aluImm .add a6 x0 0x1C, 2) := by decide
theorem crc32_at_0a : fetchRel crc32Code 0x0A = some (.aluImm .add a4 a4 0x320, 4) := by decide
theorem crc32_at_0e : fetchRel crc32Code 0x0E = some (.branch .beq a6 x0 0x28, 4) := by decide
theorem crc32_at_12 : fetchRel crc32Code 0x12 = some (.alu .add a5 a0 a1, 4) := by decide
theorem crc32_at_16 : fetchRel crc32Code 0x16 = some (.load .lbu a5 a5 0, 4) := by decide
theorem crc32_at_1a : fetchRel crc32Code 0x1A = some (.alu .xor a3 a3 a5, 2) := by decide
theorem crc32_at_1c : fetchRel crc32Code 0x1C = some (.aluImm .add a5 x0 8, 2) := by decide
theorem crc32_at_1e : fetchRel crc32Code 0x1E = some (.branch .beq a5 x0 0x12, 2) := by decide
theorem crc32_at_20 : fetchRel crc32Code 0x20 = some (.aluImm .sll a2 a3 0x1F, 4) := by decide
theorem crc32_at_24 : fetchRel crc32Code 0x24 = some (.aluImm .sra a2 a2 0x1F, 2) := by decide
theorem crc32_at_26 : fetchRel crc32Code 0x26 = some (.aluImm .srl a3 a3 1, 2) := by decide
theorem crc32_at_28 : fetchRel crc32Code 0x28 = some (.alu .and a2 a2 a4, 2) := by decide
theorem crc32_at_2a : fetchRel crc32Code 0x2A = some (.alu .xor a3 a3 a2, 2) := by decide
theorem crc32_at_2c : fetchRel crc32Code 0x2C = some (.aluImm .add a5 a5 0xFFFFFFFF, 2) := by decide
theorem crc32_at_2e : fetchRel crc32Code 0x2E = some (.branch .bne a5 x0 0xFFFFFFF2, 2) := by decide
theorem crc32_at_30 : fetchRel crc32Code 0x30 = some (.aluImm .add a1 a1 1, 2) := by decide
theorem crc32_at_32 : fetchRel crc32Code 0x32 = some (.branch .bne a1 a6 0xFFFFFFE0, 4) := by decide
theorem crc32_at_36 : fetchRel crc32Code 0x36 = some (.aluImm .xor a0 a3 0xFFFFFFFF, 4) := by decide
theorem crc32_at_3a : fetchRel crc32Code 0x3A = some (.jalr x0 ra 0, 2) := by decide

/-! ## The proof -/

/-- `mem0` holds `crc32`'s bytes from `base`. -/
abbrev Code0 (mem0 : Word → BitVec 8) (base : Word) : Prop :=
  ∀ i, i < crc32Code.length → mem0 (base + BitVec.ofNat 32 i) = byteAt crc32Code i

theorem crc32_prologue {mem0 base m f} (hc : Code0 mem0 base) (s : St mem0 base m 0 f) :
    ∃ m' f', Steps m m' ∧ St mem0 base m' 0x12 f' ∧
      f' a1 = 0 ∧ f' a3 = 0xFFFFFFFF ∧ f' a4 = 0xEDB88320 ∧ f' a6 = 0x1c ∧
      ∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a6 → f' r = f r := by
  have h0 := s.zero
  obtain ⟨m1, h1, s1⟩ := s.aluImm hc crc32_at_00 (off' := 0x02) (by decide)
  obtain ⟨m2, h2, s2⟩ := s1.aluImm hc crc32_at_02 (off' := 0x04) (by decide)
  obtain ⟨m3, h3, s3⟩ := s2.lui hc crc32_at_04 (off' := 0x08) (by decide)
  obtain ⟨m4, h4, s4⟩ := s3.aluImm hc crc32_at_08 (off' := 0x0A) (by decide)
  obtain ⟨m5, h5, s5⟩ := s4.aluImm hc crc32_at_0a (off' := 0x0E) (by decide)
  obtain ⟨m6, h6, s6⟩ := s5.notTaken hc 0x12 crc32_at_0e (by decide)
    (by simp +decide [upd, branchTaken, aluEval])
  refine ⟨m6, _, .cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.single h6))))), s6,
    by simp +decide [upd, aluEval, h0], by simp +decide [upd, aluEval],
    by simp +decide [upd, aluEval], by simp +decide [upd, aluEval], ?_⟩
  intro r r1 r3 r4 r6
  by_cases hr : r.val = 0
  · have : r = 0 := Fin.ext hr
    subst this; simp [h0]
  · simp [upd, hr, r1, r3, r4, r6]

theorem ofNat_succ_dec (k : Nat) :
    BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF#32 = BitVec.ofNat 32 k := by
  rw [BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have : k + 1 + 4294967295 = k + 2 ^ 32 := by omega
  rw [this, Nat.add_mod_right]

theorem ofNat_ne_zero {k : Nat} (h0 : k ≠ 0) (h : k < 2 ^ 32) : BitVec.ofNat 32 k ≠ 0 := by
  intro he
  have := congrArg BitVec.toNat he
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
  exact h0 this

theorem crc32_inner {mem0 base} (hc : Code0 mem0 base) : ∀ k, 1 ≤ k → k ≤ 8 → ∀ m f,
    St mem0 base m 0x20 f → f a5 = BitVec.ofNat 32 k → f a4 = 0xEDB88320 →
    ∃ m' f', Steps m m' ∧ St mem0 base m' 0x30 f' ∧ f' a3 = iterate crcStep k (f a3) ∧
      ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a5 → f' r = f r := by
  intro k
  induction k with
  | zero => intro h; exfalso; omega
  | succ k ih =>
    intro _ hk8 m f s h5 h4
    have h0 := s.zero
    obtain ⟨m1, h1, s1⟩ := s.aluImm hc crc32_at_20 (off' := 0x24) (by decide)
    obtain ⟨m2, h2, s2⟩ := s1.aluImm hc crc32_at_24 (off' := 0x26) (by decide)
    obtain ⟨m3, h3, s3⟩ := s2.aluImm hc crc32_at_26 (off' := 0x28) (by decide)
    obtain ⟨m4, h4', s4⟩ := s3.alu hc crc32_at_28 (off' := 0x2A) (by decide)
    obtain ⟨m5, h5', s5⟩ := s4.alu hc crc32_at_2a (off' := 0x2C) (by decide)
    obtain ⟨m6, h6, s6⟩ := s5.aluImm hc crc32_at_2c (off' := 0x2E) (by decide)
    have chain : Steps m m6 :=
      .cons h1 (.cons h2 (.cons h3 (.cons h4' (.cons h5' (.single h6)))))
    have s6' := s6.self
    have ha5 : reg m6 a5 = BitVec.ofNat 32 k := by
      rw [s6.regs]; simp +decide [upd, aluEval, h5, ofNat_succ_dec]
    have ha3 : reg m6 a3 = crcStep (f a3) := by
      rw [s6.regs]; simp +decide [upd, aluEval, h4, crcStep]
    have ha4 : reg m6 a4 = f a4 := by
      rw [s6.regs]; simp +decide [upd]
    have hfr : ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a5 → reg m6 r = f r := by
      intro r r2 r3 r5
      rw [s6.regs]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [h0]
      · simp [upd, hr, r2, r3, r5]
    cases k with
    | zero =>
      obtain ⟨m7, h7, s7⟩ := s6'.notTaken hc 0x30 crc32_at_2e (by decide)
        (by rw [ha5]; simp [branchTaken, reg])
      exact ⟨m7, reg m6, chain.trans (.single h7), s7, by rw [ha3]; rfl, hfr⟩
    | succ k =>
      obtain ⟨m7, h7, s7⟩ := s6'.taken hc 0x20 crc32_at_2e (by decide)
        (by rw [ha5]; simpa [branchTaken, reg] using ofNat_ne_zero (k := k + 1) (by omega) (by omega))
      obtain ⟨m', f', hs, s', h3', hfr'⟩ :=
        ih (by omega) (by omega) m7 (reg m6) s7 ha5 (by rw [ha4, h4])
      refine ⟨m', f', (chain.trans (.single h7)).trans hs, s', ?_, ?_⟩
      · rw [h3', ha3]; rfl
      · intro r r2 r3 r5; rw [hfr' r r2 r3 r5, hfr r r2 r3 r5]

theorem ofNat_ne {a b : Nat} (h : a ≠ b) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    BitVec.ofNat 32 a ≠ BitVec.ofNat 32 b := by
  intro he
  have := congrArg BitVec.toNat he
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact h this

/-- The CRC state after the first `i` of the bytes at `p`. -/
def crcPrefix (mem0 : Word → BitVec 8) (p : Word) (i : Nat) : Word :=
  ((List.range i).map fun j => mem0 (p + BitVec.ofNat 32 j)).foldl crcByte 0xFFFFFFFF

theorem crcPrefix_succ (mem0 : Word → BitVec 8) (p : Word) (i : Nat) :
    crcPrefix mem0 p (i + 1) = crcByte (crcPrefix mem0 p i) (mem0 (p + BitVec.ofNat 32 i)) := by
  simp [crcPrefix, List.range_succ, List.foldl_append]

theorem crc32_body {mem0 base} (hc : Code0 mem0 base) {i : Nat} (hi : i < 28) {m f}
    (s : St mem0 base m 0x12 f) (h1 : f a1 = BitVec.ofNat 32 i) (h4 : f a4 = 0xEDB88320)
    (h6 : f a6 = 0x1c) :
    ∃ m' f', Steps m m' ∧ St mem0 base m' (if i + 1 = 28 then 0x36 else 0x12) f' ∧
      f' a1 = BitVec.ofNat 32 (i + 1) ∧ f' a3 = crcByte (f a3) (mem0 (f a0 + BitVec.ofNat 32 i)) ∧
      ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a5 → f' r = f r := by
  have h0 := s.zero
  obtain ⟨m1, e1, s1⟩ := s.alu hc crc32_at_12 (off' := 0x16) (by decide)
  obtain ⟨m2, e2, s2⟩ := s1.lbu hc crc32_at_16 (off' := 0x1A) (by decide)
  obtain ⟨m3, e3, s3⟩ := s2.alu hc crc32_at_1a (off' := 0x1C) (by decide)
  obtain ⟨m4, e4, s4⟩ := s3.aluImm hc crc32_at_1c (off' := 0x1E) (by decide)
  obtain ⟨m5, e5, s5⟩ := s4.notTaken hc 0x20 crc32_at_1e (by decide)
    (by simp +decide [upd, branchTaken, aluEval])
  have c5 : Steps m m5 := .cons e1 (.cons e2 (.cons e3 (.cons e4 (.single e5))))
  have r5a5 : reg m5 a5 = BitVec.ofNat 32 8 := by rw [s5.regs]; simp +decide [upd, aluEval]
  have r5a3 : reg m5 a3 = f a3 ^^^ (mem0 (f a0 + BitVec.ofNat 32 i)).zeroExtend 32 := by
    rw [s5.regs]; simp +decide [upd, aluEval, h1]
  have r5a4 : reg m5 a4 = 0xEDB88320 := by rw [s5.regs]; simp +decide [upd, h4]
  have r5fr : ∀ r, r ≠ a3 → r ≠ a5 → reg m5 r = f r := by
    intro r r3 r5
    rw [s5.regs]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [h0]
    · simp [upd, hr, r3, r5]
  obtain ⟨m6, f6, c6, s6, r6a3, r6fr⟩ := crc32_inner hc 8 (by omega) (by omega) m5 (reg m5) s5.self
    r5a5 r5a4
  obtain ⟨m7, e7, s7⟩ := s6.aluImm hc crc32_at_30 (off' := 0x32) (by decide)
  have f6a1 : f6 a1 = BitVec.ofNat 32 i := by
    rw [r6fr a1 (by decide) (by decide) (by decide), r5fr a1 (by decide) (by decide), h1]
  have f6a6 : f6 a6 = 0x1c := by
    rw [r6fr a6 (by decide) (by decide) (by decide), r5fr a6 (by decide) (by decide), h6]
  have r7a1 : reg m7 a1 = BitVec.ofNat 32 (i + 1) := by
    rw [s7.regs]; simp +decide [upd, aluEval, f6a1, BitVec.ofNat_add_ofNat]
  have r7a6 : reg m7 a6 = BitVec.ofNat 32 28 := by rw [s7.regs]; simp +decide [upd, f6a6]
  have r7a3 : reg m7 a3 = crcByte (f a3) (mem0 (f a0 + BitVec.ofNat 32 i)) := by
    rw [s7.regs]; simp +decide [upd, r6a3, r5a3]; rfl
  have r7fr : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a5 → reg m7 r = f r := by
    intro r r1 r2 r3 r5
    rw [s7.regs]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [h0]
    · simp [upd, hr, r1, r6fr r r2 r3 r5, r5fr r r3 r5]
  by_cases hlast : i + 1 = 28
  · obtain ⟨m8, e8, s8⟩ := s7.self.notTaken hc 0x36 crc32_at_32 (by decide)
      (by rw [r7a1, r7a6, hlast]; simp [branchTaken])
    refine ⟨m8, reg m7, (c5.trans c6).trans (.cons e7 (.single e8)), ?_, r7a1, r7a3, r7fr⟩
    rw [ite_eq_left hlast]; exact s8
  · obtain ⟨m8, e8, s8⟩ := s7.self.taken hc 0x12 crc32_at_32 (by decide)
      (by rw [r7a1, r7a6]; simpa [branchTaken] using ofNat_ne hlast (by omega) (by omega))
    refine ⟨m8, reg m7, (c5.trans c6).trans (.cons e7 (.single e8)), ?_, r7a1, r7a3, r7fr⟩
    rw [ite_eq_right hlast]; exact s8


theorem crc32_outer {mem0 base} (hc : Code0 mem0 base) (p : Word) :
    ∀ n i, i + n = 28 → i < 28 → ∀ m f, St mem0 base m 0x12 f → f a0 = p →
      f a1 = BitVec.ofNat 32 i → f a4 = 0xEDB88320 → f a6 = 0x1c → f a3 = crcPrefix mem0 p i →
      ∃ m' f', Steps m m' ∧ St mem0 base m' 0x36 f' ∧ f' a3 = crcPrefix mem0 p 28 ∧
        ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a5 → f' r = f r := by
  intro n
  induction n with
  | zero => intro i hn hi; exfalso; omega
  | succ n ih =>
    intro i hn hi m f s h0' h1 h4 h6 h3
    obtain ⟨m1, f1, c1, s1, f1a1, f1a3, f1fr⟩ := crc32_body hc hi s h1 h4 h6
    have f1a3' : f1 a3 = crcPrefix mem0 p (i + 1) := by rw [f1a3, crcPrefix_succ, h3, h0']
    by_cases hlast : i + 1 = 28
    · rw [ite_eq_left hlast] at s1
      exact ⟨m1, f1, c1, s1, by rw [f1a3', hlast], f1fr⟩
    · rw [ite_eq_right hlast] at s1
      have fr := fun r r1 r2 r3 r5 => f1fr r r1 r2 r3 r5
      obtain ⟨m2, f2, c2, s2, f2a3, f2fr⟩ := ih (i + 1) (by omega) (by omega) m1 f1 s1
        (by rw [fr a0 (by decide) (by decide) (by decide) (by decide), h0']) f1a1
        (by rw [fr a4 (by decide) (by decide) (by decide) (by decide), h4])
        (by rw [fr a6 (by decide) (by decide) (by decide) (by decide), h6]) f1a3'
      exact ⟨m2, f2, c1.trans c2, s2, f2a3, fun r r1 r2 r3 r5 => by
        rw [f2fr r r1 r2 r3 r5, fr r r1 r2 r3 r5]⟩

/-- **The compiled `crc32` is correct.** With its bytes in memory at any
`base` and the program counter at its first byte, there is an execution
that reaches the return address in `ra` with memory unchanged, every
register but `a0` through `a6` unchanged, and `a0` holding the CRC-32 of the
28 bytes that were at `a0`. The function writes no memory, so this holds
even if those bytes overlap its code. -/
theorem crc32_correct (m : Machine) (base retAddr : Word) (hcode : CodeAt m base crc32Code)
    (hpc : m.pc = base) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = m.mem ∧
      reg m' a0 = crcBits (bytesAt m (reg m a0) 28) ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → reg m' r = reg m r := by
  have hc : Code0 m.mem base := hcode
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨m1, f1, c1, s1, f1a1, f1a3, f1a4, f1a6, f1fr⟩ := crc32_prologue hc s0
  have fr1 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → f1 r = reg m r :=
    fun r r1 _ r3 r4 _ r6 => f1fr r r1 r3 r4 r6
  obtain ⟨m2, f2, c2, s2, f2a3, f2fr⟩ := crc32_outer hc (reg m a0) 28 0 rfl (by omega) m1 f1 s1
    (fr1 a0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [f1a1]; rfl) f1a4 f1a6 (by rw [f1a3]; rfl)
  obtain ⟨m3, e3, s3⟩ := s2.aluImm hc crc32_at_36 (off' := 0x3A) (by decide)
  obtain ⟨m4, e4, pc4, mem4, regs4⟩ := s3.jalr hc crc32_at_3a
  have keep : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 →
      reg m4 r = reg m r := by
    intro r r0 r1 r2 r3 r4 r5 r6
    rw [regs4]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp; rfl
    · simp [upd, hr, r0, f2fr r r1 r2 r3 r5, fr1 r r1 r2 r3 r4 r5 r6]
  refine ⟨m4, (c1.trans c2).trans (.cons e3 (.single e4)), ?_, mem4, ?_, keep⟩
  · rw [pc4]
    have : upd f2 a0 (aluEval .xor (f2 a3) 0xFFFFFFFF) ra = retAddr := by
      rw [← keep ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), regs4] at hra
      exact hra
    rw [this]; simpa using hret
  · rw [regs4]
    simp +decide [upd, aluEval, f2a3, crcBits, crcPrefix, bytesAt]

/-- The compiled `crc32` returns `C3.crc32` of the 28 bytes at `a0`: the
specification that `decode-check` tests against `c3-verify`. -/
theorem crc32_spec (m : Machine) (base retAddr : Word) (hcode : CodeAt m base crc32Code)
    (hpc : m.pc = base) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = m.mem ∧
      (reg m' a0).toNat = C3.crc32 ((bytesAt m (reg m a0) 28).map BitVec.toNat) := by
  obtain ⟨m', hs, hpc', hmem, ha0, _⟩ := crc32_correct m base retAddr hcode hpc hra hret
  exact ⟨m', hs, hpc', hmem, by rw [ha0, crcBits_toNat]⟩

end C3.RV32
