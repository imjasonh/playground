import C3BootProofs.Proofs.JsonMembers
import C3BootProofs.Proofs.JsonModel

/-!
# `Value::u64`, as compiled

`Value::u64(&self)` stores `Ok` of the value of a number value's digits, or
`Err(Schema)`, at `out`. It fails when the value is empty, holds a byte that
isn't a digit, or doesn't fit in 64 bits. It saves `ra` and `s0`–`s2` in a
32-byte frame and puts a byte iterator in that frame for
`Iterator::all(u8::is_ascii_digit)`, which the compiler outlined as
`allAsciiDigit` at `base + 0x158`. That callee is a leaf that writes only
the iterator, so the stack region is the 32 bytes below `sp`.

A `Result<u64, TufError>` keeps its tag byte at `out`, the error byte at
`out + 1`, and the value's low and high words at `out + 8` and `out + 12`.
`U64Res` describes that layout.
-/

namespace C3.Json

/-- The value of the decimal digits `l`, from the value `acc` of the digits
before them. -/
def dvFrom (acc : Nat) (l : Bytes) : Nat := l.foldl (fun n d => 10 * n + (d - 48)) acc

theorem digitsValue_eq (l : Bytes) : digitsValue l = dvFrom 0 l := rfl

theorem dvFrom_cons (acc b : Nat) (l : Bytes) : dvFrom acc (b :: l) = dvFrom (10 * acc + (b - 48)) l := by
  simp only [dvFrom, List.foldl_cons]

theorem dvFrom_nil (acc : Nat) : dvFrom acc [] = acc := rfl

theorem le_dvFrom : ∀ (l : Bytes) (acc : Nat), acc ≤ dvFrom acc l
  | [], _ => Nat.le_refl _
  | b :: l, acc => by rw [dvFrom_cons]; exact Nat.le_trans (by omega) (le_dvFrom l _)

theorem digLen_all : ∀ l : Bytes, digLen l = l.length ↔ l.all isDigit = true
  | [] => by simp only [digLen, List.length_nil, List.all_nil]
  | b :: l => by
    cases h : isDigit b
    · simp only [digLen, h, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.all_cons,
        Bool.false_and, iff_false]
      exact fun e => Nat.succ_ne_zero _ e.symm
    · simp only [digLen, h, ↓reduceIte, List.length_cons, List.all_cons, Bool.true_and]
      rw [← digLen_all l, Nat.add_right_cancel_iff]

/-- `Value::u64` of the value `d`. -/
def u64Val (d : Bytes) : Option Nat :=
  if d = [] then none else if d.all isDigit = false then none
  else if digitsValue d < 2 ^ 64 then some (digitsValue d) else none

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem jaad_at_0 : fetchRel allAsciiDigitCode 0x0 = some (.load .lw a4 a0 0x0, 2) := by decide
theorem jaad_at_2 : fetchRel allAsciiDigitCode 0x2 = some (.load .lw a1 a0 0x4, 2) := by decide
theorem jaad_at_4 : fetchRel allAsciiDigitCode 0x4 = some (.aluImm .add a2 x0 0xA, 2) := by decide
theorem jaad_at_6 : fetchRel allAsciiDigitCode 0x6 = some (.alu .add a3 x0 a4, 2) := by decide
theorem jaad_at_8 : fetchRel allAsciiDigitCode 0x8 = some (.branch .beq a4 a1 0x16, 4) := by decide
theorem jaad_at_c : fetchRel allAsciiDigitCode 0xC = some (.load .lbu a5 a3 0x0, 4) := by decide
theorem jaad_at_10 : fetchRel allAsciiDigitCode 0x10 = some (.aluImm .add a4 a3 0x1, 4) := by decide
theorem jaad_at_14 : fetchRel allAsciiDigitCode 0x14 = some (.aluImm .add a5 a5 0xFFFFFFD0, 4) := by decide
theorem jaad_at_18 : fetchRel allAsciiDigitCode 0x18 = some (.store .sw a0 a4 0x0, 2) := by decide
theorem jaad_at_1a : fetchRel allAsciiDigitCode 0x1A = some (.branch .bltu a5 a2 0xFFFFFFEC, 4) := by decide
theorem jaad_at_1e : fetchRel allAsciiDigitCode 0x1E = some (.alu .xor a1 a1 a3, 2) := by decide
theorem jaad_at_20 : fetchRel allAsciiDigitCode 0x20 = some (.aluImm .sltu a0 a1 0x1, 4) := by decide
theorem jaad_at_24 : fetchRel allAsciiDigitCode 0x24 = some (.jalr x0 ra 0x0, 2) := by decide

theorem jaad_dig : ∀ b : BitVec 8,
    branchTaken .bltu (aluEval .add (b.zeroExtend 32) 0xFFFFFFD0) 10 = isDigit b.toNat := by decide

/-- The registers `allAsciiDigit` may change. -/
abbrev aadClob : List (Fin 32) := [a0, a1, a2, a3, a4, a5]

/-- `allAsciiDigit` returned to `ret` with `v` in `a0`, changed no memory
outside the iterator at `it`, and kept the registers outside `aadClob`. -/
def aadPost (ret : Word) (M : Word → BitVec 8) (it : Word) (v : Word) (g0 : Fin 32 → Word) : Post :=
  fun pc M' g => pc = ret ∧ Out M M' it 4 ∧ g a0 = v ∧ ∀ x, x ∉ aadClob → g x = g0 x

section
variable {M : Word → BitVec 8} {base it p : Word} {Q : Post}

theorem jaad_loop {n : Nat} (hn : n < 2 ^ 32) (hal : it.toNat % 4 = 0) (hs : Sep it 4 p n)
    (hsc : Sep it 4 base allAsciiDigitCode.length) :
    ∀ (j k : Nat) (f : Fin 32 → Word) (Mc : Word → BitVec 8) (q : Word), k + j = n → q = p + BitVec.ofNat 32 k →
      f a4 = q → f a1 = p + BitVec.ofNat 32 n → f a2 = 10 → f a0 = it → Out M Mc it 4 →
      (∀ (g : Fin 32 → Word) (Mc' : Word → BitVec 8), Out M Mc' it 4 →
        g a3 = p + BitVec.ofNat 32 (k + digLen (memBytes M q j)) → g a1 = p + BitVec.ofNat 32 n →
        (∀ x, x ∉ ([a3, a4, a5] : List (Fin 32)) → g x = f x) → WP allAsciiDigitCode base Q Mc' 0x1E g) →
      WP allAsciiDigitCode base Q Mc 0x6 f
  | 0, k, f, Mc, q, hkj, hq, h4, h1, _, _, hO, K => by
    refine WP.zero fun hz => ?_
    refine WP.alu jaad_at_6 ?_; wn
    refine WP.branch jaad_at_8 (fun _ => ?_) (fun e => ?_) <;> wn
    · refine K _ Mc hO ?_ (by rsimp; exact h1) ?_
      · rsimp; simp only [ev0, ev_mv hz]; rw [h4, hq, memBytes_zero, digLen, Nat.add_zero]
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp only [upd_app, hx.1, ↓reduceIte, ite_val_zero hz]
    · rsimp at e
      rw [h4, h1, hq, show k = n by omega] at e
      have h : branchTaken .beq (p + BitVec.ofNat 32 n) (p + BitVec.ofNat 32 n) = true := beq_iff_eq.mpr rfl
      rw [h] at e; exact absurd e (by decide)
  | j + 1, k, f, Mc, q, hkj, hq, h4, h1, h2, h0, hO, K => by
    refine WP.zero fun hz => ?_
    refine WP.alu jaad_at_6 ?_; wn
    refine WP.branch jaad_at_8 (fun e => ?_) (fun _ => ?_) <;> wn
    · rsimp at e
      rw [h4, h1, hq] at e
      exact absurd (beq_iff_eq.mp e) (add_ofNat_ne p (by omega) hn (by omega))
    have hb : Mc q = M q := by rw [hq]; exact hO.byte hs (by omega)
    refine WP.lbu jaad_at_c ?_; wn
    refine WP.aluImm jaad_at_10 ?_; wn
    refine WP.aluImm jaad_at_14 ?_; wn
    refine WP.sw jaad_at_18 (by rsimp; rw [h0, add_lit_zero]; exact hal)
      (by rsimp; rw [h0, add_lit_zero]; exact hsc) ?_; wn
    simp only [ev0, ev_mv hz]; rw [h4]; simp only [add_lit_zero]; rw [hb, h0]
    refine WP.branch jaad_at_1a (fun e => ?_) (fun e => ?_) <;> wn
    · rsimp at e
      rw [h2, jaad_dig] at e
      refine jaad_loop hn hal hs hsc j (k + 1) _ _ (q + 1) (by omega) (by rw [hq, BitVec.add_assoc, cl_succ])
        (by rsimp; rfl) (by rsimp; exact h1) (by rsimp; exact h2) (by rsimp; exact h0)
        (hO.trans (out_store32 _ _ _)) fun g Mc' hO' g3 g1 hg => K g Mc' hO' ?_ g1 fun x hx => ?_
      · rw [g3, memBytes_succ]; simp only [digLen, e, ↓reduceIte]
        rw [Nat.add_assoc, Nat.add_comm 1]
      · rw [hg x hx]; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp only [upd_app, hx.1, hx.2.1, hx.2.2, ↓reduceIte, ite_val_zero hz]
    · rsimp at e
      rw [h2, jaad_dig] at e
      refine K _ _ (hO.trans (out_store32 _ _ _)) ?_ (by rsimp; exact h1) fun x hx => ?_
      · rsimp; rw [memBytes_succ]
        simp only [digLen, e, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; exact hq
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp only [upd_app, hx.1, hx.2.1, hx.2.2, ↓reduceIte, ite_val_zero hz]

end

theorem sltu_xor1 (x y : Word) : aluEval .sltu (aluEval .xor x y) 1 = if x = y then 1 else 0 := by
  by_cases h : x = y
  · subst h; simp only [aluEval, BitVec.xor_self, ↓reduceIte]; rfl
  · have hz : x ^^^ y ≠ 0 := fun e => h (by
      have := congrArg (· ^^^ y) e
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at this
      exact this.trans BitVec.zero_xor)
    have hn : (x ^^^ y).toNat ≠ 0 := fun e => hz (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    have hl : ¬ ((x ^^^ y).toNat < (1 : Word).toNat) := by
      show ¬ (_ < 1); omega
    simp only [aluEval, BitVec.ult, h, hl, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem jaad_wp {M : Word → BitVec 8} {base ret it p : Word} {f : Fin 32 → Word} {n : Nat} (hn : n < 2 ^ 32)
    (h0 : f a0 = it) (hra : f ra = ret) (hret : ret &&& ~~~1 = ret) (hal : it.toNat % 4 = 0)
    (hp : memLoad32 M it = p) (he : memLoad32 M (it + 4) = p + BitVec.ofNat 32 n) (hs : Sep it 4 p n)
    (hsc : Sep it 4 base allAsciiDigitCode.length) :
    WP allAsciiDigitCode base (aadPost ret M it (if (memBytes M p n).all isDigit then 1 else 0) f) M 0 f := by
  refine WP.zero fun hz => ?_
  refine WP.lw jaad_at_0 (by rw [h0, add_lit_zero]; exact hal) ?_; wn
  refine WP.lw jaad_at_2 (by rsimp; rw [h0]; exact aligned_add hal (k := 4) (by decide)) ?_; wn
  refine WP.aluImm jaad_at_4 ?_; wn
  refine jaad_loop hn hal hs hsc n 0 _ M p (by omega) (add_ofNat_zero p).symm (by rsimp; rw [h0, add_lit_zero, hp])
    (by rsimp; rw [h0, he]) (by rsimp) (by rsimp; exact h0) (Out.refl _ _ _)
    fun g Mc hO g3 g1 hg => ?_
  refine WP.alu jaad_at_1e ?_; wn
  refine WP.aluImm jaad_at_20 ?_; wn
  refine WP.ret jaad_at_24 ⟨?_, hO, ?_, fun x hx => ?_⟩
  · rsimp; rw [hg ra (by decide)]; rsimp; rw [hra, add_lit_zero, hret]
  · rsimp; rw [g1, g3, Nat.zero_add, sltu_xor1]
    have hd := digLen_le (memBytes M p n)
    rw [memBytes_length] at hd
    have := digLen_all (memBytes M p n)
    rw [memBytes_length] at this
    by_cases hd' : digLen (memBytes M p n) = n
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [hd'])), ite_eq_left_of_eq_true _ _ (eq_true (this.mp hd'))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (add_ofNat_ne p hn (by omega) (Ne.symm hd'))),
        ite_eq_right_of_eq_false _ _ (eq_false fun h => hd' (this.mpr h))]
  · simp only [aadClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hx
    simp only [upd_app, n0, n1, ↓reduceIte, ite_val_zero hz]
    rw [hg x (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨n3, n4, n5⟩)]
    simp only [upd_app, n1, n2, n4, ↓reduceIte, ite_val_zero hz]

/-- `allAsciiDigit(it)`, with `it` a byte iterator over the `n` bytes at
`p`: returns 1 if every byte is a digit and 0 if not, writes only the
iterator, and keeps every register outside `aadClob`. -/
theorem allAsciiDigit_wp (m : Machine) {base retAddr it p : Word} {n : Nat}
    (hb : base.toNat % 2 = 0) (hc : CodeIn m.mem base allAsciiDigitCode) (hpc : m.pc = base)
    (ha0 : reg m a0 = it) (hn : n < 2 ^ 32) (hal : it.toNat % 4 = 0) (hp : memLoad32 m.mem it = p)
    (he : memLoad32 m.mem (it + 4) = p + BitVec.ofNat 32 n) (hs : Sep it 4 p n)
    (hsc : Sep it 4 base allAsciiDigitCode.length) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ Out m.mem m'.mem it 4 ∧
      reg m' a0 = (if (memBytes m.mem p n).all isDigit then 1 else 0) ∧
      ∀ r, r ∉ aadClob → reg m' r = reg m r :=
  let ⟨m', st, hpc', hO, h0, hfr⟩ := WP.run (jaad_wp hn ha0 hra hret hal hp he hs hsc) hb hc hpc
  ⟨m', st, hpc', hO, h0, hfr⟩

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat}
  {f : Fin 32 → Word}

/-- A call to `allAsciiDigit(it)` with the code at `tb`. -/
theorem WP.callAad {hi lo tb it p : Word} {n : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : CodeIn M tb allAsciiDigitCode) (h0 : f a0 = it) (hn : n < 2 ^ 32) (hal : it.toNat % 4 = 0)
    (hp : memLoad32 M it = p) (he : memLoad32 M (it + 4) = p + BitVec.ofNat 32 n) (hs : Sep it 4 p n)
    (hst : Sep it 4 tb allAsciiDigitCode.length) (hsc : Sep it 4 base code.length)
    (k : ∀ m2 : Machine, Out M m2.mem it 4 → reg m2 a0 = (if (memBytes M p n).all isDigit then 1 else 0) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 aadClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := aadClob) (P := fun m2 => Out M m2.mem it 4 ∧
      reg m2 a0 = (if (memBytes M p n).all isDigit then 1 else 0)) h1 h2
    (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.1.codeIn hc hsc) (fun m2 hP => k m2 hP.1 hP.2)
  obtain ⟨m2, c2, pc2, hO, r0, hfr⟩ := allAsciiDigit_wp m1 (base := tb) (it := it) (p := p) (n := n) htb
    (by rw [hmem1]; exact hct) hpc1 (by rw [hreg1]; rsimp; exact h0) hn hal (by rw [hmem1]; exact hp)
    (by rw [hmem1]; exact he) hs hst (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp)
    (even_clear _ (even_at base hb _ hev))
  rw [hmem1] at hO r0
  exact ⟨m2, c2, pc2, ⟨hO, r0⟩, hfr⟩

end

theorem u6_at_0 : fetchRel jsonU64Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem u6_at_2 : fetchRel jsonU64Code 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem u6_at_4 : fetchRel jsonU64Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem u6_at_6 : fetchRel jsonU64Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x14, 2) := by decide
theorem u6_at_8 : fetchRel jsonU64Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x10, 2) := by decide
theorem u6_at_a : fetchRel jsonU64Code 0xA = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem u6_at_c : fetchRel jsonU64Code 0xC = some (.branch .beq a2 x0 0x62, 2) := by decide
theorem u6_at_e : fetchRel jsonU64Code 0xE = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem u6_at_10 : fetchRel jsonU64Code 0x10 = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem u6_at_12 : fetchRel jsonU64Code 0x12 = some (.alu .add a0 a1 a2, 4) := by decide
theorem u6_at_16 : fetchRel jsonU64Code 0x16 = some (.store .sw sp a1 0x8, 2) := by decide
theorem u6_at_18 : fetchRel jsonU64Code 0x18 = some (.store .sw sp a0 0xC, 2) := by decide
theorem u6_at_1a : fetchRel jsonU64Code 0x1A = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem u6_at_1c : fetchRel jsonU64Code 0x1C = some (.auipc ra 0x0, 4) := by decide
theorem u6_at_20 : fetchRel jsonU64Code 0x20 = some (.jalr ra ra 0x13C, 4) := by decide
theorem u6_at_24 : fetchRel jsonU64Code 0x24 = some (.branch .beq a0 x0 0x4A, 2) := by decide
theorem u6_at_26 : fetchRel jsonU64Code 0x26 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem u6_at_28 : fetchRel jsonU64Code 0x28 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem u6_at_2a : fetchRel jsonU64Code 0x2A = some (.aluImm .add a1 x0 0xA, 2) := by decide
theorem u6_at_2c : fetchRel jsonU64Code 0x2C = some (.branch .beq (9 : Fin 32) x0 0x4E, 2) := by decide
theorem u6_at_2e : fetchRel jsonU64Code 0x2E = some (.alu .mulhu a4 a0 a1, 4) := by decide
theorem u6_at_32 : fetchRel jsonU64Code 0x32 = some (.alu .mul a3 a2 a1, 4) := by decide
theorem u6_at_36 : fetchRel jsonU64Code 0x36 = some (.alu .mulhu a2 a2 a1, 4) := by decide
theorem u6_at_3a : fetchRel jsonU64Code 0x3A = some (.alu .add a3 a3 a4, 2) := by decide
theorem u6_at_3c : fetchRel jsonU64Code 0x3C = some (.alu .sltu a4 a3 a4, 4) := by decide
theorem u6_at_40 : fetchRel jsonU64Code 0x40 = some (.alu .sltu a2 x0 a2, 4) := by decide
theorem u6_at_44 : fetchRel jsonU64Code 0x44 = some (.alu .or a2 a2 a4, 2) := by decide
theorem u6_at_46 : fetchRel jsonU64Code 0x46 = some (.branch .bne a2 x0 0x28, 2) := by decide
theorem u6_at_48 : fetchRel jsonU64Code 0x48 = some (.alu .mul a2 a0 a1, 4) := by decide
theorem u6_at_4c : fetchRel jsonU64Code 0x4C = some (.load .lbu a0 (8 : Fin 32) 0x0, 4) := by decide
theorem u6_at_50 : fetchRel jsonU64Code 0x50 = some (.aluImm .add a0 a0 0xFFFFFFD0, 4) := by decide
theorem u6_at_54 : fetchRel jsonU64Code 0x54 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem u6_at_58 : fetchRel jsonU64Code 0x58 = some (.alu .add a0 a0 a2, 2) := by decide
theorem u6_at_5a : fetchRel jsonU64Code 0x5A = some (.alu .sltu a4 a0 a2, 4) := by decide
theorem u6_at_5e : fetchRel jsonU64Code 0x5E = some (.alu .add a2 a3 a4, 4) := by decide
theorem u6_at_62 : fetchRel jsonU64Code 0x62 = some (.alu .sltu a3 a2 a3, 4) := by decide
theorem u6_at_66 : fetchRel jsonU64Code 0x66 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x1, 2) := by decide
theorem u6_at_68 : fetchRel jsonU64Code 0x68 = some (.alu .and a3 a3 a4, 2) := by decide
theorem u6_at_6a : fetchRel jsonU64Code 0x6A = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem u6_at_6c : fetchRel jsonU64Code 0x6C = some (.branch .beq a3 x0 0xFFFFFFC0, 2) := by decide
theorem u6_at_6e : fetchRel jsonU64Code 0x6E = some (.aluImm .add a0 x0 0x21, 4) := by decide
theorem u6_at_72 : fetchRel jsonU64Code 0x72 = some (.store .sb (18 : Fin 32) a0 0x1, 4) := by decide
theorem u6_at_76 : fetchRel jsonU64Code 0x76 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem u6_at_78 : fetchRel jsonU64Code 0x78 = some (.jal x0 0xA, 2) := by decide
theorem u6_at_7a : fetchRel jsonU64Code 0x7A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem u6_at_7c : fetchRel jsonU64Code 0x7C = some (.alu .add a3 x0 (18 : Fin 32), 2) := by decide
theorem u6_at_7e : fetchRel jsonU64Code 0x7E = some (.store .sw a3 a0 0x8, 2) := by decide
theorem u6_at_80 : fetchRel jsonU64Code 0x80 = some (.store .sw a3 a2 0xC, 2) := by decide
theorem u6_at_82 : fetchRel jsonU64Code 0x82 = some (.store .sb (18 : Fin 32) a1 0x0, 4) := by decide
theorem u6_at_86 : fetchRel jsonU64Code 0x86 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem u6_at_88 : fetchRel jsonU64Code 0x88 = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem u6_at_8a : fetchRel jsonU64Code 0x8A = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem u6_at_8c : fetchRel jsonU64Code 0x8C = some (.load .lw (18 : Fin 32) sp 0x10, 2) := by decide
theorem u6_at_8e : fetchRel jsonU64Code 0x8E = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem u6_at_90 : fetchRel jsonU64Code 0x90 = some (.jalr x0 ra 0x0, 2) := by decide

theorem u6_sltu (a b : Word) :
    (a.toNat < b.toNat ∧ aluEval .sltu a b = 1) ∨ (b.toNat ≤ a.toNat ∧ aluEval .sltu a b = 0) := by
  by_cases hl : a.toNat < b.toNat
  · exact .inl ⟨hl, ite_eq_left_of_eq_true _ _ (eq_true (by simp only [BitVec.ult]; exact decide_eq_true hl))⟩
  · exact .inr ⟨by omega, ite_eq_right_of_eq_false _ _ (eq_false (by
      simp only [BitVec.ult]; exact fun e => hl (of_decide_eq_true e)))⟩

theorem u6_tmulhu (x : Word) : (aluEval .mulhu x 10).toNat = x.toNat * 10 / 4294967296 := by
  show (BitVec.ofNat 32 (x.toNat * 10 / 2 ^ 32)).toNat = _
  have := x.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem u6_tmul (x : Word) : (aluEval .mul x 10).toNat = x.toNat * 10 % 4294967296 := by
  show (x * 10).toNat = _
  rw [BitVec.toNat_mul]; rfl

theorem u6_tadd (x y : Word) : (aluEval .add x y).toNat = (x.toNat + y.toNat) % 4294967296 :=
  BitVec.toNat_add x y

theorem u6_mul (lo hi : Word) :
    branchTaken .bne (aluEval .or (aluEval .sltu 0 (aluEval .mulhu hi 10))
      (aluEval .sltu (aluEval .add (aluEval .mul hi 10) (aluEval .mulhu lo 10)) (aluEval .mulhu lo 10))) 0 =
      decide (2 ^ 64 ≤ 10 * (hi.toNat * 2 ^ 32 + lo.toNat)) := by
  have := lo.isLt; have := hi.isLt
  have tA := u6_tmulhu lo; have tB := u6_tmulhu hi; have tC := u6_tmul hi
  have tS := u6_tadd (aluEval .mul hi 10) (aluEval .mulhu lo 10)
  have k0 : (aluEval .mulhu lo 10).toNat * 4294967296 ≤ lo.toNat * 10 := by
    rw [tA]; exact Nat.div_mul_le_self _ _
  have k4 : (aluEval .mulhu lo 10).toNat < 10 := by omega
  have t0 : (0 : Word).toNat = 0 := rfl
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl, show (2 : Nat) ^ 32 = 4294967296 from rfl]
  rcases u6_sltu 0 (aluEval .mulhu hi 10) with ⟨h1, e1⟩ | ⟨h1, e1⟩
  · rw [decide_eq_true (by omega)]
    rcases u6_sltu (aluEval .add (aluEval .mul hi 10) (aluEval .mulhu lo 10)) (aluEval .mulhu lo 10) with
      ⟨_, e2⟩ | ⟨_, e2⟩ <;> rw [e1, e2] <;> rfl
  have k3 : (aluEval .mul hi 10).toNat = hi.toNat * 10 := by omega
  rcases u6_sltu (aluEval .add (aluEval .mul hi 10) (aluEval .mulhu lo 10)) (aluEval .mulhu lo 10) with
    ⟨h2, e2⟩ | ⟨h2, e2⟩ <;> rw [e1, e2]
  · have k1 : 4294967296 ≤ (aluEval .mul hi 10).toNat + (aluEval .mulhu lo 10).toNat := by omega
    rw [decide_eq_true (by omega)]; rfl
  · have k1 : (aluEval .mul hi 10).toNat + (aluEval .mulhu lo 10).toNat < 4294967296 := by omega
    rw [decide_eq_false (by omega)]; rfl

theorem u6_mul_ok (lo hi : Word) (h : 10 * (hi.toNat * 2 ^ 32 + lo.toNat) < 2 ^ 64) :
    (aluEval .add (aluEval .mul hi 10) (aluEval .mulhu lo 10)).toNat * 2 ^ 32 + (aluEval .mul lo 10).toNat =
      10 * (hi.toNat * 2 ^ 32 + lo.toNat) := by
  have := lo.isLt; have := hi.isLt
  have tA := u6_tmulhu lo; have tC := u6_tmul hi; have tD := u6_tmul lo
  have tS := u6_tadd (aluEval .mul hi 10) (aluEval .mulhu lo 10)
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl, show (2 : Nat) ^ 32 = 4294967296 from rfl] at *
  have k0 : (aluEval .mulhu lo 10).toNat * 4294967296 ≤ lo.toNat * 10 := by
    rw [tA]; exact Nat.div_mul_le_self _ _
  have k4 : (aluEval .mulhu lo 10).toNat < 10 := by omega
  have k5 : hi.toNat * 10 < 4294967296 := by omega
  have k3 : (aluEval .mul hi 10).toNat = hi.toNat * 10 := by omega
  have k1 : (aluEval .mul hi 10).toNat + (aluEval .mulhu lo 10).toNat < 4294967296 := by omega
  have k6 : (aluEval .mul lo 10).toNat = lo.toNat * 10 - (aluEval .mulhu lo 10).toNat * 4294967296 := by
    omega
  omega

theorem u6_add (lo hi d : Word) :
    branchTaken .beq (aluEval .and (aluEval .sltu (aluEval .add hi (aluEval .sltu (aluEval .add d lo) lo)) hi)
      (aluEval .sltu (aluEval .add d lo) lo)) 0 = decide (hi.toNat * 2 ^ 32 + lo.toNat + d.toNat < 2 ^ 64) := by
  have := lo.isLt; have := hi.isLt; have := d.isLt
  have tA := u6_tadd d lo
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl, show (2 : Nat) ^ 32 = 4294967296 from rfl] at *
  rcases u6_sltu (aluEval .add d lo) lo with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rw [e1]
  · have tB := u6_tadd hi 1
    have t1 : (1 : Word).toNat = 1 := rfl
    rcases u6_sltu (aluEval .add hi 1) hi with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;> rw [e2]
    · rw [decide_eq_false (by omega)]; rfl
    · rw [decide_eq_true (by omega)]; rfl
  · have k : lo.toNat + d.toNat < 4294967296 := by omega
    rw [decide_eq_true (by omega)]
    rcases u6_sltu (aluEval .add hi 0) hi with ⟨_, e2⟩ | ⟨_, e2⟩ <;> rw [e2] <;> rfl

theorem u6_add_ok (lo hi d : Word) (h : hi.toNat * 2 ^ 32 + lo.toNat + d.toNat < 2 ^ 64) :
    (aluEval .add hi (aluEval .sltu (aluEval .add d lo) lo)).toNat * 2 ^ 32 + (aluEval .add d lo).toNat =
      hi.toNat * 2 ^ 32 + lo.toNat + d.toNat := by
  have := lo.isLt; have := hi.isLt; have := d.isLt
  have tA := u6_tadd d lo
  have tB := u6_tadd hi (aluEval .sltu (aluEval .add d lo) lo)
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl, show (2 : Nat) ^ 32 = 4294967296 from rfl] at *
  rcases u6_sltu (aluEval .add d lo) lo with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rw [e1] at tB ⊢
  · have t1 : (1 : Word).toNat = 1 := rfl
    omega
  · have t1 : (0 : Word).toNat = 0 := rfl
    omega
theorem u6_dig : ∀ b : BitVec 8, isDigit b.toNat = true →
    aluEval .and (aluEval .add (b.zeroExtend 32) 0xFFFFFFD0) 0xFF = BitVec.ofNat 32 (b.toNat - 48) := by
  decide

theorem u6_dec (j : Nat) : aluEval .add (BitVec.ofNat 32 (j + 1)) 0xFFFFFFFF = BitVec.ofNat 32 j := by
  rw [ev_add, ← cl_succ, BitVec.add_assoc, show (1 : Word) + 0xFFFFFFFF = 0 from by decide]
  exact BitVec.add_zero _

/-- The registers the digit loop changes. -/
abbrev u6L : List (Fin 32) := [8, 9, a0, a1, a2, a3, a4]

theorem u6_loop {M : Word → BitVec 8} {Q : Post} {base : Word} :
    ∀ (j : Nat) (q : Word) (acc : Nat) (f : Fin 32 → Word), j < 2 ^ 32 → f 9 = BitVec.ofNat 32 j → f 8 = q →
      f a1 = 10 → (f a2).toNat * 2 ^ 32 + (f a0).toNat = acc → (memBytes M q j).all isDigit = true →
      (dvFrom acc (memBytes M q j) < 2 ^ 64 → ∀ g : Fin 32 → Word,
        (g a2).toNat * 2 ^ 32 + (g a0).toNat = dvFrom acc (memBytes M q j) → (∀ x, x ∉ u6L → g x = f x) →
        WP jsonU64Code base Q M 0x7A g) →
      (2 ^ 64 ≤ dvFrom acc (memBytes M q j) → ∀ g : Fin 32 → Word, (∀ x, x ∉ u6L → g x = f x) →
        WP jsonU64Code base Q M 0x6E g) →
      WP jsonU64Code base Q M 0x2C f := by
  intro j
  induction j with
  | zero =>
    intro q acc f _ h9 _ _ hacc _ Kok _
    refine WP.zero fun hz => ?_
    refine WP.branch u6_at_2c (fun _ => ?_) (fun e => ?_) <;> wn
    · have := (f a0).isLt; have := (f a2).isLt
      rw [memBytes_zero, dvFrom_nil] at Kok
      exact Kok (by rw [← hacc]; omega) f hacc fun _ _ => rfl
    · rw [h9, hz, br_beq0 (by decide)] at e; exact absurd e (by decide)
  | succ j ih =>
    intro q acc f hj h9 h8 h1 hacc hd Kok Kerr
    refine WP.zero fun hz => ?_
    rw [memBytes_succ] at Kok Kerr hd
    simp only [List.all_cons, Bool.and_eq_true] at hd
    rw [dvFrom_cons] at Kok Kerr
    refine WP.branch u6_at_2c (fun e => ?_) (fun _ => ?_) <;> wn
    · rw [h9, hz, br_beq0 hj] at e; exact absurd (of_decide_eq_true e) (by omega)
    refine WP.alu u6_at_2e ?_; wn
    refine WP.alu u6_at_32 ?_; wn
    refine WP.alu u6_at_36 ?_; wn
    refine WP.alu u6_at_3a ?_; wn
    refine WP.alu u6_at_3c ?_; wn
    refine WP.alu u6_at_40 ?_; wn
    refine WP.alu u6_at_44 ?_; wn
    have hle := le_dvFrom (memBytes M (q + 1) j) (10 * acc + ((M q).toNat - 48))
    refine WP.branch u6_at_46 (fun e => ?_) (fun e => ?_) <;> wn
    · rsimp at e; simp only [hz, h1, u6_mul] at e; rw [hacc] at e
      exact Kerr (by have := of_decide_eq_true e; omega) _ (by keepz hz)
    rsimp at e; simp only [hz, h1, u6_mul] at e; rw [hacc] at e
    have hm := u6_mul_ok (f a0) (f a2) (by rw [hacc]; have := of_decide_eq_false e; omega)
    refine WP.alu u6_at_48 ?_; wn
    refine WP.lbu u6_at_4c ?_; wn
    refine WP.aluImm u6_at_50 ?_; wn
    refine WP.aluImm u6_at_54 ?_; wn
    refine WP.alu u6_at_58 ?_; wn
    refine WP.alu u6_at_5a ?_; wn
    refine WP.alu u6_at_5e ?_; wn
    refine WP.alu u6_at_62 ?_; wn
    refine WP.aluImm u6_at_66 ?_; wn
    refine WP.alu u6_at_68 ?_; wn
    refine WP.aluImm u6_at_6a ?_; wn
    rw [h8, add_lit_zero, u6_dig _ hd.1, h1, h9, u6_dec]
    have hb := (M q).isLt
    have hdn : (BitVec.ofNat 32 ((M q).toNat - 48)).toNat = (M q).toNat - 48 := ofNat_tn (by omega)
    refine WP.branch u6_at_6c (fun e => ?_) (fun e => ?_) <;> wn
    · rsimp at e; simp only [hz, u6_add, hdn] at e
      have e' := of_decide_eq_true e
      rw [hm] at e'
      refine ih (q + 1) _ _ (by omega) (by rsimp) (by rsimp; rfl) (by rsimp; exact h1) ?_ hd.2
        (fun hV g hg hfg => Kok hV g hg fun x hx => ?_) (fun hV g hfg => Kerr hV g fun x hx => ?_)
      · rsimp; rw [u6_add_ok _ _ _ (by rw [hm, hdn]; exact e'), hm, hdn]; omega
      · rw [hfg x hx]; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        obtain ⟨n8, n9, n10, n11, n12, n13, n14⟩ := hx
        simp only [upd_app, n8, n9, n10, n11, n12, n13, n14, ↓reduceIte, ite_val_zero hz]
      · rw [hfg x hx]; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        obtain ⟨n8, n9, n10, n11, n12, n13, n14⟩ := hx
        simp only [upd_app, n8, n9, n10, n11, n12, n13, n14, ↓reduceIte, ite_val_zero hz]
    · rsimp at e; simp only [hz, u6_add, hdn] at e
      have e' := of_decide_eq_false e
      rw [hm] at e'
      exact Kerr (by omega) _ (by keepz hz)

/-- `out` holds `r` as a `Result<u64, TufError>` with `Err(Schema)`, and
only the 16 bytes at `out` changed. -/
def U64Res (M M' : Word → BitVec 8) (out : Word) : Option Nat → Prop
  | some v => (∀ x, Sep x 1 out 16 → M' x = M x) ∧ M' out = 0 ∧
      (memLoad32 M' (out + 12)).toNat * 2 ^ 32 + (memLoad32 M' (out + 8)).toNat = v
  | none => (∀ x, Sep x 1 out 16 → M' x = M x) ∧ M' out = 1 ∧ M' (out + 1) = 0x21

/-- `U64Res` after changes to the `k` bytes at `s`. -/
def U64ResF (M M' : Word → BitVec 8) (out s : Word) (k : Nat) (r : Option Nat) : Prop :=
  ∃ M1, Out M M1 s k ∧ U64Res M1 M' out r

section
variable {M M' M1 M2 Mp : Word → BitVec 8} {base out s p : Word} {f g0 : Fin 32 → Word}

theorem U64Res.outside {r : Option Nat} (h : U64Res M M' out r) : Out M M' out 16 := by
  rcases r with _ | _
  · exact h.1
  · exact h.1

theorem u64Res_ok (M : Word → BitVec 8) (out lo hi : Word) :
    U64Res M (memStore8 (memStore32 (memStore32 M (out + 8) lo) (out + 12) hi) out 0) out
      (some (hi.toNat * 2 ^ 32 + lo.toNat)) := by
  have s12 : Sep out 1 (out + 12) 4 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 12) (k := 4) (Or.inl (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have s8 : Sep out 1 (out + 8) 4 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 8) (k := 4) (Or.inl (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have s128 : Sep (out + 12) 4 (out + 8) 4 :=
    sep_offsets out (c := 12) (n := 4) (d := 8) (k := 4) (Or.inr (by decide)) (by decide) (by decide)
  refine ⟨fun x hx => ?_, memStore8_same _ _ _, ?_⟩
  · have t12 : Sep (out + 12) 4 x 1 := (hx.subR (c := 12) (l := 4) (by decide)).symm
    have t8 : Sep (out + 8) 4 x 1 := (hx.subR (c := 8) (l := 4) (by decide)).symm
    rw [memStore8_ne (sep_byte0 hx (by decide)), memStore32_get_sep t12, memStore32_get_sep t8]
  · rw [memLoad32_store8_sep s12, memLoad32_store32_same, memLoad32_store8_sep s8, memLoad32_store32_sep s128,
      memLoad32_store32_same]

theorem u64Res_err (M : Word → BitVec 8) (out : Word) :
    U64Res M (memStore8 (memStore8 M (out + 1) 0x21) out 1) out none := by
  refine ⟨fun x hx => ?_, memStore8_same _ _ _, ?_⟩
  · rw [memStore8_ne (sep_byte0 hx (by decide)), memStore8_ne (sep_byte1 hx (by decide))]
  · rw [memStore8_ne (ne_add_one out), memStore8_same]

/-- The registers `Value::u64` changes before its epilogue restores the saved ones. -/
abbrev u6E : List (Fin 32) := jClob ++ [ra, sp, 8, 9, 18]

/-- The frame offsets of the saved registers. -/
abbrev u6Cs : List Nat := [0x10, 0x14, 0x18, 0x1C]

/-- The saved registers in the frame at `s`. -/
def U6Saved (s : Word) (g0 : Fin 32 → Word) (M1 : Word → BitVec 8) : Prop :=
  memLoad32 M1 (s + BitVec.ofNat 32 0x1C) = g0 ra ∧ memLoad32 M1 (s + BitVec.ofNat 32 0x18) = g0 8 ∧
    memLoad32 M1 (s + BitVec.ofNat 32 0x14) = g0 9 ∧ memLoad32 M1 (s + BitVec.ofNat 32 0x10) = g0 18

/-- Memory after the prologue. -/
def u6M1 (M : Word → BitVec 8) (s : Word) (g0 : Fin 32 → Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 M (s + 0x1C) (g0 ra)) (s + 0x18) (g0 8)) (s + 0x14) (g0 9))
    (s + 0x10) (g0 18)

theorem u6_pro (M : Word → BitVec 8) (s : Word) (g0 : Fin 32 → Word) :
    Out M (u6M1 M s g0) s 32 ∧ U6Saved s g0 (u6M1 M s g0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ((((out_store32 _ _ _).widen (d := 0x1C) (by decide)).trans
      ((out_store32 _ _ _).widen (d := 0x18) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x14) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x10) (by decide))
  · exact ld_skip 0x1C 0x10 (by decide) (by decide) (by decide) (ld_skip 0x1C 0x14 (by decide) (by decide)
      (by decide) (ld_skip 0x1C 0x18 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)))
  · exact ld_skip 0x18 0x10 (by decide) (by decide) (by decide) (ld_skip 0x18 0x14 (by decide) (by decide)
      (by decide) (memLoad32_store32_same _ _ _))
  · exact ld_skip 0x14 0x10 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)
  · exact memLoad32_store32_same _ _ _

/-- The function returned to `ret` with `r` at `out`, changed only the 32
bytes at `s` besides, and kept every register outside `jClob`. -/
abbrev U6Post (ret : Word) (M : Word → BitVec 8) (out s : Word) (r : Option Nat) (g0 : Fin 32 → Word) : Post :=
  RPost ret (fun M' => U64ResF M M' out s 32 r) g0

theorem u6_epi {r : Option Nat} (h18 : f 18 = out) (hsp : f sp = s) (hS : Slots u6Cs s Mp M2)
    (hv : U6Saved s g0 Mp) (hsp0 : g0 sp = s + BitVec.ofNat 32 32) (hret : g0 ra &&& ~~~1 = g0 ra)
    (hal : s.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ u6E → f x = g0 x)
    (hso : Sep out 16 s 32) (hsc : Sep out 16 base jsonU64Code.length)
    (hR : U64ResF M (memStore8 M2 out ((f a1).extractLsb' 0 8)) out s 32 r) :
    WP jsonU64Code base (U6Post (g0 ra) M out s r g0) M2 0x82 f := by
  have h0 : Sep out 1 base jsonU64Code.length := by
    have := hsc.shift (c := 0) (by decide); rwa [add_ofNat_zero] at this
  have ho1 : Sep out 1 s 32 := by
    have := hso.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
  refine WP.sb u6_at_82 (by rw [h18, add_lit_zero]; exact h0) ?_; wn
  rw [h18, add_lit_zero]
  have hS' := hS.out (out_store8 M2 out ((f a1).extractLsb' 0 8)) (slots_sep_out ho1 (by decide))
  obtain ⟨v1, v2, v3, v4⟩ := hv
  have e1 : memLoad32 (memStore8 M2 out ((f a1).extractLsb' 0 8)) (s + 0x1C) = g0 ra := (hS' 0x1C (by decide)).trans v1
  have e2 : memLoad32 (memStore8 M2 out ((f a1).extractLsb' 0 8)) (s + 0x18) = g0 8 := (hS' 0x18 (by decide)).trans v2
  have e3 : memLoad32 (memStore8 M2 out ((f a1).extractLsb' 0 8)) (s + 0x14) = g0 9 := (hS' 0x14 (by decide)).trans v3
  have e4 : memLoad32 (memStore8 M2 out ((f a1).extractLsb' 0 8)) (s + 0x10) = g0 18 := (hS' 0x10 (by decide)).trans v4
  refine WP.lw u6_at_86 (by rw [hsp]; exact aligned_add hal (k := 0x1C) (by decide)) ?_; wn
  refine WP.lw u6_at_88 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x18) (by decide)) ?_; wn
  refine WP.lw u6_at_8a (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x14) (by decide)) ?_; wn
  refine WP.lw u6_at_8c (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x10) (by decide)) ?_; wn
  refine WP.aluImm u6_at_8e ?_; wn
  refine WP.ret u6_at_90 ⟨?_, hR, ?_⟩
  · rsimp; rw [hsp, e1, add_lit_zero, hret]
  refine frame_of (L2 := [ra, sp, 8, 9, 18]) (by keepz hz0) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> rsimp
  · rw [hsp, e1]
  · rw [hsp, hsp0]; rfl
  · rw [hsp, e2]
  · rw [hsp, e3]
  · rw [hsp, e4]

theorem u6_err (h18 : f 18 = out) (hsp : f sp = s) (hO : Out M M2 s 32) (hS : Slots u6Cs s Mp M2)
    (hv : U6Saved s g0 Mp) (hsp0 : g0 sp = s + BitVec.ofNat 32 32) (hret : g0 ra &&& ~~~1 = g0 ra)
    (hal : s.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ u6E → f x = g0 x)
    (hso : Sep out 16 s 32) (hsc : Sep out 16 base jsonU64Code.length) :
    WP jsonU64Code base (U6Post (g0 ra) M out s none g0) M2 0x6E f := by
  refine WP.zero fun hz => ?_
  have ho1 : Sep (out + 1) 1 s 32 := hso.shift (c := 1) (by decide)
  refine WP.aluImm u6_at_6e ?_; wn
  refine WP.sb u6_at_72 (by (try rsimp); rw [h18]; exact hsc.shift (c := 1) (by decide)) ?_; wn
  refine WP.aluImm u6_at_76 ?_; wn
  refine WP.jal u6_at_78 (by decide) ?_; wn
  rw [h18]
  refine u6_epi (by (try rsimp); exact h18) (by (try rsimp); exact hsp)
    (hS.out (out_store8 _ _ _) (slots_sep_out ho1 (by decide))) hv hsp0 hret hal hz0 (by keepz hz0) hso hsc ?_
  rsimp
  simp only [ev0, ev_mv hz]
  exact ⟨M2, hO, u64Res_err M2 out⟩

theorem u6_ok {v : Nat} (h18 : f 18 = out) (hsp : f sp = s) (hv2 : (f a2).toNat * 2 ^ 32 + (f a0).toNat = v)
    (hO : Out M M2 s 32) (hS : Slots u6Cs s Mp M2)
    (hv : U6Saved s g0 Mp) (hsp0 : g0 sp = s + BitVec.ofNat 32 32) (hret : g0 ra &&& ~~~1 = g0 ra)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ u6E → f x = g0 x)
    (hso : Sep out 16 s 32) (hsc : Sep out 16 base jsonU64Code.length) :
    WP jsonU64Code base (U6Post (g0 ra) M out s (some v) g0) M2 0x7A f := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm u6_at_7a ?_; wn
  refine WP.alu u6_at_7c ?_; wn
  refine WP.sw u6_at_7e (by (try rsimp); simp only [ev0, h18]; exact aligned_add halo (k := 8) (by decide))
    (by (try rsimp); simp only [ev0, h18]; exact hsc.sub (c := 8) (by decide)) ?_; wn
  refine WP.sw u6_at_80 (by (try rsimp); simp only [ev0, h18]; exact aligned_add halo (k := 12) (by decide))
    (by (try rsimp); simp only [ev0, h18]; exact hsc.sub (c := 12) (by decide)) ?_; wn
  have hO2 : Out M2 (memStore32 (memStore32 M2 (out + 8) (f a0)) (out + 12) (f a2)) out 16 :=
    ((out_store32 _ _ _).widen (d := 8) (by decide)).trans ((out_store32 _ _ _).widen (d := 12) (by decide))
  (try rsimp)
  (try simp only [ev0, ev_mv hz, h18])
  refine u6_epi (by (try rsimp); exact h18) (by (try rsimp); exact hsp)
    (hS.out hO2 (slots_sep_out hso (by decide))) hv hsp0 hret hal hz0 (by keepz hz0) hso hsc ?_
  (try rsimp)
  (try simp only [ev0, ev_mv hz])
  rw [show BitVec.extractLsb' 0 8 (0 : Word) = 0 from rfl, ← hv2]
  exact ⟨M2, hO, u64Res_ok M2 out (f a0) (f a2)⟩

end

theorem u6_zadd (x : Word) : (0 : Word) + x = x := BitVec.zero_add x

theorem u6L_sub : ∀ x : Fin 32, x ∉ u6E → x ∉ u6L := by decide

theorem u64Val_digits {d : Bytes} (h0 : d ≠ []) (hd : d.all isDigit = true) :
    u64Val d = if dvFrom 0 d < 2 ^ 64 then some (dvFrom 0 d) else none := by
  rw [u64Val, ite_eq_right_of_eq_false _ _ (eq_false h0), ite_eq_right_of_eq_false _ _ (eq_false (by rw [hd]; exact Bool.noConfusion)), digitsValue_eq]

section
variable {M : Word → BitVec 8} {base out s p : Word} {f : Fin 32 → Word}

theorem u6_wp {n : Nat} (h0 : f a0 = out) (h1 : f a1 = p) (h2 : f a2 = BitVec.ofNat 32 n)
    (hsp : f sp = s + BitVec.ofNat 32 32) (hn : n < 2 ^ 32) (hret : f ra &&& ~~~1 = f ra)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hb : base.toNat % 2 = 0)
    (hca : CodeIn M (base + 0x158) allAsciiDigitCode) (hSc : Sep s 32 base jsonU64Code.length)
    (hSa : Sep s 32 (base + 0x158) allAsciiDigitCode.length) (hSp : Sep s 32 p n) (hso : Sep out 16 s 32)
    (hsc : Sep out 16 base jsonU64Code.length) :
    WP jsonU64Code base (U6Post (f ra) M out s (u64Val (memBytes M p n)) f) M 0 f := by
  refine WP.zero fun hz => ?_
  have esp : aluEval .add (f sp) 0xFFFFFFE0 = s := by
    rw [hsp, ev_add, BitVec.add_assoc, show BitVec.ofNat 32 32 + (0xFFFFFFE0 : Word) = 0 from by decide]
    exact BitVec.add_zero s
  refine WP.aluImm u6_at_0 ?_; wn
  rw [esp]
  refine WP.sw u6_at_2 (by (try rsimp); exact aligned_add hal (k := 0x1C) (by decide))
    (by (try rsimp); exact hSc.sub (c := 0x1C) (by decide)) ?_; wn
  refine WP.sw u6_at_4 (by (try rsimp); exact aligned_add hal (k := 0x18) (by decide))
    (by (try rsimp); exact hSc.sub (c := 0x18) (by decide)) ?_; wn
  refine WP.sw u6_at_6 (by (try rsimp); exact aligned_add hal (k := 0x14) (by decide))
    (by (try rsimp); exact hSc.sub (c := 0x14) (by decide)) ?_; wn
  refine WP.sw u6_at_8 (by (try rsimp); exact aligned_add hal (k := 0x10) (by decide))
    (by (try rsimp); exact hSc.sub (c := 0x10) (by decide)) ?_; wn
  change WP jsonU64Code base _ (u6M1 M s f) 0xA _
  obtain ⟨hO1, hv⟩ := u6_pro M s f
  refine WP.alu u6_at_a ?_; wn
  refine WP.branch u6_at_c (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [h2, br_beq0 hn] at e
    obtain rfl : n = 0 := of_decide_eq_true e
    rw [memBytes_zero, u64Val, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    exact u6_err (by (try rsimp); simp only [ev0, ev_mv hz, h0, u6_zadd]) (by try rsimp) hO1 (Slots.refl _ _ _) hv hsp
      hret hal hz (by keepz hz) hso hsc
  rsimp at e
  rw [h2, br_beq0 hn] at e
  have hpos : n ≠ 0 := of_decide_eq_false e
  refine WP.alu u6_at_e ?_; wn
  refine WP.alu u6_at_10 ?_; wn
  refine WP.alu u6_at_12 ?_; wn
  refine WP.sw u6_at_16 (by (try rsimp); exact aligned_add hal (k := 8) (by decide))
    (by (try rsimp); exact hSc.sub (c := 8) (by decide)) ?_; wn
  refine WP.sw u6_at_18 (by (try rsimp); exact aligned_add hal (k := 0xC) (by decide))
    (by (try rsimp); exact hSc.sub (c := 0xC) (by decide)) ?_; wn
  refine WP.aluImm u6_at_1a ?_; wn
  simp only [ev0, h1, h2]
  simp only [ev_add]
  generalize hM3 : memStore32 (memStore32 (u6M1 M s f) (s + 8) p) (s + 12) (p + BitVec.ofNat 32 n) = M3
  have hO3 : Out M M3 s 32 := by
    rw [← hM3]
    exact hO1.trans (((out_store32 _ _ _).widen (d := 8) (by decide)).trans
      ((out_store32 _ _ _).widen (d := 12) (by decide)))
  have hS3 : Slots u6Cs s (u6M1 M s f) M3 := by
    rw [← hM3]
    exact ((Slots.refl _ _ _).out (out_store32 _ _ _) (slots_sep s (d := 8) (l := 4) (by decide) (by decide))).out
      (out_store32 _ _ _) (slots_sep s (d := 12) (l := 4) (by decide) (by decide))
  have hp3 : memLoad32 M3 (s + 8) = p := by
    have t : Sep (s + 12) 4 (s + 8) 4 :=
      sep_offsets s (c := 12) (n := 4) (d := 8) (k := 4) (Or.inr (by decide)) (by decide) (by decide)
    rw [← hM3, memLoad32_store32_sep t, memLoad32_store32_same]
  have he3 : memLoad32 M3 (s + 8 + 4) = p + BitVec.ofNat 32 n := by
    rw [BitVec.add_assoc, ← hM3]; exact memLoad32_store32_same _ _ _
  refine WP.callAad (tb := base + 0x158) (it := s + 8) (p := p) (n := n) u6_at_1c u6_at_20
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hb 0x158 (by decide)) (by decide)
    (hO3.codeIn hca hSa) (by (try rsimp); try rfl) hn (aligned_add hal (k := 8) (by decide)) hp3 he3
    (hSp.sub (c := 8) (l := 4) (by decide)) (hSa.sub (c := 8) (l := 4) (by decide))
    (hSc.sub (c := 8) (l := 4) (by decide)) fun m2 hOa r0 => ?_
  rw [hO3.bytes hSp] at r0
  have hOm : Out M m2.mem s 32 := hO3.trans (hOa.widen (d := 8) (by decide))
  have hSm : Slots u6Cs s (u6M1 M s f) m2.mem :=
    hS3.out hOa (slots_sep s (d := 8) (l := 4) (by decide) (by decide))
  have hbm : memBytes m2.mem p n = memBytes M p n := hOm.bytes hSp
  have hne : memBytes M p n ≠ [] := fun h => hpos (by
    have := memBytes_length M p n; rw [h] at this; exact this.symm)
  by_cases hd : (memBytes M p n).all isDigit = true
  · rw [u64Val_digits hne hd]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hd)] at r0
    refine WP.branch u6_at_24 (fun e => ?_) (fun _ => ?_) <;> wn
    · rsimp at e; simp only [r0, hz] at e; exact absurd e (by decide)
    refine WP.aluImm u6_at_26 ?_; wn
    refine WP.aluImm u6_at_28 ?_; wn
    refine WP.aluImm u6_at_2a ?_; wn
    refine u6_loop n p 0 _ hn (by (try rsimp); (try simp only [ev0, ev_mv hz, u6_zadd]))
      (by (try rsimp); (try simp only [ev0, ev_mv hz, u6_zadd])) (by (try rsimp); (try simp only [ev0, ev_mv hz, u6_zadd]))
      (by (try rsimp); (try simp only [ev0, ev_mv hz, u6_zadd]); try rfl) (by rw [hbm]; exact hd)
      (fun hV g hg hfg => ?_) (fun hV g hfg => ?_)
    · rw [hbm] at hV hg
      rw [ite_eq_left_of_eq_true _ _ (eq_true hV)]
      refine u6_ok ((hfg 18 (by decide)).trans (by (try rsimp); simp only [ev0, ev_mv hz, h0, u6_zadd]))
        ((hfg sp (by decide)).trans (by try rsimp)) hg hOm hSm hv hsp hret hal halo hz ?_ hso hsc
      intro x hx
      rw [hfg x (u6L_sub x hx)]
      revert x
      keepz hz
    · rw [hbm] at hV
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      refine u6_err ((hfg 18 (by decide)).trans (by (try rsimp); simp only [ev0, ev_mv hz, h0, u6_zadd]))
        ((hfg sp (by decide)).trans (by try rsimp)) hOm hSm hv hsp hret hal hz ?_ hso hsc
      intro x hx
      rw [hfg x (u6L_sub x hx)]
      revert x
      keepz hz
  · have hd' : (memBytes M p n).all isDigit = false := by
      cases h : (memBytes M p n).all isDigit
      · rfl
      · exact absurd h hd
    rw [u64Val, ite_eq_right_of_eq_false _ _ (eq_false hne), ite_eq_left_of_eq_true _ _ (eq_true hd')]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hd)] at r0
    refine WP.branch u6_at_24 (fun _ => ?_) (fun e => ?_) <;> wn
    · exact u6_err (by (try rsimp); simp only [ev0, ev_mv hz, h0, u6_zadd]) (by try rsimp) hOm hSm hv hsp hret hal hz
        (by keepz hz) hso hsc
    · rsimp at e; simp only [r0, hz] at e; exact absurd e (by decide)

end

/-- `Value::u64` on the `n` bytes at `p`: stores `u64Val` of them at `out`
as a `Result<u64, TufError>` with `Err(Schema)` (`0x21`), changes no memory
outside the 16 bytes at `out` and the 32 bytes below `sp`, and keeps every
register outside `jClob`. -/
theorem jsonU64_correct (m : Machine) {base retAddr out s p : Word} {n : Nat}
    (hb : base.toNat % 2 = 0) (hc : CodeIn m.mem base jsonU64Code)
    (hca : CodeIn m.mem (base + 0x158) allAsciiDigitCode) (hpc : m.pc = base) (ha0 : reg m a0 = out)
    (ha1 : reg m a1 = p) (ha2 : reg m a2 = BitVec.ofNat 32 n) (hsp : reg m sp = s + BitVec.ofNat 32 32)
    (hn : n < 2 ^ 32) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hSc : Sep s 32 base jsonU64Code.length)
    (hSa : Sep s 32 (base + 0x158) allAsciiDigitCode.length) (hSp : Sep s 32 p n) (hso : Sep out 16 s 32)
    (hsc : Sep out 16 base jsonU64Code.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      U64ResF m.mem m'.mem out s 32 (u64Val (memBytes m.mem p n)) ∧
      ∀ r, r ∉ jClob → reg m' r = reg m r := by
  obtain ⟨m', st, hpc', hR, hfr⟩ := WP.run (u6_wp ha0 ha1 ha2 hsp hn (by rw [hra]; exact hret) hal halo hb hca
    hSc hSa hSp hso hsc) hb hc hpc
  exact ⟨m', st, hpc'.trans hra, hR, hfr⟩

end C3.RV32
