import C3BootProofs.Proofs.JsonWp
import C3BootProofs.Proofs.JsonModel

/-!
# `json::string_end`, as compiled

`string_end(doc, pos, mode)` stores `Ok` of the position after the string
whose opening quote is at `pos`, or `Err(Json)`, at `out`. It is a leaf
with no frame. `a4` holds the mode: 0 for strict, 1 for canonical.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem sen_at_0 : fetchRel jsonStringEndCode 0x0 = some (.aluImm .add a6 a3 0x1, 4) := by decide
theorem sen_at_4 : fetchRel jsonStringEndCode 0x4 = some (.branch .beq a6 x0 0x40, 4) := by decide
theorem sen_at_8 : fetchRel jsonStringEndCode 0x8 = some (.branch .bgeu a3 a2 0x3C, 4) := by decide
theorem sen_at_c : fetchRel jsonStringEndCode 0xC = some (.aluImm .add (6 : Fin 32) x0 0x0, 2) := by decide
theorem sen_at_e : fetchRel jsonStringEndCode 0xE = some (.alu .add a1 a1 a6, 2) := by decide
theorem sen_at_10 : fetchRel jsonStringEndCode 0x10 = some (.aluImm .xor (5 : Fin 32) a3 0xFFFFFFFF, 4) := by decide
theorem sen_at_14 : fetchRel jsonStringEndCode 0x14 = some (.alu .add (5 : Fin 32) (5 : Fin 32) a2, 2) := by decide
theorem sen_at_16 : fetchRel jsonStringEndCode 0x16 = some (.aluImm .add (17 : Fin 32) x0 0x1F, 2) := by decide
theorem sen_at_18 : fetchRel jsonStringEndCode 0x18 = some (.branch .beq (5 : Fin 32) (6 : Fin 32) 0x2C, 4) := by decide
theorem sen_at_1c : fetchRel jsonStringEndCode 0x1C = some (.load .lbu a2 a1 0x0, 4) := by decide
theorem sen_at_20 : fetchRel jsonStringEndCode 0x20 = some (.aluImm .add a5 a2 0xFFFFFFDE, 4) := by decide
theorem sen_at_24 : fetchRel jsonStringEndCode 0x24 = some (.branch .beq a5 x0 0x14, 2) := by decide
theorem sen_at_26 : fetchRel jsonStringEndCode 0x26 = some (.aluImm .add a5 a2 0xFFFFFFA4, 4) := by decide
theorem sen_at_2a : fetchRel jsonStringEndCode 0x2A = some (.branch .beq a5 x0 0x1A, 2) := by decide
theorem sen_at_2c : fetchRel jsonStringEndCode 0x2C = some (.aluImm .add (6 : Fin 32) (6 : Fin 32) 0x1, 2) := by decide
theorem sen_at_2e : fetchRel jsonStringEndCode 0x2E = some (.aluImm .add a1 a1 0x1, 2) := by decide
theorem sen_at_30 : fetchRel jsonStringEndCode 0x30 = some (.branch .bne a4 x0 0xFFFFFFE8, 2) := by decide
theorem sen_at_32 : fetchRel jsonStringEndCode 0x32 = some (.branch .bgeu (17 : Fin 32) a2 0x12, 4) := by decide
theorem sen_at_36 : fetchRel jsonStringEndCode 0x36 = some (.jal x0 0xFFFFFFE2, 2) := by decide
theorem sen_at_38 : fetchRel jsonStringEndCode 0x38 = some (.alu .add a2 (6 : Fin 32) a6, 4) := by decide
theorem sen_at_3c : fetchRel jsonStringEndCode 0x3C = some (.branch .bgeu a3 a2 0x8, 4) := by decide
theorem sen_at_40 : fetchRel jsonStringEndCode 0x40 = some (.aluImm .add a2 a2 0x1, 2) := by decide
theorem sen_at_42 : fetchRel jsonStringEndCode 0x42 = some (.branch .bne a2 x0 0x12, 2) := by decide
theorem sen_at_44 : fetchRel jsonStringEndCode 0x44 = some (.aluImm .add a1 x0 0x20, 4) := by decide
theorem sen_at_48 : fetchRel jsonStringEndCode 0x48 = some (.store .sb a0 a1 0x1, 4) := by decide
theorem sen_at_4c : fetchRel jsonStringEndCode 0x4C = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem sen_at_4e : fetchRel jsonStringEndCode 0x4E = some (.store .sb a0 a1 0x0, 4) := by decide
theorem sen_at_52 : fetchRel jsonStringEndCode 0x52 = some (.jalr x0 ra 0x0, 2) := by decide
theorem sen_at_54 : fetchRel jsonStringEndCode 0x54 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem sen_at_56 : fetchRel jsonStringEndCode 0x56 = some (.store .sw a0 a2 0x4, 2) := by decide
theorem sen_at_58 : fetchRel jsonStringEndCode 0x58 = some (.jal x0 0xFFFFFFF6, 2) := by decide

/-- The register `a4` holds for `mode`: canonical is 1. -/
def modeW (c : Bool) : Word := if c then 1 else 0

theorem br_mode (c : Bool) : branchTaken .bne (modeW c) 0 = c := by cases c <;> rfl

theorem sen_q : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFFDE) 0 = (b.toNat == 34) := by decide

theorem sen_bs : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFFA4) 0 = (b.toNat == 92) := by decide

theorem sen_ctl : ∀ b : BitVec 8, branchTaken .bgeu 31 (b.zeroExtend 32) = decide (b.toNat < 32) := by
  decide

/-- The registers `string_end` may change. -/
abbrev seClob : List (Fin 32) := [a1, a2, a5, a6, t0, t1, a7]

/-- `string_end` returned to `ret` with `r` at `out`. -/
def sePost (ret : Word) (M : Word → BitVec 8) (out : Word) (r : Option Nat) (g0 : Fin 32 → Word) : Post :=
  fun pc M' g => pc = ret ∧ UsizeRes M M' out r ∧ ∀ x, x ∉ seClob → g x = g0 x

section
variable {M : Word → BitVec 8} {base ret out : Word} {f g0 : Fin 32 → Word}

theorem sen_err (h0 : f a0 = out) (hra : f ra = ret) (hret : ret &&& ~~~1 = ret)
    (hsep : Sep out 8 base jsonStringEndCode.length) (hfr : ∀ x, x ∉ seClob → f x = g0 x) :
    WP jsonStringEndCode base (sePost ret M out none g0) M 0x44 f := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm sen_at_44 ?_; wn
  refine WP.sb sen_at_48 (by rsimp; rw [h0]; exact hsep.shift (c := 1) (by decide)) ?_; wn
  refine WP.aluImm sen_at_4c ?_; wn
  refine WP.sb sen_at_4e (by rsimp; rw [h0]; exact hsep.shift (c := 0) (by decide)) ?_; wn
  refine WP.ret sen_at_52 ⟨?_, ?_, ?_⟩
  · rsimp; rw [hra, add_lit_zero, hret]
  · rw [h0, hz, add_lit_zero]; exact usizeRes_err M out
  · keep hz

theorem sen_ok {i pos : Nat} (h0 : f a0 = out) (hra : f ra = ret) (hret : ret &&& ~~~1 = ret)
    (hal : out.toNat % 4 = 0) (hsep : Sep out 8 base jsonStringEndCode.length)
    (hfr : ∀ x, x ∉ seClob → f x = g0 x) (ht1 : f t1 = BitVec.ofNat 32 i)
    (h6 : f a6 = BitVec.ofNat 32 (pos + 1)) (h3 : f a3 = BitVec.ofNat 32 pos) (hlt : pos + 1 + i + 1 < 2 ^ 32) :
    WP jsonStringEndCode base (sePost ret M out (some (pos + 1 + i + 1)) g0) M 0x38 f := by
  refine WP.zero fun hz => ?_
  have hv : aluEval .add (f 6) (f a6) = BitVec.ofNat 32 (pos + 1 + i) := by
    rw [ht1, h6, ev_add, ofNat_add_ofNat, Nat.add_comm i]
  refine WP.alu sen_at_38 ?_; wn
  refine WP.branch sen_at_3c (fun e => ?_) (fun _ => ?_) <;> wn
  · rsimp at e
    rw [h3, hv, br_bgeu (by omega) (by omega)] at e
    exact absurd (not_dec_true e) (by omega)
  refine WP.aluImm sen_at_40 ?_; wn
  refine WP.branch sen_at_42 (fun _ => ?_) (fun e => ?_) <;> wn
  · refine WP.aluImm sen_at_54 ?_; wn
    refine WP.sw sen_at_56 (by rsimp; rw [h0]; exact aligned_add hal (k := 4) (by decide))
      (by rsimp; rw [h0]; exact hsep.sub (c := 4) (by decide)) ?_; wn
    refine WP.jal sen_at_58 (by decide) ?_; wn
    refine WP.sb sen_at_4e (by rsimp; rw [h0]; exact hsep.shift (c := 0) (by decide)) ?_; wn
    refine WP.ret sen_at_52 ⟨?_, ?_, ?_⟩
    · rsimp; rw [hra, add_lit_zero, hret]
    · rw [h0, add_lit_zero, hv, ev_add, cl_succ]; exact usizeRes_ok M out _
    · keep hz
  · rsimp at e
    rw [hv, ev_add, cl_succ, br_bne0 (by omega)] at e
    exact absurd (not_dec_false e) (by omega)

theorem sen_loop {c : Bool} {pos R : Nat} (hret : ret &&& ~~~1 = ret) (hal : out.toNat % 4 = 0)
    (hsep : Sep out 8 base jsonStringEndCode.length) (hR : pos + 1 + R < 2 ^ 32) :
    ∀ (j i : Nat) (f : Fin 32 → Word) (q : Word), i + j = R → f t1 = BitVec.ofNat 32 i → f a1 = q →
      f a0 = out → f ra = ret → f a6 = BitVec.ofNat 32 (pos + 1) → f a3 = BitVec.ofNat 32 pos →
      f a4 = modeW c → f t0 = BitVec.ofNat 32 R → f a7 = 31 → (∀ x, x ∉ seClob → f x = g0 x) →
      WP jsonStringEndCode base
        (sePost ret M out ((strScan c (memBytes M q j) i).map fun k => pos + 1 + k + 1) g0) M 0x18 f
  | 0, i, f, q, hij, ht1, _, h0, hra, _, _, _, ht0, _, hfr => by
    refine WP.branch sen_at_18 (fun _ => ?_) (fun e => ?_) <;> wn
    · simp only [memBytes_zero, strScan, Option.map_none]; exact sen_err h0 hra hret hsep hfr
    · rw [ht0, ht1, br_beq (by omega) (by omega)] at e
      exact absurd (of_decide_eq_false e) (by omega)
  | j + 1, i, f, q, hij, ht1, h1, h0, hra, h6, h3, h4, ht0, h7, hfr => by
    refine WP.zero fun hz => ?_
    refine WP.branch sen_at_18 (fun e => ?_) (fun _ => ?_) <;> wn
    · rw [ht0, ht1, br_beq (by omega) (by omega)] at e
      exact absurd (of_decide_eq_true e) (by omega)
    refine WP.lbu sen_at_1c ?_; wn
    refine WP.aluImm sen_at_20 ?_; wn
    rw [h1, add_lit_zero, memBytes_succ]
    refine WP.branch sen_at_24 (fun e => ?_) (fun e => ?_) <;> wn
    · rsimp at e
      rw [sen_q] at e
      simp only [strScan, e, ↓reduceIte, Option.map_some]
      exact sen_ok (by rsimp; exact h0) (by rsimp; exact hra) hret hal hsep (by keep hz) (by rsimp; exact ht1)
        (by rsimp; exact h6) (by rsimp; exact h3) (by omega)
    rsimp at e
    rw [sen_q] at e
    refine WP.aluImm sen_at_26 ?_; wn
    refine WP.branch sen_at_2a (fun e2 => ?_) (fun e2 => ?_) <;> wn
    · rsimp at e2
      rw [sen_bs] at e2
      simp only [strScan, e, e2, Bool.false_eq_true, ↓reduceIte, Option.map_none]
      exact sen_err (by rsimp; exact h0) (by rsimp; exact hra) hret hsep (by keep hz)
    rsimp at e2
    rw [sen_bs] at e2
    refine WP.aluImm sen_at_2c ?_; wn
    refine WP.aluImm sen_at_2e ?_; wn
    have hnext : ∀ g : Fin 32 → Word, g t1 = BitVec.ofNat 32 (i + 1) → g a1 = q + 1 → g a0 = out →
        g ra = ret → g a6 = BitVec.ofNat 32 (pos + 1) → g a3 = BitVec.ofNat 32 pos → g a4 = modeW c →
        g t0 = BitVec.ofNat 32 R → g a7 = 31 → (∀ x, x ∉ seClob → g x = g0 x) →
        WP jsonStringEndCode base
          (sePost ret M out ((strScan c (memBytes M (q + 1) j) (i + 1)).map fun k => pos + 1 + k + 1) g0)
          M 0x18 g :=
      fun g => sen_loop hret hal hsep hR j (i + 1) g (q + 1) (by omega)
    refine WP.branch sen_at_30 (fun e3 => ?_) (fun e3 => ?_) <;> wn
    · rsimp at e3
      rw [h4, br_mode] at e3
      subst e3
      simp only [strScan, e, e2, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_and]
      refine hnext _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        first | (keep hz; done) | (rsimp; first | assumption | (rw [ht1]; exact cl_succ i) | (rw [h1]; rfl))
    rsimp at e3
    rw [h4, br_mode] at e3
    subst e3
    refine WP.branch sen_at_32 (fun e4 => ?_) (fun e4 => ?_) <;> wn
    · rsimp at e4
      rw [h7, sen_ctl] at e4
      simp only [strScan, e, e2, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and,
        decide_eq_true_eq.mp e4, decide_true, Option.map_none]
      exact sen_err (by rsimp; exact h0) (by rsimp; exact hra) hret hsep (by keep hz)
    rsimp at e4
    rw [h7, sen_ctl] at e4
    refine WP.jal sen_at_36 (by decide) ?_; wn
    simp only [strScan, e, e2, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, e4]
    refine hnext _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      first | (keep hz; done) | (rsimp; first | assumption | (rw [ht1]; exact cl_succ i) | (rw [h1]; rfl))

theorem sen_wp {c : Bool} {p : Word} {n pos : Nat} (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32)
    (h0 : f a0 = out) (h1 : f a1 = p) (h2 : f a2 = BitVec.ofNat 32 n) (h3 : f a3 = BitVec.ofNat 32 pos)
    (h4 : f a4 = modeW c) (hra : f ra = ret) (hret : ret &&& ~~~1 = ret) (hal : out.toNat % 4 = 0)
    (hsep : Sep out 8 base jsonStringEndCode.length) :
    WP jsonStringEndCode base (sePost ret M out (stringEnd c (memBytes M p n) pos) f) M 0 f := by
  refine WP.zero fun hz => ?_
  have hfr0 : ∀ x, x ∉ seClob → f x = f x := fun _ _ => rfl
  have hlen : (memBytes M p n).length = n := memBytes_length M p n
  refine WP.aluImm sen_at_0 ?_; wn
  refine WP.branch sen_at_4 (fun e => ?_) (fun _ => ?_) <;> wn
  · rsimp at e
    rw [h3, ev_add, cl_succ] at e
    have hp1 : pos + 1 = 2 ^ 32 := by
      by_cases h : pos + 1 < 2 ^ 32
      · rw [br_beq0 h] at e; exact absurd (of_decide_eq_true e) (by omega)
      · omega
    have hle : (memBytes M p n).length ≤ pos := by omega
    simp only [stringEnd, hle, ↓reduceIte]
    exact sen_err (by rsimp; exact h0) (by rsimp; exact hra) hret hsep (by keep hz)
  refine WP.branch sen_at_8 (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [h3, h2, br_bgeu hpos hn] at e
    have hle : (memBytes M p n).length ≤ pos := by have := not_dec_true e; omega
    simp only [stringEnd, hle, ↓reduceIte]
    exact sen_err (by rsimp; exact h0) (by rsimp; exact hra) hret hsep (by keep hz)
  rsimp at e
  rw [h3, h2, br_bgeu hpos hn] at e
  have hlt : pos < n := not_dec_false e
  refine WP.aluImm sen_at_c ?_; wn
  refine WP.alu sen_at_e ?_; wn
  refine WP.aluImm sen_at_10 ?_; wn
  refine WP.alu sen_at_14 ?_; wn
  refine WP.aluImm sen_at_16 ?_; wn
  have hle : ¬(memBytes M p n).length ≤ pos := by omega
  simp only [stringEnd, hle, ↓reduceIte]
  rw [jmemBytes_drop]
  refine sen_loop hret hal hsep (R := n - (pos + 1)) (by omega) (n - (pos + 1)) 0 _ _ (by omega)
    (by rsimp) (by rsimp; rw [h1, h3, ev_add, ev_add, cl_succ]) (by rsimp; exact h0) (by rsimp; exact hra)
    (by rsimp; rw [h3, ev_add, cl_succ]) (by rsimp; exact h3) (by rsimp; exact h4) ?_ (by rsimp) (by keep hz)
  rsimp
  rw [h3, h2, not_add_ofNat hlt hn, Nat.sub_sub]

/-- `string_end(doc, pos, mode)` with `doc` the `n` bytes at `p`, `pos` in
`a3`, and `mode` in `a4`: stores `stringEnd` of them at `out` as a
`Result<usize, TufError>`, changes no other memory, and keeps every
register outside `seClob`. -/
theorem jsonStringEnd_correct (m : Machine) {base retAddr out p : Word} {n pos : Nat} {c : Bool}
    (hb : base.toNat % 2 = 0) (hc : CodeIn m.mem base jsonStringEndCode) (hpc : m.pc = base)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = p) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (ha3 : reg m a3 = BitVec.ofNat 32 pos) (ha4 : reg m a4 = modeW c) (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32)
    (hal : out.toNat % 4 = 0) (hsep : Sep out 8 base jsonStringEndCode.length)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      UsizeRes m.mem m'.mem out (stringEnd c (memBytes m.mem p n) pos) ∧
      ∀ r, r ∉ seClob → reg m' r = reg m r :=
  WP.run (sen_wp hn hpos ha0 ha1 ha2 ha3 ha4 hra hret hal hsep) hb hc hpc

end

end C3.RV32
