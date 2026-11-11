import C3BootProofs.Proofs.ShaSpec
import C3BootProofs.Proofs.FieldMont
import C3BootProofs.Image.BootloaderV0

/-!
# Tools for the compiled SHA-256 compression function

`compress256` is 11 KB of mostly straight-line code. Its proof decodes it
in windows, short pieces of the function's bytes (`CodeIn.window`), so that
each `fetchRel` lemma decodes a short list; runs the machine-outlined helper
it calls in the middle of its rounds as one step (`sha_o97_rot`); and folds
each rotation, shift, complement, and round constant into an irreducible
name as soon as its instruction runs, so that each round's identity closes
by associativity and commutativity alone.
-/

namespace C3.RV32

open C3.ImageV0

theorem getD_take_lt : ∀ (code : List Nat) (l i : Nat), i < l → (code.take l).getD i 0 = code.getD i 0
  | [], l, _, _ => by cases l <;> rfl
  | _ :: _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: as, l + 1, i + 1, h => getD_take_lt as l i (by omega)

theorem getD_drop : ∀ (code : List Nat) (s i : Nat), (code.drop s).getD i 0 = code.getD (s + i) 0
  | [], _, _ => by simp only [List.drop_nil]; rfl
  | _ :: _, 0, _ => by rw [Nat.zero_add]; rfl
  | _ :: as, s + 1, i => by
    rw [show s + 1 + i = (s + i) + 1 by omega]
    exact getD_drop as s i

/-- Memory that holds `code` holds each window of it. -/
theorem CodeIn.window {M : Word → BitVec 8} {P : Word} {code w : List Nat} {s : Nat} (hc : CodeIn M P code)
    (hw : w = (code.drop s).take w.length) (hl : s + w.length ≤ code.length) :
    CodeIn M (P + BitVec.ofNat 32 s) w := fun i hi => by
  rw [add_ofNat_assoc, hc (s + i) (by omega)]
  unfold byteAt
  rw [hw, getD_take_lt _ _ _ hi, getD_drop]

theorem St.rebase {M : Word → BitVec 8} {base : Word} {m : Machine} {s k : Nat} {f : Fin 32 → Word}
    (h : St M base m (s + k) f) : St M (base + BitVec.ofNat 32 s) m k f :=
  ⟨by rw [h.pc, add_ofNat_assoc], h.mem, h.regs⟩

theorem St.unbase {M : Word → BitVec 8} {base : Word} {m : Machine} {s k : Nat} {f : Fin 32 → Word}
    (h : St M (base + BitVec.ofNat 32 s) m k f) : St M base m (s + k) f :=
  ⟨by rw [h.pc, add_ofNat_assoc], h.mem, h.regs⟩

theorem St.rebase0 {M : Word → BitVec 8} {base : Word} {m : Machine} {s : Nat} {f : Fin 32 → Word}
    (h : St M base m s f) : St M (base + BitVec.ofNat 32 s) m 0 f := St.rebase (k := 0) h

theorem St.shift {M : Word → BitVec 8} {base : Word} {m : Machine} {s k s' : Nat} {f : Fin 32 → Word}
    (h : St M (base + BitVec.ofNat 32 s) m k f) (e : s + k = s') : St M (base + BitVec.ofNat 32 s') m 0 f := by
  subst e; exact St.rebase0 h.unbase

/-- An `auipc rd; jalr rd, off(rd)` call, the form the machine outliner uses
with `t0`. -/
theorem St.callReg {M : Word → BitVec 8} {base cb : Word} {code : List Nat} {m : Machine} {off : Nat}
    {f : Fin 32 → Word} (s : St M base m off f) (hc : CodeIn M base code) {rd : Fin 32} {imm o : Word}
    (hrd : rd.val ≠ 0)
    (h1 : fetchRel code off = some (.auipc rd imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr rd rd o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = cb) (hbe : cb.toNat % 2 = 0) :
    ∃ m1, Steps m m1 ∧ m1.pc = cb ∧ m1.mem = M ∧
      ∀ r, reg m1 r = upd f rd (base + BitVec.ofNat 32 (off + 8)) r := by
  obtain ⟨m1, e1, t1⟩ := s.auipc hc h1 (off' := off + 4) (ofNat_add_ofNat off 4)
  obtain ⟨m2, e2, pc2, mem2, regs2⟩ := t1.call hc h2
  have hL : base + BitVec.ofNat 32 (off + 4) + 4 = base + BitVec.ofNat 32 (off + 8) := by
    rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  refine ⟨m2, .cons e1 (.single e2), ?_, mem2, fun r => ?_⟩
  · rw [pc2, upd_same hrd, hb]; exact even_clear _ hbe
  · rw [regs2, hL]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]
    by_cases e : r = rd
    · subst e; rw [upd_same hrd, upd_same hrd]
    · rw [upd_ne h0 e, upd_ne h0 e, upd_ne h0 e]

/-! ## Irreducible wrappers for AC-closed round equations -/

def notMask : Word := 0xFFFFFFFF
def shr3 (x : Word) : Word := x >>> 3
def shr10 (x : Word) : Word := x >>> 10
def ktAt (t : Nat) : Word := Sha256.k[t]!
def rotrW (x : Word) (n : Nat) : Word := Sha256.rotr x n
def vsW (w : Nat → Word) (hv : Sha256.V8) (n : Nat) : Sha256.V8 := Sha256.vs w hv n

theorem xor_notMask (x : Word) : aluEval .xor x 0xFFFFFFFF = x ^^^ notMask := rfl
theorem shr3_eval (x : Word) : aluEval .srl x 0x3 = shr3 x := rfl
theorem shr10_eval (x : Word) : aluEval .srl x 0xA = shr10 x := rfl
theorem ktAt_def (t : Nat) : ktAt t = Sha256.k[t]! := rfl
theorem ch_mask (e f g : Word) : Sha256.ch e f g = (e &&& f) + (g &&& (e ^^^ notMask)) := Sha256.ch_add e f g
theorem vsW_def (w : Nat → Word) (hv : Sha256.V8) (n : Nat) : vsW w hv n = Sha256.vs w hv n := rfl
theorem bigSigma0_w (x : Word) : Sha256.bigSigma0 x = rotrW x 2 ^^^ rotrW x 13 ^^^ rotrW x 22 := rfl
theorem bigSigma1_w (x : Word) : Sha256.bigSigma1 x = rotrW x 6 ^^^ rotrW x 11 ^^^ rotrW x 25 := rfl
theorem s0_fold (x : Word) : Sha256.smallSigma0 x = rotrW x 7 ^^^ rotrW x 18 ^^^ shr3 x := rfl
theorem s1_fold (x : Word) : Sha256.smallSigma1 x = rotrW x 17 ^^^ rotrW x 19 ^^^ shr10 x := rfl

theorem rotr_or_lr (x : Word) (r l : Nat) (hrl : (r + l == 32 && decide (0 < r) && decide (r < 32)) = true) :
    (x >>> r) ||| (x <<< l) = rotrW x r := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrl
  obtain ⟨⟨hsum, _⟩, hlt⟩ := hrl
  unfold rotrW Sha256.rotr
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hlt, show 32 - r = l by omega]

theorem rotr_or_rl (x : Word) (r l : Nat) (hrl : (r + l == 32 && decide (0 < r) && decide (r < 32)) = true) :
    (x <<< l) ||| (x >>> r) = rotrW x r := by
  rw [BitVec.or_comm]; exact rotr_or_lr x r l hrl

theorem vs_a_0 (w : Nat → Word) (hv : Sha256.V8) :
    (vsW w hv 1).a =
      (hv.h + Sha256.bigSigma1 hv.e + Sha256.ch hv.e hv.f hv.g + ktAt 0 + w 0) +
        (Sha256.bigSigma0 hv.a + Sha256.maj hv.a hv.b hv.c) := rfl

theorem vs_a_1 (w : Nat → Word) (hv : Sha256.V8) :
    (vsW w hv 2).a =
      (hv.g + Sha256.bigSigma1 (vsW w hv 1).e + Sha256.ch (vsW w hv 1).e hv.e hv.f + ktAt 1 + w 1) +
        (Sha256.bigSigma0 (vsW w hv 1).a + Sha256.maj (vsW w hv 1).a hv.a hv.b) := rfl

theorem vs_a_2 (w : Nat → Word) (hv : Sha256.V8) :
    (vsW w hv 3).a =
      (hv.f + Sha256.bigSigma1 (vsW w hv 2).e +
          Sha256.ch (vsW w hv 2).e (vsW w hv 1).e hv.e + ktAt 2 + w 2) +
        (Sha256.bigSigma0 (vsW w hv 2).a +
          Sha256.maj (vsW w hv 2).a (vsW w hv 1).a hv.a) := rfl

theorem vs_a_3 (w : Nat → Word) (hv : Sha256.V8) :
    (vsW w hv 4).a =
      (hv.e + Sha256.bigSigma1 (vsW w hv 3).e +
          Sha256.ch (vsW w hv 3).e (vsW w hv 2).e (vsW w hv 1).e + ktAt 3 + w 3) +
        (Sha256.bigSigma0 (vsW w hv 3).a +
          Sha256.maj (vsW w hv 3).a (vsW w hv 2).a (vsW w hv 1).a) := rfl

theorem vs_a_ge4 (w : Nat → Word) (hv : Sha256.V8) (s r4 r3 r2 r1 : Nat)
    (h : (s == r4 + 1 && r4 == r3 + 1 && r3 == r2 + 1 && r2 == r1 + 1 && decide (1 ≤ r1)) = true) :
    (vsW w hv s).a =
      ((vsW w hv r1).e + Sha256.bigSigma1 (vsW w hv r4).e +
          Sha256.ch (vsW w hv r4).e (vsW w hv r3).e (vsW w hv r2).e +
          ktAt r4 + w r4) +
        (Sha256.bigSigma0 (vsW w hv r4).a +
          Sha256.maj (vsW w hv r4).a (vsW w hv r3).a (vsW w hv r2).a) := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hr1⟩ := h
  cases r1 with
  | zero => omega
  | succ n => rfl

theorem vs_e_0 (w : Nat → Word) (hv : Sha256.V8) :
    (vsW w hv 1).e = hv.d + (hv.h + Sha256.bigSigma1 hv.e + Sha256.ch hv.e hv.f hv.g + ktAt 0 + w 0) := rfl

theorem vs_e_1 (w : Nat → Word) (hv : Sha256.V8) :
    (vsW w hv 2).e =
      hv.c + (hv.g + Sha256.bigSigma1 (vsW w hv 1).e +
        Sha256.ch (vsW w hv 1).e hv.e hv.f + ktAt 1 + w 1) := rfl

theorem vs_e_2 (w : Nat → Word) (hv : Sha256.V8) :
    (vsW w hv 3).e =
      hv.b + (hv.f + Sha256.bigSigma1 (vsW w hv 2).e +
        Sha256.ch (vsW w hv 2).e (vsW w hv 1).e hv.e + ktAt 2 + w 2) := rfl

theorem vs_e_3 (w : Nat → Word) (hv : Sha256.V8) :
    (vsW w hv 4).e =
      hv.a + (hv.e + Sha256.bigSigma1 (vsW w hv 3).e +
        Sha256.ch (vsW w hv 3).e (vsW w hv 2).e (vsW w hv 1).e + ktAt 3 + w 3) := rfl

theorem vs_e_ge4 (w : Nat → Word) (hv : Sha256.V8) (s r4 r3 r2 r1 : Nat)
    (h : (s == r4 + 1 && r4 == r3 + 1 && r3 == r2 + 1 && r2 == r1 + 1 && decide (1 ≤ r1)) = true) :
    (vsW w hv s).e =
      (vsW w hv r1).a + ((vsW w hv r1).e + Sha256.bigSigma1 (vsW w hv r4).e +
        Sha256.ch (vsW w hv r4).e (vsW w hv r3).e (vsW w hv r2).e +
        ktAt r4 + w r4) := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hr1⟩ := h
  cases r1 with
  | zero => omega
  | succ n => rfl

theorem vs64_b (w : Nat → Word) (hv : Sha256.V8) : (vsW w hv 64).b = (vsW w hv 63).a := rfl
theorem vs64_c (w : Nat → Word) (hv : Sha256.V8) : (vsW w hv 64).c = (vsW w hv 62).a := rfl
theorem vs64_d (w : Nat → Word) (hv : Sha256.V8) : (vsW w hv 64).d = (vsW w hv 61).a := rfl
theorem vs64_f (w : Nat → Word) (hv : Sha256.V8) : (vsW w hv 64).f = (vsW w hv 63).e := rfl
theorem vs64_g (w : Nat → Word) (hv : Sha256.V8) : (vsW w hv 64).g = (vsW w hv 62).e := rfl
theorem vs64_h (w : Nat → Word) (hv : Sha256.V8) : (vsW w hv 64).h = (vsW w hv 61).e := rfl

theorem vs64_toList (w : Nat → Word) (hv : Sha256.V8) :
    (vsW w hv 64).toList =
      [(vsW w hv 64).a, (vsW w hv 64).b, (vsW w hv 64).c, (vsW w hv 64).d,
       (vsW w hv 64).e, (vsW w hv 64).f, (vsW w hv 64).g, (vsW w hv 64).h] := rfl

attribute [irreducible] notMask shr3 shr10 ktAt rotrW vsW

/-! ## `OUTLINED_FUNCTION_97` -/

theorem o97_at_0 : fetchRel shaSigma1PartCode 0x0 = some (.alu .or a0 a0 a1, 2) := by decide
theorem o97_at_2 : fetchRel shaSigma1PartCode 0x2 = some (.alu .or a2 a2 a3, 2) := by decide
theorem o97_at_4 : fetchRel shaSigma1PartCode 0x4 = some (.aluImm .srl a1 (28 : Fin 32) 0x11, 4) := by decide
theorem o97_at_8 : fetchRel shaSigma1PartCode 0x8 = some (.aluImm .sll a3 (28 : Fin 32) 0xF, 4) := by decide
theorem o97_at_c : fetchRel shaSigma1PartCode 0xC = some (.alu .xor a0 a0 a2, 2) := by decide
theorem o97_at_e : fetchRel shaSigma1PartCode 0xE = some (.alu .or a1 a1 a3, 2) := by decide
theorem o97_at_10 : fetchRel shaSigma1PartCode 0x10 = some (.aluImm .srl a2 (28 : Fin 32) 0x13, 4) := by decide
theorem o97_at_14 : fetchRel shaSigma1PartCode 0x14 = some (.aluImm .sll a3 (28 : Fin 32) 0xD, 4) := by decide
theorem o97_at_18 : fetchRel shaSigma1PartCode 0x18 = some (.jalr x0 (5 : Fin 32) 0x0, 2) := by decide

set_option maxHeartbeats 1000000 in
/-- A call from the compression function to `OUTLINED_FUNCTION_97`, the
machine outliner's piece of `σ₁`: it combines two rotations' halves in `a0`
and starts the next two from `t3`, and returns through `t0`. -/
theorem sha_o97 {M : Word → BitVec 8} {Pw P97 : Word} {code : List Nat} {n : Machine} {k : Nat}
    {imm o : Word} (s : St M Pw n k (reg n)) (hc : CodeIn M Pw code) (h97 : CodeIn M P97 shaSigma1PartCode)
    (h1 : fetchRel code k = some (.auipc (5 : Fin 32) imm, 4))
    (h2 : fetchRel code (k + 4) = some (.jalr (5 : Fin 32) (5 : Fin 32) o, 4))
    (hb : Pw + BitVec.ofNat 32 k + imm + o = P97) (hP97 : P97.toNat % 2 = 0)
    (hret : (Pw + BitVec.ofNat 32 (k + 8)).toNat % 2 = 0) :
    ∃ n', Steps n n' ∧ St M Pw n' (k + 8) (reg n') ∧
      reg n' a0 = (reg n a0 ||| reg n a1) ^^^ (reg n a2 ||| reg n a3) ∧
      reg n' a1 = reg n (28 : Fin 32) >>> 17 ||| reg n (28 : Fin 32) <<< 15 ∧
      reg n' a2 = reg n (28 : Fin 32) >>> 19 ∧ reg n' a3 = reg n (28 : Fin 32) <<< 13 ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ (5 : Fin 32) → reg n' q = reg n q := by
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callReg hc (by decide) h1 h2 hb hP97
  have s1 : St M P97 m1 0 (reg m1) := ⟨by rw [pc1]; simp, mem1, fun _ => rfl⟩
  obtain ⟨m2, d2, u2⟩ := s1.alu h97 o97_at_0 (off' := 2) (by decide)
  obtain ⟨m3, d3, u3⟩ := u2.alu h97 o97_at_2 (off' := 4) (by decide)
  obtain ⟨m4, d4, u4⟩ := u3.aluImm h97 o97_at_4 (off' := 8) (by decide)
  obtain ⟨m5, d5, u5⟩ := u4.aluImm h97 o97_at_8 (off' := 0xC) (by decide)
  obtain ⟨m6, d6, u6⟩ := u5.alu h97 o97_at_c (off' := 0xE) (by decide)
  obtain ⟨m7, d7, u7⟩ := u6.alu h97 o97_at_e (off' := 0x10) (by decide)
  obtain ⟨m8, d8, u8⟩ := u7.aluImm h97 o97_at_10 (off' := 0x14) (by decide)
  obtain ⟨m9, d9, u9⟩ := u8.aluImm h97 o97_at_14 (off' := 0x18) (by decide)
  obtain ⟨m10, d10, pc10, mem10, regs10⟩ := u9.jalr h97 o97_at_18
  have r1 : ∀ q, q ≠ (5 : Fin 32) → reg m1 q = reg n q := fun q h => by
    rw [regs1]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact s.zero.symm
    · exact upd_ne h0 h
  have t0v : reg m1 (5 : Fin 32) = Pw + BitVec.ofNat 32 (k + 8) := by rw [regs1, upd_same (by decide)]
  have z1 : reg m1 0 = 0 := s1.zero
  refine ⟨m10, c1.trans (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
    (.single d10))))))))), ⟨?_, by rw [mem10], fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc10]; simp +decide only [upd, ↓reduceIte, t0v]; rw [add_lit_zero]; exact even_clear _ hret
  · rw [regs10]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [r1 a0 (by decide), r1 a1 (by decide), r1 a2 (by decide), r1 a3 (by decide)]
  · rw [regs10]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [r1 (28 : Fin 32) (by decide)]; rfl
  · rw [regs10]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [r1 (28 : Fin 32) (by decide)]; rfl
  · rw [regs10]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [r1 (28 : Fin 32) (by decide)]; rfl
  · intro q q0 q1 q2 q3 q5
    rw [regs10]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact z1
    simp only [upd, h0, q0, q1, q2, q3, ite_false]
    exact r1 q q5

/-- `sha_o97` with its rotations folded into `Sha256.rotr`. -/
theorem sha_o97_rot {M : Word → BitVec 8} {P : Word} {s k : Nat} {code : List Nat} {n : Machine}
    {imm o x y : Word} (st : St M (P + BitVec.ofNat 32 s) n k (reg n))
    (hc : CodeIn M (P + BitVec.ofNat 32 s) code) (h97 : CodeIn M (P + 0xC09C) shaSigma1PartCode)
    (h1 : fetchRel code k = some (.auipc (5 : Fin 32) imm, 4))
    (h2 : fetchRel code (k + 4) = some (.jalr (5 : Fin 32) (5 : Fin 32) o, 4))
    (hb : (BitVec.ofNat 32 s + BitVec.ofNat 32 k + imm + o == 0xC09C) = true)
    (hP : P.toNat % 2 = 0) (hsk : ((s + (k + 8)) % 2 == 0) = true)
    (ha0 : reg n a0 = x >>> 7) (ha1 : reg n a1 = x <<< 25)
    (ha2 : reg n a2 = x >>> 18) (ha3 : reg n a3 = x <<< 14) (ht3 : reg n (28 : Fin 32) = y) :
    ∃ n' v, Steps n n' ∧ (rotrW x 7 ^^^ rotrW x 18) = v ∧
      St M (P + BitVec.ofNat 32 s) n' (k + 8) (reg n') ∧
      reg n' a0 = v ∧ reg n' a1 = rotrW y 17 ∧ reg n' a2 = y >>> 19 ∧ reg n' a3 = y <<< 13 ∧
      ∀ q, (q.val != 10 && q.val != 11 && q.val != 12 && q.val != 13 && q.val != 5) = true →
        reg n' q = reg n q := by
  have hb' : P + BitVec.ofNat 32 s + BitVec.ofNat 32 k + imm + o = P + 0xC09C := by
    have e := beq_iff_eq.mp hb
    calc P + BitVec.ofNat 32 s + BitVec.ofNat 32 k + imm + o
        = P + (BitVec.ofNat 32 s + BitVec.ofNat 32 k + imm + o) := by
          simp only [BitVec.add_assoc]
      _ = P + 0xC09C := by rw [e]
  have hret : (P + BitVec.ofNat 32 s + BitVec.ofNat 32 (k + 8)).toNat % 2 = 0 := by
    rw [add_ofNat_assoc]; exact even_at P hP _ (beq_iff_eq.mp hsk)
  obtain ⟨n', cs, u, r0, r1, r2, r3, kr⟩ := sha_o97 st hc h97 h1 h2 hb' (even_at P hP 0xC09C (by decide)) hret
  rw [ha0, ha1, ha2, ha3, rotr_or_lr x 7 25 rfl, rotr_or_lr x 18 14 rfl] at r0
  rw [ht3, rotr_or_lr y 17 15 rfl] at r1
  rw [ht3] at r2 r3
  refine ⟨n', _, cs, rfl, u, r0, r1, r2, r3, fun q hq => kr q ?_ ?_ ?_ ?_ ?_⟩
  all_goals (intro e; subst e; exact Bool.noConfusion hq)

/-! ## Environment and `rfl`-checked step combinators -/

/-- The schedule recurrence, section 6.2.2 step 1, for a schedule given as a
function. -/
def ShaSched (w : Nat → Word) : Prop :=
  ∀ t, 16 ≤ t → t < 64 →
    w t = Sha256.smallSigma1 (w (t - 2)) + w (t - 7) + Sha256.smallSigma0 (w (t - 15)) + w (t - 16)

/-- Where the compression function's rounds run: its code at `P` and the
outlined helper where the image puts it, the round constants at
`shaKAddress`, the frame at `F` with the state pointer `stp` at `F + 0xC`,
and the 0x58 bytes of the frame that the rounds store to apart from the
code, the constants, and the state. -/
structure ShaEnv (M0 : Word → BitVec 8) (P F stp : Word) : Prop where
  code : CodeIn M0 P sha256CompressCode
  o97 : CodeIn M0 (P + 0xC09C) shaSigma1PartCode
  hP : P.toNat % 2 = 0
  hF : F.toNat % 4 = 0
  hstp : stp.toNat % 4 = 0
  hK : ∀ t, t < 64 → memLoad32 M0 (BitVec.ofNat 32 shaKAddress + BitVec.ofNat 32 (4 * t)) = ktAt t
  stpSlot : memLoad32 M0 (F + BitVec.ofNat 32 0xC) = stp
  sC : Sep (F + BitVec.ofNat 32 0x14) 0x58 P sha256CompressCode.length
  s97 : Sep (F + BitVec.ofNat 32 0x14) 0x58 (P + 0xC09C) shaSigma1PartCode.length
  sK : Sep (F + BitVec.ofNat 32 0x14) 0x58 (BitVec.ofNat 32 shaKAddress) 256
  stC : Sep stp 32 P sha256CompressCode.length
  stR : Sep stp 32 (F + BitVec.ofNat 32 0x14) 0x58

section
variable {M0 : Word → BitVec 8} {P F stp : Word}

theorem ShaEnv.win (env : ShaEnv M0 P F stp) {M' : Word → BitVec 8}
    (h : ∀ x, Sep (F + BitVec.ofNat 32 0x14) 0x58 x 1 → M' x = M0 x) {w : List Nat} {s : Nat}
    (hw : w = (sha256CompressCode.drop s).take w.length) (hl : s + w.length ≤ sha256CompressCode.length) :
    CodeIn M' (P + BitVec.ofNat 32 s) w :=
  CodeIn.window (fun i hi => by rw [h _ (env.sC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi) hw hl

theorem ShaEnv.win2 (env : ShaEnv M0 P F stp) {M' : Word → BitVec 8}
    (h : ∀ x, Sep (F + BitVec.ofNat 32 0x14) 0x58 x 1 → Sep stp 32 x 1 → M' x = M0 x) {w : List Nat} {s : Nat}
    (hw : w = (sha256CompressCode.drop s).take w.length) (hl : s + w.length ≤ sha256CompressCode.length) :
    CodeIn M' (P + BitVec.ofNat 32 s) w :=
  CodeIn.window (fun i hi => by
    rw [h _ (env.sC.subR (c := i) (l := 1) (by omega)) (env.stC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi) hw hl

theorem ShaEnv.out97 (env : ShaEnv M0 P F stp) {M' : Word → BitVec 8}
    (h : ∀ x, Sep (F + BitVec.ofNat 32 0x14) 0x58 x 1 → M' x = M0 x) :
    CodeIn M' (P + 0xC09C) shaSigma1PartCode := fun i hi => by
  rw [h _ (env.s97.subR (c := i) (l := 1) (by omega))]; exact env.o97 i hi

theorem reg_step_ne {M : Word → BitVec 8} {B : Word} {n : Machine} {off : Nat} {f : Fin 32 → Word}
    {rd q : Fin 32} {v w : Word} (u : St M B n off (upd f rd v))
    (hne : (q.val == 0 || q.val == rd.val) = false) (h : f q = w) : reg n q = w := by
  rw [u.regs]
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hne
  exact (upd_ne hne.1 (fun e => hne.2 (congrArg Fin.val e))).trans h

theorem reg_step_eq {M : Word → BitVec 8} {B : Word} {n : Machine} {off : Nat} {f : Fin 32 → Word}
    {rd : Fin 32} {v : Word} (u : St M B n off (upd f rd v)) (h0 : (rd.val == 0) = false) :
    reg n rd = v :=
  (u.regs rd).trans (upd_same (beq_eq_false_iff_ne.mp h0))

theorem reg_step_sw {M : Word → BitVec 8} {B : Word} {n : Machine} {off : Nat} {f : Fin 32 → Word}
    {q : Fin 32} {w : Word} (u : St M B n off f) (h : f q = w) : reg n q = w :=
  (u.regs q).trans h

theorem off_step {off off' : Nat} {len : Word} (h : (off + len.toNat == off') = true) :
    BitVec.ofNat 32 off + len = BitVec.ofNat 32 off' := by
  rw [← beq_iff_eq.mp h, ← ofNat_add_ofNat, ofNat_toNat_self]

theorem sha_alu {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' : Nat}
    {op : AluOp} {rd rs1 rs2 : Fin 32} {a b len : Word}
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.alu op rd rs1 rs2, len)) (hn : (off + len.toNat == off') = true)
    (h1 : reg m rs1 = a) (h2 : reg m rs2 = b) :
    ∃ m1 v, step m = some m1 ∧ aluEval op a b = v ∧ St M B m1 off' (upd (reg m) rd v) := by
  obtain ⟨m1, v, d, hv, u⟩ := s.aluG hc hf (off_step hn)
  rw [h1, h2] at hv
  exact ⟨m1, v, d, hv, u⟩

theorem sha_or_lr {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' r l : Nat}
    {rd rs1 rs2 : Fin 32} {x len : Word}
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.alu .or rd rs1 rs2, len)) (hn : (off + len.toNat == off') = true)
    (hrl : (r + l == 32 && decide (0 < r) && decide (r < 32)) = true)
    (h1 : reg m rs1 = x >>> r) (h2 : reg m rs2 = x <<< l) :
    ∃ m1, step m = some m1 ∧ St M B m1 off' (upd (reg m) rd (rotrW x r)) := by
  obtain ⟨m1, d, u⟩ := s.alu hc hf (off_step hn)
  have e : aluEval .or (reg m rs1) (reg m rs2) = rotrW x r := by
    show reg m rs1 ||| reg m rs2 = _; rw [h1, h2]; exact rotr_or_lr x r l hrl
  rw [e] at u; exact ⟨m1, d, u⟩

theorem sha_or_rl {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' r l : Nat}
    {rd rs1 rs2 : Fin 32} {x len : Word}
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.alu .or rd rs1 rs2, len)) (hn : (off + len.toNat == off') = true)
    (hrl : (r + l == 32 && decide (0 < r) && decide (r < 32)) = true)
    (h1 : reg m rs1 = x <<< l) (h2 : reg m rs2 = x >>> r) :
    ∃ m1, step m = some m1 ∧ St M B m1 off' (upd (reg m) rd (rotrW x r)) := by
  obtain ⟨m1, d, u⟩ := s.alu hc hf (off_step hn)
  have e : aluEval .or (reg m rs1) (reg m rs2) = rotrW x r := by
    show reg m rs1 ||| reg m rs2 = _; rw [h1, h2]; exact rotr_or_rl x r l hrl
  rw [e] at u; exact ⟨m1, d, u⟩

theorem sha_mv {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' : Nat}
    {rd rs : Fin 32} {a len : Word}
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.alu .add rd x0 rs, len)) (hn : (off + len.toNat == off') = true)
    (h : reg m rs = a) :
    ∃ m1, step m = some m1 ∧ St M B m1 off' (upd (reg m) rd a) := by
  obtain ⟨m1, d, u⟩ := s.alu hc hf (off_step hn)
  have e : aluEval .add (reg m x0) (reg m rs) = a := by
    show reg m 0 + reg m rs = a; rw [s.zero, h]; exact BitVec.zero_add a
  rw [e] at u; exact ⟨m1, d, u⟩

theorem sha_srl {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' k : Nat}
    {rd rs : Fin 32} {a imm len : Word}
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.aluImm .srl rd rs imm, len)) (hn : (off + len.toNat == off') = true)
    (hk : (imm.toNat % 32 == k) = true) (h : reg m rs = a) :
    ∃ m1, step m = some m1 ∧ St M B m1 off' (upd (reg m) rd (a >>> k)) := by
  obtain ⟨m1, d, u⟩ := s.aluImm hc hf (off_step hn)
  have e : aluEval .srl (reg m rs) imm = a >>> k := by
    show reg m rs >>> (imm.toNat % 32) = a >>> k; rw [h, beq_iff_eq.mp hk]
  rw [e] at u; exact ⟨m1, d, u⟩

theorem sha_shr3 {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' : Nat}
    {rd rs : Fin 32} {a len : Word}
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.aluImm .srl rd rs 0x3, len)) (hn : (off + len.toNat == off') = true)
    (h : reg m rs = a) :
    ∃ m1, step m = some m1 ∧ St M B m1 off' (upd (reg m) rd (shr3 a)) := by
  obtain ⟨m1, d, u⟩ := s.aluImm hc hf (off_step hn)
  rw [h, shr3_eval] at u; exact ⟨m1, d, u⟩

theorem sha_shr10 {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' : Nat}
    {rd rs : Fin 32} {a len : Word}
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.aluImm .srl rd rs 0xA, len)) (hn : (off + len.toNat == off') = true)
    (h : reg m rs = a) :
    ∃ m1, step m = some m1 ∧ St M B m1 off' (upd (reg m) rd (shr10 a)) := by
  obtain ⟨m1, d, u⟩ := s.aluImm hc hf (off_step hn)
  rw [h, shr10_eval] at u; exact ⟨m1, d, u⟩

theorem sha_sll {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' k : Nat}
    {rd rs : Fin 32} {a imm len : Word}
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.aluImm .sll rd rs imm, len)) (hn : (off + len.toNat == off') = true)
    (hk : (imm.toNat % 32 == k) = true) (h : reg m rs = a) :
    ∃ m1, step m = some m1 ∧ St M B m1 off' (upd (reg m) rd (a <<< k)) := by
  obtain ⟨m1, d, u⟩ := s.aluImm hc hf (off_step hn)
  have e : aluEval .sll (reg m rs) imm = a <<< k := by
    show reg m rs <<< (imm.toNat % 32) = a <<< k; rw [h, beq_iff_eq.mp hk]
  rw [e] at u; exact ⟨m1, d, u⟩

theorem sha_not {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' : Nat}
    {rd rs : Fin 32} {a len : Word}
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.aluImm .xor rd rs 0xFFFFFFFF, len)) (hn : (off + len.toNat == off') = true)
    (h : reg m rs = a) :
    ∃ m1 v, step m = some m1 ∧ (a ^^^ notMask) = v ∧ St M B m1 off' (upd (reg m) rd v) := by
  obtain ⟨m1, v, d, hv, u⟩ := s.aluImmG hc hf (off_step hn)
  rw [h, xor_notMask] at hv
  exact ⟨m1, v, d, hv, u⟩

theorem sha_li {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' : Nat}
    {rd : Fin 32} {imm len : Word}
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.aluImm .add rd x0 imm, len)) (hn : (off + len.toNat == off') = true) :
    ∃ m1, step m = some m1 ∧ St M B m1 off' (upd (reg m) rd imm) := by
  obtain ⟨m1, d, u⟩ := s.aluImm hc hf (off_step hn)
  have e : aluEval .add (reg m x0) imm = imm := by show reg m 0 + imm = imm; rw [s.zero]; exact BitVec.zero_add imm
  rw [e] at u; exact ⟨m1, d, u⟩

theorem sha_addi_c {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' : Nat}
    {rd rs : Fin 32} {a imm c len : Word}
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.aluImm .add rd rs imm, len)) (hn : (off + len.toNat == off') = true)
    (h : reg m rs = a) (hc' : a + imm = c) :
    ∃ m1, step m = some m1 ∧ St M B m1 off' (upd (reg m) rd c) := by
  obtain ⟨m1, d, u⟩ := s.aluImm hc hf (off_step hn)
  have e : aluEval .add (reg m rs) imm = c := by show reg m rs + imm = c; rw [h, hc']
  rw [e] at u; exact ⟨m1, d, u⟩

/-- A store to a frame slot the rounds use stays inside their region. -/
theorem sha_inR (o : Nat) (h1 : 0x14 ≤ o) (h2 : o + 4 ≤ 0x6C) (x : Word)
    (hx : Sep (F + BitVec.ofNat 32 0x14) 0x58 x 1) : Sep (F + BitVec.ofNat 32 o) 4 x 1 := by
  have := hx.sub (c := o - 0x14) (l := 4) (by omega)
  rwa [add_ofNat_assoc, show 0x14 + (o - 0x14) = o by omega] at this

/-- A frame word outside the rounds' region reads as before them. -/
theorem sha_outR {M : Word → BitVec 8} (fr : ∀ x, Sep (F + BitVec.ofNat 32 0x14) 0x58 x 1 → M x = M0 x)
    {o : Nat} (ho : 0x6C ≤ o ∨ o + 4 ≤ 0x14) (ho2 : o + 4 ≤ 2 ^ 32) :
    memLoad32 M (F + BitVec.ofNat 32 o) = memLoad32 M0 (F + BitVec.ofNat 32 o) :=
  memLoad32_congr fun j hj => fr _ (by
    rw [add_ofNat_assoc]
    exact sep_offsets F (by rcases ho with h | h
                            · exact .inl (by omega)
                            · exact .inr (by omega)) (by decide) (by omega))

theorem stR_slot (env : ShaEnv M0 P F stp) (c o : Nat) (h1 : c + 4 ≤ 32) (h2 : 0x14 ≤ o) (h3 : o + 4 ≤ 0x6C) :
    Sep (stp + BitVec.ofNat 32 c) 4 (F + BitVec.ofNat 32 o) 4 := by
  have := (env.stR.sub (c := c) (l := 4) h1).subR (c := o - 0x14) (l := 4) (by omega)
  rwa [add_ofNat_assoc, show 0x14 + (o - 0x14) = o by omega] at this

theorem sha_lw_slot {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' o : Nat}
    {rd rs : Fin 32} {v oW len : Word} (env : ShaEnv M0 P F stp)
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.load .lw rd rs oW, len)) (hn : (off + len.toNat == off') = true)
    (ho : (oW == BitVec.ofNat 32 o && o % 4 == 0) = true)
    (hrs : reg m rs = F) (hm : memLoad32 M (F + BitVec.ofNat 32 o) = v) :
    ∃ m1, step m = some m1 ∧ St M B m1 off' (upd (reg m) rd v) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at ho
  obtain ⟨rfl, ho4⟩ := ho
  obtain ⟨m1, d, u⟩ := s.lw hc hf (off_step hn) (by rw [hrs]; exact aligned_add env.hF ho4)
  rw [hrs, hm] at u; exact ⟨m1, d, u⟩

theorem sha_lw_w {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' o i : Nat}
    {rd rs : Fin 32} {w : Nat → Word} {oW len : Word} (env : ShaEnv M0 P F stp)
    (fr : ∀ x, Sep (F + BitVec.ofNat 32 0x14) 0x58 x 1 → M x = M0 x)
    (hWin : ∀ i, i < 16 → memLoad32 M0 (F + BitVec.ofNat 32 (0x6C + 4 * i)) = w i)
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.load .lw rd rs oW, len)) (hn : (off + len.toNat == off') = true)
    (ho : (oW == BitVec.ofNat 32 o && o == 0x6C + 4 * i && decide (i < 16)) = true)
    (hrs : reg m rs = F) :
    ∃ m1, step m = some m1 ∧ St M B m1 off' (upd (reg m) rd (w i)) := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
  obtain ⟨⟨rfl, rfl⟩, hi⟩ := ho
  refine sha_lw_slot env s hc hf hn ?_ hrs
    ((sha_outR fr (.inl (by omega)) (by omega)).trans (hWin i hi))
  simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨trivial, by omega⟩

theorem sha_lw_stp {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' : Nat}
    {rd rs : Fin 32} {len : Word} (env : ShaEnv M0 P F stp)
    (fr : ∀ x, Sep (F + BitVec.ofNat 32 0x14) 0x58 x 1 → M x = M0 x)
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.load .lw rd rs 0xC, len)) (hn : (off + len.toNat == off') = true)
    (hrs : reg m rs = F) :
    ∃ m1, step m = some m1 ∧ St M B m1 off' (upd (reg m) rd stp) :=
  sha_lw_slot (o := 0xC) env s hc hf hn rfl hrs ((sha_outR fr (.inr (by decide)) (by decide)).trans env.stpSlot)

theorem sha_lw_k {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' t : Nat}
    {rd rs : Fin 32} {oW len : Word} (env : ShaEnv M0 P F stp)
    (fr : ∀ x, Sep (F + BitVec.ofNat 32 0x14) 0x58 x 1 → M x = M0 x)
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.load .lw rd rs oW, len)) (hn : (off + len.toNat == off') = true)
    (ho : (oW == BitVec.ofNat 32 (4 * t) && decide (t < 64)) = true)
    (hrs : reg m rs = BitVec.ofNat 32 shaKAddress) :
    ∃ m1, step m = some m1 ∧ St M B m1 off' (upd (reg m) rd (ktAt t)) := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
  obtain ⟨rfl, ht⟩ := ho
  have hal : (BitVec.ofNat 32 shaKAddress + BitVec.ofNat 32 (4 * t)).toNat % 4 = 0 :=
    aligned_add (by decide) (by omega)
  obtain ⟨m1, d, u⟩ := s.lw hc hf (off_step hn) (by rw [hrs]; exact hal)
  have hm : memLoad32 M (BitVec.ofNat 32 shaKAddress + BitVec.ofNat 32 (4 * t)) = ktAt t := by
    rw [← env.hK t ht]
    exact memLoad32_congr fun j hj => fr _ (by rw [add_ofNat_assoc]; exact env.sK.subR (c := 4 * t + j) (l := 1) (by omega))
  rw [hrs, hm] at u; exact ⟨m1, d, u⟩

theorem sha_sw_frame {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' o : Nat}
    {rb rs : Fin 32} {v oW len : Word} (env : ShaEnv M0 P F stp)
    (fr : ∀ x, Sep (F + BitVec.ofNat 32 0x14) 0x58 x 1 → M x = M0 x)
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.store .sw rb rs oW, len)) (hn : (off + len.toNat == off') = true)
    (ho : (oW == BitVec.ofNat 32 o && o % 4 == 0 && decide (0x14 ≤ o) && decide (o + 4 ≤ 0x6C)) = true)
    (hrb : reg m rb = F) (hrs : reg m rs = v) :
    ∃ m1 M', step m = some m1 ∧ memStore32 M (F + BitVec.ofNat 32 o) v = M' ∧
      (∀ x, Sep (F + BitVec.ofNat 32 0x14) 0x58 x 1 → M' x = M0 x) ∧ St M' B m1 off' (reg m) := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
  obtain ⟨⟨⟨rfl, ho4⟩, h1⟩, h2⟩ := ho
  obtain ⟨m1, d, u⟩ := s.sw hc hf (off_step hn) (by rw [hrb]; exact aligned_add env.hF ho4)
  rw [hrb, hrs] at u
  exact ⟨m1, _, d, rfl, fun x hx => by rw [memStore32_get_sep (sha_inR o h1 h2 x hx), fr x hx], u⟩

theorem sha_sw_stp0 {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' o : Nat}
    {rb rs : Fin 32} {v oW len : Word} (env : ShaEnv M0 P F stp)
    (fr : ∀ x, Sep (F + BitVec.ofNat 32 0x14) 0x58 x 1 → M x = M0 x)
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.store .sw rb rs oW, len)) (hn : (off + len.toNat == off') = true)
    (ho : (oW == BitVec.ofNat 32 o && o % 4 == 0 && decide (o + 4 ≤ 32)) = true)
    (hrb : reg m rb = stp) (hrs : reg m rs = v) :
    ∃ m1 M', step m = some m1 ∧ memStore32 M (stp + BitVec.ofNat 32 o) v = M' ∧
      (∀ x, Sep (F + BitVec.ofNat 32 0x14) 0x58 x 1 → Sep stp 32 x 1 → M' x = M0 x) ∧
      St M' B m1 off' (reg m) := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
  obtain ⟨⟨rfl, ho4⟩, hle⟩ := ho
  obtain ⟨m1, d, u⟩ := s.sw hc hf (off_step hn) (by rw [hrb]; exact aligned_add env.hstp ho4)
  rw [hrb, hrs] at u
  exact ⟨m1, _, d, rfl, fun x hx hs => by rw [memStore32_get_sep (hs.sub (c := o) (l := 4) hle), fr x hx], u⟩

theorem sha_sw_stp {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' o : Nat}
    {rb rs : Fin 32} {v oW len : Word} (env : ShaEnv M0 P F stp)
    (fr : ∀ x, Sep (F + BitVec.ofNat 32 0x14) 0x58 x 1 → Sep stp 32 x 1 → M x = M0 x)
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.store .sw rb rs oW, len)) (hn : (off + len.toNat == off') = true)
    (ho : (oW == BitVec.ofNat 32 o && o % 4 == 0 && decide (o + 4 ≤ 32)) = true)
    (hrb : reg m rb = stp) (hrs : reg m rs = v) :
    ∃ m1 M', step m = some m1 ∧ memStore32 M (stp + BitVec.ofNat 32 o) v = M' ∧
      (∀ x, Sep (F + BitVec.ofNat 32 0x14) 0x58 x 1 → Sep stp 32 x 1 → M' x = M0 x) ∧
      St M' B m1 off' (reg m) := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
  obtain ⟨⟨rfl, ho4⟩, hle⟩ := ho
  obtain ⟨m1, d, u⟩ := s.sw hc hf (off_step hn) (by rw [hrb]; exact aligned_add env.hstp ho4)
  rw [hrb, hrs] at u
  exact ⟨m1, _, d, rfl, fun x hx hs => by rw [memStore32_get_sep (hs.sub (c := o) (l := 4) hle), fr x hx hs], u⟩

theorem load_store_eq {M1 M2 : Word → BitVec 8} {b v : Word} {c : Nat}
    (hM : memStore32 M1 (b + BitVec.ofNat 32 c) v = M2) :
    memLoad32 M2 (b + BitVec.ofNat 32 c) = v := by
  rw [← hM]; exact memLoad32_store32_same M1 _ v

theorem load_store_ne {M1 M2 : Word → BitVec 8} {b v w : Word} {c d : Nat}
    (hM : memStore32 M1 (b + BitVec.ofNat 32 c) v = M2)
    (hok : ((c == d) == false && (c % 4 == 0) && (d % 4 == 0) && decide (c + 4 ≤ 0x100) && decide (d + 4 ≤ 0x100)) = true)
    (h : memLoad32 M1 (b + BitVec.ofNat 32 d) = w) :
    memLoad32 M2 (b + BitVec.ofNat 32 d) = w := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hcd, hc4⟩, hd4⟩, hc2⟩, hd2⟩ := hok
  rw [← hM, memLoad32_store32_off hcd hc4 hd4 (by omega) (by omega), h]

theorem load_store_stp_slot {M1 M2 : Word → BitVec 8} {v w : Word} {c o : Nat} (env : ShaEnv M0 P F stp)
    (hM : memStore32 M1 (stp + BitVec.ofNat 32 c) v = M2)
    (hok : (decide (c + 4 ≤ 32) && decide (0x14 ≤ o) && decide (o + 4 ≤ 0x6C)) = true)
    (h : memLoad32 M1 (F + BitVec.ofNat 32 o) = w) :
    memLoad32 M2 (F + BitVec.ofNat 32 o) = w := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨h1, h2⟩, h3⟩ := hok
  rw [← hM, memLoad32_store32_sep (stR_slot env c o h1 h2 h3), h]

theorem sha_lui {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' : Nat}
    {rd : Fin 32} {imm len : Word}
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.lui rd imm, len)) (hn : (off + len.toNat == off') = true) :
    ∃ m1, step m = some m1 ∧ St M B m1 off' (upd (reg m) rd imm) :=
  s.lui hc hf (off_step hn)

theorem sched_step {w : Nat → Word} (hw : ShaSched w) (t t2 t7 t15 t16 : Nat)
    (ht : (decide (16 ≤ t) && decide (t < 64) && t - 2 == t2 && t - 7 == t7 && t - 15 == t15 && t - 16 == t16) = true) :
    w t = Sha256.smallSigma1 (w t2) + w t7 + Sha256.smallSigma0 (w t15) + w t16 := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := ht
  exact hw t h1 h2

theorem sha_add {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' : Nat}
    {rd rs1 rs2 : Fin 32} {a b len : Word}
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.alu .add rd rs1 rs2, len)) (hn : (off + len.toNat == off') = true)
    (h1 : reg m rs1 = a) (h2 : reg m rs2 = b) :
    ∃ m1 v, step m = some m1 ∧ a + b = v ∧ St M B m1 off' (upd (reg m) rd v) :=
  sha_alu s hc hf hn h1 h2

theorem sha_xor {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' : Nat}
    {rd rs1 rs2 : Fin 32} {a b len : Word}
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.alu .xor rd rs1 rs2, len)) (hn : (off + len.toNat == off') = true)
    (h1 : reg m rs1 = a) (h2 : reg m rs2 = b) :
    ∃ m1 v, step m = some m1 ∧ a ^^^ b = v ∧ St M B m1 off' (upd (reg m) rd v) :=
  sha_alu s hc hf hn h1 h2

theorem sha_and {M : Word → BitVec 8} {B : Word} {code : List Nat} {m : Machine} {off off' : Nat}
    {rd rs1 rs2 : Fin 32} {a b len : Word}
    (s : St M B m off (reg m)) (hc : CodeIn M B code)
    (hf : fetchRel code off = some (.alu .and rd rs1 rs2, len)) (hn : (off + len.toNat == off') = true)
    (h1 : reg m rs1 = a) (h2 : reg m rs2 = b) :
    ∃ m1 v, step m = some m1 ∧ a &&& b = v ∧ St M B m1 off' (upd (reg m) rd v) :=
  sha_alu s hc hf hn h1 h2

end

end C3.RV32
