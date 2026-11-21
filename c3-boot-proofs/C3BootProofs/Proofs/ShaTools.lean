import C3BootProofs.Proofs.ShaSpec
import C3BootProofs.Proofs.FieldMont

/-!
# Tools for the compiled SHA-256 code

Code windows (`CodeIn.window`), step rebasing, irreducible names for each
rotation, shift, complement, and round constant, the working variables round
by round, and how the compiled code reads a block: 64 bytes in memory
(`memBytes`), and their big-endian words (`be32_wordAt`).
-/

namespace C3.RV32

set_option maxRecDepth 20000

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

/-- The `n` bytes starting at `p` in `M`, as natural numbers below 256. -/
def memBytes (M : Word → BitVec 8) (p : Word) (n : Nat) : Bytes :=
  (List.range n).map fun i => (M (p + BitVec.ofNat 32 i)).toNat

/-- The `k` 64-byte blocks starting at `bp` in `M`. -/
def blockList (M : Word → BitVec 8) (bp : Word) (k : Nat) : List Bytes :=
  (List.range k).map fun j => memBytes M (bp + BitVec.ofNat 32 (64 * j)) 64

theorem memBytes_length (M : Word → BitVec 8) (p : Word) (n : Nat) : (memBytes M p n).length = n := by
  unfold memBytes; rw [List.length_map, List.length_range]

theorem memBytes_getD {M : Word → BitVec 8} {p : Word} {n i : Nat} (hi : i < n) :
    (memBytes M p n).getD i 0 = (M (p + BitVec.ofNat 32 i)).toNat := by
  unfold memBytes
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem memBytes_congr {M M' : Word → BitVec 8} {p : Word} {n : Nat}
    (h : ∀ i, i < n → M' (p + BitVec.ofNat 32 i) = M (p + BitVec.ofNat 32 i)) :
    memBytes M' p n = memBytes M p n := by
  unfold memBytes
  exact List.map_congr_left fun i hi => congrArg BitVec.toNat (h i (List.mem_range.mp hi))

theorem range_add_split (a b : Nat) :
    List.range (a + b) = List.range a ++ (List.range b).map (a + ·) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega, List.range_succ, ih, List.range_succ,
      List.map_append, List.map_cons, List.map_nil, List.append_assoc]

theorem memBytes_split (M : Word → BitVec 8) (p : Word) (a b : Nat) :
    memBytes M p (a + b) = memBytes M p a ++ memBytes M (p + BitVec.ofNat 32 a) b := by
  unfold memBytes
  rw [range_add_split, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => by simp only [Function.comp_apply, ← add_ofNat_assoc]

theorem blockList_succ (M : Word → BitVec 8) (bp : Word) (j : Nat) :
    blockList M bp (j + 1) = blockList M bp j ++ [memBytes M (bp + BitVec.ofNat 32 (64 * j)) 64] := by
  unfold blockList
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem blockList_cons (M : Word → BitVec 8) (bp : Word) (k : Nat) :
    blockList M bp (k + 1) = memBytes M bp 64 :: blockList M (bp + BitVec.ofNat 32 64) k := by
  unfold blockList
  have r1 : List.range (k + 1) = 0 :: (List.range k).map (1 + ·) := by
    rw [Nat.add_comm k 1, range_add_split 1 k]; rfl
  rw [r1, List.map_cons, List.map_map]
  simp only [Nat.mul_zero, add_ofNat_zero]
  congr 1
  exact List.map_congr_left fun j _ => by
    simp only [Function.comp_apply]
    rw [show 64 * (1 + j) = 64 + 64 * j by omega, ← add_ofNat_assoc]

/-- `Sha256.blocks` on `64 * k` bytes in memory produces `blockList M bp k`. -/
theorem blocks_memBytes (M : Word → BitVec 8) :
    ∀ (k fuel : Nat) (bp : Word), k ≤ fuel → Sha256.blocks fuel (memBytes M bp (64 * k)) = blockList M bp k
  | 0, fuel, bp, _ => by
    cases fuel <;> rfl
  | k + 1, 0, _, h => absurd h (by omega)
  | k + 1, fuel + 1, bp, h => by
    rw [show 64 * (k + 1) = 64 + 64 * k by omega, memBytes_split, blockList_cons]
    have hlen : (memBytes M bp 64).length = 64 := memBytes_length M bp 64
    have hne : (memBytes M bp 64 ++ memBytes M (bp + BitVec.ofNat 32 64) (64 * k)).isEmpty = false := by
      cases hc : memBytes M bp 64 with
      | nil => rw [hc] at hlen; cases hlen
      | cons _ _ => rfl
    unfold Sha256.blocks
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte, List.take_append_of_le_length (Nat.le_of_eq hlen.symm),
      List.take_of_length_le (Nat.le_of_eq hlen), List.drop_append_of_le_length (Nat.le_of_eq hlen.symm),
      List.drop_eq_nil_of_le (Nat.le_of_eq hlen), List.nil_append]
    rw [blocks_memBytes M k fuel _ (by omega)]

/-! ## Big-endian 32-bit word assembly -/

theorem zext_toNat (b : BitVec 8) : (b.zeroExtend 32).toNat = b.toNat := by revert b; decide +kernel
theorem zext_shl8_toNat (b : BitVec 8) : (b.zeroExtend 32 <<< 8).toNat = b.toNat * 2 ^ 8 := by revert b; decide +kernel
theorem zext_shl16_toNat (b : BitVec 8) : (b.zeroExtend 32 <<< 16).toNat = b.toNat * 2 ^ 16 := by revert b; decide +kernel
theorem zext_shl24_toNat (b : BitVec 8) : (b.zeroExtend 32 <<< 24).toNat = b.toNat * 2 ^ 24 := by revert b; decide +kernel

theorem zext_hi : ∀ (b : BitVec 8) (i : Fin 32), 8 ≤ i.val → (b.zeroExtend 32).getLsbD i.val = false := by decide +kernel
theorem shl8_lo : ∀ (b : BitVec 8) (i : Fin 32), i.val < 8 → (b.zeroExtend 32 <<< 8).getLsbD i.val = false := by decide +kernel
theorem shl8_hi : ∀ (b : BitVec 8) (i : Fin 32), 16 ≤ i.val → (b.zeroExtend 32 <<< 8).getLsbD i.val = false := by decide +kernel
theorem shl16_lo : ∀ (b : BitVec 8) (i : Fin 32), i.val < 16 → (b.zeroExtend 32 <<< 16).getLsbD i.val = false := by decide +kernel
theorem shl16_hi : ∀ (b : BitVec 8) (i : Fin 32), 24 ≤ i.val → (b.zeroExtend 32 <<< 16).getLsbD i.val = false := by decide +kernel
theorem shl24_lo : ∀ (b : BitVec 8) (i : Fin 32), i.val < 24 → (b.zeroExtend 32 <<< 24).getLsbD i.val = false := by decide +kernel

theorem or_disj_toNat {x y : Word} (h : ∀ i, i < 32 → (x.getLsbD i && y.getLsbD i) = false) :
    (x ||| y).toNat = x.toNat + y.toNat := by
  have hc := Sha256.carry_disj h 32 (by decide)
  rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at hc
  rw [← Sha256.add_disj h, BitVec.toNat_add, Nat.mod_eq_of_lt hc]

theorem be32_assemble (b0 b1 b2 b3 : BitVec 8) :
    ((b3.zeroExtend 32 ||| (b2.zeroExtend 32 <<< 8)) |||
      ((b0.zeroExtend 32 <<< 24) ||| (b1.zeroExtend 32 <<< 16))) =
    BitVec.ofNat 32 (b0.toNat * 2 ^ 24 + b1.toNat * 2 ^ 16 + b2.toNat * 2 ^ 8 + b3.toNat) := by
  have d1 : ∀ i, i < 32 → ((b3.zeroExtend 32).getLsbD i && (b2.zeroExtend 32 <<< 8).getLsbD i) = false :=
    fun i hi => by
      by_cases h8 : i < 8
      · rw [shl8_lo b2 ⟨i, hi⟩ h8, Bool.and_false]
      · rw [zext_hi b3 ⟨i, hi⟩ (by simp; omega), Bool.false_and]
  have d2 : ∀ i, i < 32 → ((b0.zeroExtend 32 <<< 24).getLsbD i && (b1.zeroExtend 32 <<< 16).getLsbD i) = false :=
    fun i hi => by
      by_cases h24 : i < 24
      · rw [shl24_lo b0 ⟨i, hi⟩ h24, Bool.false_and]
      · rw [shl16_hi b1 ⟨i, hi⟩ (by simp; omega), Bool.and_false]
  have d3 : ∀ i, i < 32 →
      ((b3.zeroExtend 32 ||| (b2.zeroExtend 32 <<< 8)).getLsbD i &&
        ((b0.zeroExtend 32 <<< 24) ||| (b1.zeroExtend 32 <<< 16)).getLsbD i) = false :=
    fun i hi => by
      rw [BitVec.getLsbD_or, BitVec.getLsbD_or]
      by_cases h16 : i < 16
      · rw [shl24_lo b0 ⟨i, hi⟩ (by simp; omega), shl16_lo b1 ⟨i, hi⟩ h16]; simp
      · rw [zext_hi b3 ⟨i, hi⟩ (by simp; omega), shl8_hi b2 ⟨i, hi⟩ (by simp; omega)]; simp
  apply BitVec.eq_of_toNat_eq
  rw [or_disj_toNat d3, or_disj_toNat d1, or_disj_toNat d2,
    zext_toNat, zext_shl8_toNat, zext_shl16_toNat, zext_shl24_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt; omega)]
  omega

theorem be32_wordAt (M : Word → BitVec 8) (cur : Word) {i : Nat} (hi : i < 16) :
    let p := cur + BitVec.ofNat 32 (4 * i)
    (((M (p + 3)).zeroExtend 32 ||| ((M (p + 2)).zeroExtend 32 <<< 8)) |||
      (((M (p + 0)).zeroExtend 32 <<< 24) ||| ((M (p + 1)).zeroExtend 32 <<< 16))) =
    (Sha256.schedule (memBytes M cur 64))[i]! := by
  intro p
  rw [be32_assemble, Sha256.sched_lt _ hi]
  unfold Sha256.wordAt
  have e0 : p + 0 = cur + BitVec.ofNat 32 (4 * i) := add_lit_zero p
  have e1 : p + 1 = cur + BitVec.ofNat 32 (4 * i + 1) := add_ofNat_assoc cur (4 * i) 1
  have e2 : p + 2 = cur + BitVec.ofNat 32 (4 * i + 2) := add_ofNat_assoc cur (4 * i) 2
  have e3 : p + 3 = cur + BitVec.ofNat 32 (4 * i + 3) := add_ofNat_assoc cur (4 * i) 3
  rw [e0, e1, e2, e3,
    memBytes_getD (n := 64) (i := 4 * i) (by omega),
    memBytes_getD (n := 64) (i := 4 * i + 1) (by omega),
    memBytes_getD (n := 64) (i := 4 * i + 2) (by omega),
    memBytes_getD (n := 64) (i := 4 * i + 3) (by omega)]

/-! ## Step combinators -/

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

end C3.RV32
