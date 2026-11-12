import C3BootProofs.Proofs.ShaTools
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

theorem load_store_stp_slot {M1 M2 : Word → BitVec 8} {v w : Word} {c o : Nat} (env : ShaEnv M0 P F stp)
    (hM : memStore32 M1 (stp + BitVec.ofNat 32 c) v = M2)
    (hok : (decide (c + 4 ≤ 32) && decide (0x14 ≤ o) && decide (o + 4 ≤ 0x6C)) = true)
    (h : memLoad32 M1 (F + BitVec.ofNat 32 o) = w) :
    memLoad32 M2 (F + BitVec.ofNat 32 o) = w := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨h1, h2⟩, h3⟩ := hok
  rw [← hM, memLoad32_store32_sep (stR_slot env c o h1 h2 h3), h]

end

end C3.RV32
