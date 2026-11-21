import C3BootProofs.Proofs.ByteCompare

/-!
# `time::digits::<2>`, as compiled

`c3_verify::time::digits::<2>` takes two bytes off the front of a slice and
reads them as an ASCII decimal number. It fails with `BadTime` (0x19) when
the slice is shorter than two bytes or a byte is not a digit; two digits
can't overflow, so its `Overflow` path never runs.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem td_at_0 : fetchRel timeDigits2Code 0x0 = some (.load .lw a4 a1 0x4, 2) := by decide
theorem td_at_2 : fetchRel timeDigits2Code 0x2 = some (.aluImm .add a6 x0 0x1, 2) := by decide
theorem td_at_4 : fetchRel timeDigits2Code 0x4 = some (.branch .bgeu a6 a4 0x52, 4) := by decide
theorem td_at_8 : fetchRel timeDigits2Code 0x8 = some (.aluImm .add a3 x0 0x0, 2) := by decide
theorem td_at_a : fetchRel timeDigits2Code 0xA = some (.load .lw a2 a1 0x0, 2) := by decide
theorem td_at_c : fetchRel timeDigits2Code 0xC = some (.aluImm .add (17 : Fin 32) a4 0xFFFFFFFE, 4) := by decide
theorem td_at_10 : fetchRel timeDigits2Code 0x10 = some (.aluImm .add a5 x0 0x2, 2) := by decide
theorem td_at_12 : fetchRel timeDigits2Code 0x12 = some (.aluImm .add a4 a2 0x2, 4) := by decide
theorem td_at_16 : fetchRel timeDigits2Code 0x16 = some (.store .sw a1 a4 0x0, 2) := by decide
theorem td_at_18 : fetchRel timeDigits2Code 0x18 = some (.store .sw a1 (17 : Fin 32) 0x4, 4) := by decide
theorem td_at_1c : fetchRel timeDigits2Code 0x1C = some (.aluImm .add (17 : Fin 32) x0 0xF6, 4) := by decide
theorem td_at_20 : fetchRel timeDigits2Code 0x20 = some (.aluImm .add (5 : Fin 32) x0 0xA, 2) := by decide
theorem td_at_22 : fetchRel timeDigits2Code 0x22 = some (.branch .beq a5 x0 0x40, 2) := by decide
theorem td_at_24 : fetchRel timeDigits2Code 0x24 = some (.load .lbu a1 a2 0x0, 4) := by decide
theorem td_at_28 : fetchRel timeDigits2Code 0x28 = some (.aluImm .add a4 a1 0xFFFFFFC6, 4) := by decide
theorem td_at_2c : fetchRel timeDigits2Code 0x2C = some (.aluImm .and a4 a4 0xFF, 4) := by decide
theorem td_at_30 : fetchRel timeDigits2Code 0x30 = some (.branch .bltu a4 (17 : Fin 32) 0x26, 4) := by decide
theorem td_at_34 : fetchRel timeDigits2Code 0x34 = some (.alu .mulhu a4 a3 (5 : Fin 32), 4) := by decide
theorem td_at_38 : fetchRel timeDigits2Code 0x38 = some (.branch .bne a4 x0 0x1A, 2) := by decide
theorem td_at_3a : fetchRel timeDigits2Code 0x3A = some (.alu .mul a4 a3 (5 : Fin 32), 4) := by decide
theorem td_at_3e : fetchRel timeDigits2Code 0x3E = some (.aluImm .add a1 a1 0xFFFFFFD0, 4) := by decide
theorem td_at_42 : fetchRel timeDigits2Code 0x42 = some (.aluImm .and a3 a1 0xFF, 4) := by decide
theorem td_at_46 : fetchRel timeDigits2Code 0x46 = some (.alu .add a3 a3 a4, 2) := by decide
theorem td_at_48 : fetchRel timeDigits2Code 0x48 = some (.alu .sltu a1 a3 a4, 4) := by decide
theorem td_at_4c : fetchRel timeDigits2Code 0x4C = some (.aluImm .add a2 a2 0x1, 2) := by decide
theorem td_at_4e : fetchRel timeDigits2Code 0x4E = some (.aluImm .add a5 a5 0xFFFFFFFF, 2) := by decide
theorem td_at_50 : fetchRel timeDigits2Code 0x50 = some (.branch .beq a1 x0 0xFFFFFFD2, 2) := by decide
theorem td_at_52 : fetchRel timeDigits2Code 0x52 = some (.aluImm .add a1 x0 0x6, 2) := by decide
theorem td_at_54 : fetchRel timeDigits2Code 0x54 = some (.jal x0 0x4, 2) := by decide
theorem td_at_56 : fetchRel timeDigits2Code 0x56 = some (.aluImm .add a1 x0 0x19, 2) := by decide
theorem td_at_58 : fetchRel timeDigits2Code 0x58 = some (.store .sb a0 a1 0x1, 4) := by decide
theorem td_at_5c : fetchRel timeDigits2Code 0x5C = some (.store .sb a0 a6 0x0, 4) := by decide
theorem td_at_60 : fetchRel timeDigits2Code 0x60 = some (.jalr x0 ra 0x0, 2) := by decide
theorem td_at_62 : fetchRel timeDigits2Code 0x62 = some (.aluImm .add a6 x0 0x0, 2) := by decide
theorem td_at_64 : fetchRel timeDigits2Code 0x64 = some (.store .sw a0 a3 0x4, 2) := by decide
theorem td_at_66 : fetchRel timeDigits2Code 0x66 = some (.jal x0 0xFFFFFFF6, 2) := by decide
end

/-- Whether `b` is an ASCII decimal digit. -/
def isDigit (b : BitVec 8) : Bool := decide (0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39)

/-- The value of the two ASCII digits `b0 b1`, if both are digits. -/
def digits2Of (b0 b1 : BitVec 8) : Option Nat :=
  if isDigit b0 = true ∧ isDigit b1 = true then some ((b0.toNat - 0x30) * 10 + (b1.toNat - 0x30)) else none

/-- What `digits::<2>` leaves in memory, with its `Result<u32, Error>` at
`out` and the slice `(p, n)` at `d`. -/
def digits2Mem (M : Word → BitVec 8) (out d p : Word) (n : Nat) : Word → BitVec 8 :=
  if n < 2 then memStore8 (memStore8 M (out + 1) 0x19) out 1
  else match digits2Of (M p) (M (p + 1)) with
    | some v => memStore8 (memStore32 (memStore32 (memStore32 M d (p + 2)) (d + 4) (BitVec.ofNat 32 n + 0xFFFFFFFE))
        (out + 4) (BitVec.ofNat 32 v)) out 0
    | none => memStore8 (memStore8 (memStore32 (memStore32 M d (p + 2)) (d + 4) (BitVec.ofNat 32 n + 0xFFFFFFFE))
        (out + 1) 0x19) out 1

theorem td_digit : ∀ b : BitVec 8,
    branchTaken .bltu (aluEval .and (aluEval .add (b.zeroExtend 32) 0xFFFFFFC6) 0xFF) 0xF6 = !isDigit b := by decide

theorem td_val : ∀ b : BitVec 8, isDigit b = true →
    aluEval .and (aluEval .add (b.zeroExtend 32) 0xFFFFFFD0) 0xFF = BitVec.ofNat 32 (b.toNat - 0x30) := by decide

theorem td_lt : ∀ b : BitVec 8, isDigit b = true → b.toNat - 0x30 < 10 := by decide

theorem td_step : ∀ d0 d1 : Fin 10,
    aluEval .mulhu (BitVec.ofNat 32 d0) 0xA = 0 ∧ aluEval .mul (BitVec.ofNat 32 d0) 0xA = BitVec.ofNat 32 (d0 * 10) ∧
    aluEval .sltu (aluEval .add (BitVec.ofNat 32 d1) (BitVec.ofNat 32 (d0 * 10))) (BitVec.ofNat 32 (d0 * 10)) = 0 ∧
    aluEval .add (BitVec.ofNat 32 d1) (BitVec.ofNat 32 (d0 * 10)) = BitVec.ofNat 32 (d0 * 10 + d1) := by decide


/-- The registers `digits::<2>` leaves alone. -/
def tdKeep (q : Fin 32) : Bool := q.val ∉ [5, 11, 12, 13, 14, 15, 16, 17]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The compiled `time::digits::<2>`**: with the slice `(p, n)` in the
reader at `d` and the result at `out`, it leaves `digits2Mem` in memory. -/
theorem timeDigits2_correct (m : Machine) {base retAddr out d p : Word} {n : Nat} (hb : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base timeDigits2Code) (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (hd : d.toNat % 4 = 0) (hout : out.toNat % 4 = 0) (hn : n < 2 ^ 32)
    (lp : memLoad32 m.mem d = p) (ln : memLoad32 m.mem (d + 4) = BitVec.ofNat 32 n)
    (sOC : Sep out 8 base timeDigits2Code.length) (sDC : Sep d 8 base timeDigits2Code.length) (sDP : Sep d 8 p 2)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = digits2Mem m.mem out d p n ∧
      ∀ q, tdKeep q = true → reg m' q = reg m q := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have o0 : Sep out 1 base timeDigits2Code.length := by
    have := sOC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
  -- the error tail, from 0x56 with 1 in `a6`
  have err : ∀ {Mx : Word → BitVec 8} {nn : Machine}, St Mx base nn 0x56 (reg nn) → CodeIn Mx base timeDigits2Code →
      reg nn a0 = out → reg nn a6 = 1 → (∀ q, tdKeep q = true → reg nn q = reg m q) →
      ∃ m', Steps nn m' ∧ m'.pc = retAddr ∧ m'.mem = memStore8 (memStore8 Mx (out + 1) 0x19) out 1 ∧
        ∀ q, tdKeep q = true → reg m' q = reg m q := by
    intro Mx nn st hcx r0 r6 kk
    obtain ⟨n1, d1, u1⟩ := st.aluImm hcx td_at_56 (off' := 0x58) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.self.sb hcx td_at_58 (off' := 0x5C) (by decide)
    rw [u1.regs a0, upd_ne' (by decide) st.zero, r0, u1.regs a1] at u2
    simp +decide only [upd_app, ↓reduceIte] at u2
    have hc2 := CodeIn.store8 (v := (aluEval .add (reg nn x0) 0x19).extractLsb' 0 8) hcx (sOC.sub (c := 1) (l := 1) (by decide))
    obtain ⟨n3, d3, u3⟩ := u2.sb hc2 td_at_5c (off' := 0x60) (by decide)
    rw [u1.regs a0, upd_ne' (by decide) st.zero, r0, add_lit_zero, u1.regs a6, upd_ne' (by decide) st.zero, r6] at u3
    have hc3 := CodeIn.store8 (v := (1 : Word).extractLsb' 0 8) hc2 o0
    obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hc3 td_at_60
    refine ⟨n4, .cons d1 (.cons d2 (.cons d3 (.single d4))), ?_, ?_, fun q hq => ?_⟩
    · rw [pc4, add_lit_zero, u1.regs, upd_ne' (by decide) st.zero, kk ra (by decide), hra, hret]
    · rw [mem4, st.zero]; rfl
    · rw [regs4, u1.regs, upd_ne' (fun e => by subst e; revert hq; decide) st.zero]; exact kk q hq
  -- one pass of the loop, from 0x22
  have iter : ∀ {Mx : Word → BitVec 8} {nn : Machine} (j acc : Nat) (q : Word), acc < 10 → j < 2 →
      St Mx base nn 0x22 (reg nn) → CodeIn Mx base timeDigits2Code → reg nn a5 = BitVec.ofNat 32 (j + 1) →
      reg nn a3 = BitVec.ofNat 32 acc → reg nn a2 = q → reg nn (17 : Fin 32) = 0xF6 → reg nn (5 : Fin 32) = 0xA →
      reg nn a6 = 1 → reg nn a0 = out → (∀ q', tdKeep q' = true → reg nn q' = reg m q') →
      (isDigit (Mx q) = false → ∃ m', Steps nn m' ∧ m'.pc = retAddr ∧
        m'.mem = memStore8 (memStore8 Mx (out + 1) 0x19) out 1 ∧ ∀ q', tdKeep q' = true → reg m' q' = reg m q') ∧
      (isDigit (Mx q) = true → ∃ n', Steps nn n' ∧ St Mx base n' 0x22 (reg n') ∧ reg n' a5 = BitVec.ofNat 32 j ∧
        reg n' a3 = BitVec.ofNat 32 (acc * 10 + ((Mx q).toNat - 0x30)) ∧ reg n' a2 = q + 1 ∧
        reg n' (17 : Fin 32) = 0xF6 ∧ reg n' (5 : Fin 32) = 0xA ∧ reg n' a6 = 1 ∧ reg n' a0 = out ∧
        ∀ q', tdKeep q' = true → reg n' q' = reg m q') := by
    intro Mx nn j acc q hacc hj st hcx r5 r3 r2 r17 rt0 r6 r0 kk
    obtain ⟨n1, d1, u1⟩ := st.notTaken hcx 0x24 td_at_22 (by decide) (by
      rw [r5, st.zero]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; intro h
      have := congrArg BitVec.toNat h; rw [ofNat_tn (by omega)] at this; change _ = 0 at this; omega)
    obtain ⟨n2, c2, u2⟩ := St.block [.lbu a1 a2 0x0, .aluImm .add a4 a1 0xFFFFFFC6, .aluImm .and a4 a4 0xFF] u1 hcx
      (off' := 0x30) (by decide) (by simp [BlockOk, BInstr.ok])
    simp only [runBlock, BInstr.run] at u2
    have k2 : ∀ q', q' ≠ a1 → q' ≠ a4 → reg n2 q' = reg nn q' := fun q' h1 h4 => by
      rw [u2.regs, updz ((updz st.zero (by decide)).trans st.zero |> fun h => (updz (r := 0) h (by decide)).trans h) h4,
        updz ((updz st.zero (by decide)).trans st.zero) h4, updz st.zero h1]
    have v4 : reg n2 a4 = aluEval .and (aluEval .add ((Mx q).zeroExtend 32) 0xFFFFFFC6) 0xFF := by
      rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2, add_lit_zero]
    have v1 : reg n2 a1 = (Mx q).zeroExtend 32 := by
      rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2, add_lit_zero]
    refine ⟨fun hbad => ?_, fun hgood => ?_⟩
    · obtain ⟨n3, d3, u3⟩ := u2.self.taken hcx 0x56 td_at_30 (by decide) (by
        rw [v4, k2 17 (by decide) (by decide), r17, td_digit, hbad]; rfl)
      obtain ⟨m', c', h1, h2, h3⟩ := err u3.self hcx (by rw [u3.regs, k2 a0 (by decide) (by decide), r0])
        (by rw [u3.regs, k2 a6 (by decide) (by decide), r6])
        (fun q' hq => by rw [u3.regs, k2 q' (fun e => by subst e; revert hq; decide) (fun e => by subst e; revert hq; decide)]
                         exact kk q' hq)
      exact ⟨m', .cons d1 (c2.trans (.cons d3 c')), h1, h2, h3⟩
    have hd10 := td_lt _ hgood
    obtain ⟨st0, st1, st2, st3⟩ := td_step ⟨acc, hacc⟩ ⟨(Mx q).toNat - 0x30, hd10⟩
    obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hcx 0x34 td_at_30 (by decide) (by
      rw [v4, k2 17 (by decide) (by decide), r17, td_digit, hgood]; rfl)
    obtain ⟨n4, d4, u4⟩ := u3.self.alu hcx td_at_34 (off' := 0x38) (by decide)
    have v44 : reg n4 a4 = 0 := by
      rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u3.regs, k2 a3 (by decide) (by decide), r3, u3.regs, k2 5 (by decide) (by decide), rt0]; exact st0
    obtain ⟨n5, d5, u5⟩ := u4.self.notTaken hcx 0x3A td_at_38 (by decide) (by
      rw [v44, u4.self.zero]; exact bne_self_eq_false _)
    obtain ⟨n6, c6, u6⟩ := St.block [.alu .mul a4 a3 (5 : Fin 32), .aluImm .add a1 a1 0xFFFFFFD0,
      .aluImm .and a3 a1 0xFF, .alu .add a3 a3 a4, .alu .sltu a1 a3 a4, .aluImm .add a2 a2 1,
      .aluImm .add a5 a5 0xFFFFFFFF] u5.self hcx (off' := 0x50) (by decide) (by simp [BlockOk, BInstr.ok])
    simp only [runBlock, BInstr.run] at u6
    have k5 : ∀ q', q' ≠ a4 → reg n5 q' = reg n2 q' := fun q' h => by
      rw [u5.regs, u4.regs, upd_ne' h u3.self.zero, u3.regs]
    have e3 : reg n5 a3 = BitVec.ofNat 32 acc := by rw [k5 a3 (by decide), k2 a3 (by decide) (by decide), r3]
    have e5 : reg n5 (5 : Fin 32) = 0xA := by rw [k5 5 (by decide), k2 5 (by decide) (by decide), rt0]
    have e1 : reg n5 a1 = (Mx q).zeroExtend 32 := by rw [k5 a1 (by decide), v1]
    have e2 : reg n5 a2 = q := by rw [k5 a2 (by decide), k2 a2 (by decide) (by decide), r2]
    have e55 : reg n5 a5 = BitVec.ofNat 32 (j + 1) := by rw [k5 a5 (by decide), k2 a5 (by decide) (by decide), r5]
    have g6 : ∀ q', reg n6 q' = _ := u6.regs
    have v61 : reg n6 a1 = 0 := by
      rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [e3, e5, e1, st1, td_val _ hgood]; exact st2
    obtain ⟨n7, d7, u7⟩ := u6.self.taken hcx 0x22 td_at_50 (by decide) (by rw [v61, u6.self.zero]; rfl)
    refine ⟨n7, .cons d1 (c2.trans (.cons d3 (.cons d4 (.cons d5 (c6.trans (.single d7)))))), u7.self, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, fun q' hq => ?_⟩
    · rw [u7.regs, u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [e55, ev_add]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, ofNat_tn (by omega), ofNat_tn (by omega), show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
      omega
    · rw [u7.regs, u6.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [e3, e5, e1, st1, td_val _ hgood, st3, Nat.mul_comm]
    · rw [u7.regs, u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [e2]; rfl
    · rw [u7.regs, u6.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [k5 17 (by decide), k2 17 (by decide) (by decide), r17]
    · rw [u7.regs, u6.regs]; simp +decide only [upd_app, ↓reduceIte]; exact e5
    · rw [u7.regs, u6.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [k5 a6 (by decide), k2 a6 (by decide) (by decide), r6]
    · rw [u7.regs, u6.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [k5 a0 (by decide), k2 a0 (by decide) (by decide), r0]
    · by_cases h0 : q'.val = 0
      · have : q' = 0 := Fin.ext h0
        subst this; exact u7.self.zero.trans hz.symm
      obtain ⟨h1, h2, h3, h4, h5⟩ : q' ≠ a1 ∧ q' ≠ a2 ∧ q' ≠ a3 ∧ q' ≠ a4 ∧ q' ≠ a5 := by revert hq; revert q'; decide
      rw [u7.regs, u6.regs, upd_ne h0 h5, upd_ne h0 h2, upd_ne h0 h1, upd_ne h0 h3, upd_ne h0 h3, upd_ne h0 h1,
        upd_ne h0 h4, k5 q' h4, k2 q' h1 h4]
      exact kk q' hq
  obtain ⟨n1, d1, u1⟩ := s0.lw hc td_at_0 (off' := 2) (by decide) (by rw [ha1]; exact aligned_add hd (k := 4) (by decide))
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hc td_at_2 (off' := 4) (by decide)
  have v24 : reg n2 a4 = BitVec.ofNat 32 n := by
    rw [u2.regs, upd_ne' (by decide) u1.self.zero, u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha1, ln]
  have v26 : reg n2 a6 = 1 := by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u1.self.zero]; rfl
  have k2 : ∀ q, q ≠ a4 → q ≠ a6 → reg n2 q = reg m q := fun q h4 h6 => by
    rw [u2.regs, upd_ne' h6 u1.self.zero, u1.regs, upd_ne' h4 hz]
  have kk2 : ∀ q, tdKeep q = true → reg n2 q = reg m q := fun q hq =>
    k2 q (fun e => by subst e; revert hq; decide) (fun e => by subst e; revert hq; decide)
  by_cases hn2 : n < 2
  · obtain ⟨n3, d3, u3⟩ := u2.self.taken hc 0x56 td_at_4 (by decide) (by
      rw [v26, v24]; show (!decide ((1 : Word).toNat < (BitVec.ofNat 32 n).toNat)) = true
      rw [ofNat_tn hn, show (1 : Word).toNat = 1 from rfl, decide_eq_false (by omega)]; rfl)
    obtain ⟨m', c', h1, h2, h3⟩ := err u3.self hc (by rw [u3.regs, k2 a0 (by decide) (by decide), ha0])
      (by rw [u3.regs, v26]) (fun q hq => by rw [u3.regs]; exact kk2 q hq)
    exact ⟨m', .cons d1 (.cons d2 (.cons d3 c')), h1, by rw [h2, digits2Mem, ite_eq_left hn2], h3⟩
  obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hc 0x8 td_at_4 (by decide) (by
    rw [v26, v24]; show (!decide ((1 : Word).toNat < (BitVec.ofNat 32 n).toNat)) = false
    rw [ofNat_tn hn, show (1 : Word).toNat = 1 from rfl, decide_eq_true (by omega)]; rfl)
  obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc td_at_8 (off' := 0xA) (by decide)
  obtain ⟨n5, d5, u5⟩ := u4.self.lw hc td_at_a (off' := 0xC) (by decide) (by
    rw [u4.regs, upd_ne' (by decide) u3.self.zero, u3.regs, k2 a1 (by decide) (by decide), ha1, add_lit_zero]; exact hd)
  obtain ⟨n6, c6, u6⟩ := St.block [.aluImm .add (17 : Fin 32) a4 0xFFFFFFFE, .aluImm .add a5 x0 2,
    .aluImm .add a4 a2 2] u5.self hc (off' := 0x16) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u6
  have k5 : ∀ q, q ≠ a2 → q ≠ a3 → reg n5 q = reg n2 q := fun q h2 h3 => by
    rw [u5.regs, upd_ne' h2 u4.self.zero, u4.regs, upd_ne' h3 u3.self.zero, u3.regs]
  have e51 : reg n5 a1 = d := by rw [k5 a1 (by decide) (by decide), k2 a1 (by decide) (by decide), ha1]
  have e52 : reg n5 a2 = p := by
    rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [u4.regs, upd_ne' (by decide) u3.self.zero, u3.regs, k2 a1 (by decide) (by decide), ha1, add_lit_zero, lp]
  have k6 : ∀ q, q ≠ (17 : Fin 32) → q ≠ a5 → q ≠ a4 → reg n6 q = reg n5 q := fun q h7 h5 h4 => by
    rw [u6.regs, updz ((updz u5.self.zero (by decide)).trans u5.self.zero |> fun h =>
      (updz (r := 0) h (by decide)).trans h) h4, updz ((updz u5.self.zero (by decide)).trans u5.self.zero) h5,
      updz u5.self.zero h7]
  obtain ⟨n7, d7, u7⟩ := u6.self.sw hc td_at_16 (off' := 0x18) (by decide) (by
    rw [k6 a1 (by decide) (by decide) (by decide), e51, add_lit_zero]; exact hd)
  have v64 : reg n6 a4 = p + 2 := by
    rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [e52]; rfl
  rw [k6 a1 (by decide) (by decide) (by decide), e51, add_lit_zero, v64] at u7
  have hc7 := CodeIn.store32 (a := d) (v := p + 2) hc ((sDC.sub (c := 0) (l := 4) (by decide)) |> fun h => by
    rwa [add_ofNat_zero] at h)
  obtain ⟨n8, d8, u8⟩ := u7.sw hc7 td_at_18 (off' := 0x1C) (by decide) (by
    rw [k6 a1 (by decide) (by decide) (by decide), e51]; exact aligned_add hd (k := 4) (by decide))
  have v67 : reg n6 17 = BitVec.ofNat 32 n + 0xFFFFFFFE := by
    rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [k5 a4 (by decide) (by decide), v24]; rfl
  rw [k6 a1 (by decide) (by decide) (by decide), e51, v67] at u8
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 m.mem d (p + 2)) (d + 4) (BitVec.ofNat 32 n + 0xFFFFFFFE) = M1 :=
    ⟨_, rfl⟩
  rw [hM1] at u8
  have hc8 : CodeIn M1 base timeDigits2Code := by
    rw [← hM1]; exact CodeIn.store32 hc7 (sDC.sub (c := 4) (l := 4) (by decide))
  obtain ⟨n9, c9, u9⟩ := St.block [.aluImm .add (17 : Fin 32) x0 0xF6, .aluImm .add (5 : Fin 32) x0 0xA] u8.self hc8
    (off' := 0x22) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u9
  have k9 : ∀ q, q ≠ (17 : Fin 32) → q ≠ (5 : Fin 32) → reg n9 q = reg n6 q := fun q h7 h5 => by
    rw [u9.regs, updz ((updz u8.self.zero (by decide)).trans u8.self.zero) h5, updz u8.self.zero h7, u8.regs]
  have sD0 : Sep d 4 p 2 := by have := sDP.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have M1p : ∀ i, i < 2 → M1 (p + BitVec.ofNat 32 i) = m.mem (p + BitVec.ofNat 32 i) := fun i hi => by
    rw [← hM1, memStore32_get_sep (a := d + 4) (sDP.sub (c := 4) (l := 4) (by decide) |>.subR (c := i) (l := 1) (by omega)),
      memStore32_get_sep (a := d) (sD0.subR (c := i) (l := 1) (by omega))]
  have Mp0 : M1 p = m.mem p := by have := M1p 0 (by decide); rwa [add_ofNat_zero] at this
  have Mp1 : M1 (p + 1) = m.mem (p + 1) := M1p 1 (by decide)
  have kk9 : ∀ q, tdKeep q = true → reg n9 q = reg m q := fun q hq => by
    obtain ⟨h7, h5, h4, h2, h3, h55⟩ : q ≠ (17 : Fin 32) ∧ q ≠ (5 : Fin 32) ∧ q ≠ a4 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a5 := by
      revert hq; revert q; decide
    rw [k9 q h7 h5, k6 q h7 h55 h4, k5 q h2 h3]; exact kk2 q hq
  have P1 := iter (Mx := M1) 1 0 p (by decide) (by decide) u9.self hc8
    (by rw [k9 a5 (by decide) (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [k9 a3 (by decide) (by decide), k6 a3 (by decide) (by decide) (by decide), u5.regs, upd_ne' (by decide) u4.self.zero,
          u4.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u3.self.zero]; rfl)
    (by rw [k9 a2 (by decide) (by decide), k6 a2 (by decide) (by decide) (by decide), e52])
    (by rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u8.self.zero]; rfl)
    (by rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [k9 a6 (by decide) (by decide), k6 a6 (by decide) (by decide) (by decide), k5 a6 (by decide) (by decide), v26])
    (by rw [k9 a0 (by decide) (by decide), k6 a0 (by decide) (by decide) (by decide), k5 a0 (by decide) (by decide),
          k2 a0 (by decide) (by decide), ha0])
    kk9
  have S9 : Steps m n9 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (c6.trans (.cons d7 (.cons d8 c9)))))))
  have hn2' : ¬ n < 2 := hn2
  cases hg0 : isDigit (M1 p) with
  | false =>
    obtain ⟨m', c', h1, h2, h3⟩ := P1.1 hg0
    refine ⟨m', S9.trans c', h1, ?_, h3⟩
    rw [h2, digits2Mem, ite_eq_right hn2', show digits2Of (m.mem p) (m.mem (p + 1)) = none by
      unfold digits2Of; rw [← Mp0, hg0]; exact ite_eq_right (fun h => Bool.false_ne_true h.1), ← hM1]
  | true =>
    obtain ⟨n10, c10, u10, r5, r3, r2, r17, rt0, r6, r0, kk10⟩ := P1.2 hg0
    have P2 := iter (Mx := M1) 0 (0 * 10 + ((M1 p).toNat - 0x30)) (p + 1) (by have := td_lt _ hg0; omega) (by decide)
      u10 hc8 r5 r3 r2 r17 rt0 r6 r0 kk10
    cases hg1 : isDigit (M1 (p + 1)) with
    | false =>
      obtain ⟨m', c', h1, h2, h3⟩ := P2.1 hg1
      refine ⟨m', S9.trans (c10.trans c'), h1, ?_, h3⟩
      rw [h2, digits2Mem, ite_eq_right hn2', show digits2Of (m.mem p) (m.mem (p + 1)) = none by
        unfold digits2Of; rw [← Mp0, ← Mp1, hg1]; exact ite_eq_right (fun h => Bool.false_ne_true h.2), ← hM1]
    | true =>
      obtain ⟨n11, c11, u11, s5, s3, -, -, -, -, s0', kk11⟩ := P2.2 hg1
      obtain ⟨n12, d12, u12⟩ := u11.taken hc8 0x62 td_at_22 (by decide) (by rw [s5, u11.zero]; rfl)
      obtain ⟨n13, d13, u13⟩ := u12.self.aluImm hc8 td_at_62 (off' := 0x64) (by decide)
      obtain ⟨n14, d14, u14⟩ := u13.self.sw hc8 td_at_64 (off' := 0x66) (by decide) (by
        rw [u13.regs, upd_ne' (by decide) u12.self.zero, u12.regs, s0']; exact aligned_add hout (k := 4) (by decide))
      rw [u13.regs a0, upd_ne' (by decide) u12.self.zero, u12.regs, s0', u13.regs a3, upd_ne' (by decide) u12.self.zero,
        u12.regs, s3] at u14
      have hc14 := CodeIn.store32 (a := out + 4)
        (v := BitVec.ofNat 32 ((0 * 10 + ((M1 p).toNat - 0x30)) * 10 + ((M1 (p + 1)).toNat - 0x30))) hc8
        (sOC.sub (c := 4) (l := 4) (by decide))
      obtain ⟨n15, d15, u15⟩ := u14.jump hc14 td_at_66 (off' := 0x5C) (by decide) (by
        rw [u14.pc, show base + BitVec.ofNat 32 0x66 + 0xFFFFFFF6 = base + BitVec.ofNat 32 0x5C by rw [BitVec.add_assoc]; rfl]
        exact even_bit0 (even_at base hb 0x5C (by decide)))
      obtain ⟨n16, d16, u16⟩ := u15.sb hc14 td_at_5c (off' := 0x60) (by decide)
      rw [u13.regs a0, upd_ne' (by decide) u12.self.zero, u12.regs, s0', add_lit_zero, u13.regs a6] at u16
      simp +decide only [upd_app, ↓reduceIte] at u16
      have hc16 := CodeIn.store8 (v := (aluEval .add (reg n12 x0) 0).extractLsb' 0 8) hc14 o0
      obtain ⟨n17, d17, pc17, mem17, regs17⟩ := u16.jalr hc16 td_at_60
      refine ⟨n17, S9.trans (c10.trans (c11.trans (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16
        (.single d17)))))))), ?_, ?_, fun q hq => ?_⟩
      · rw [pc17, add_lit_zero, u13.regs, upd_ne' (by decide) u12.self.zero, u12.regs, kk11 ra (by decide), hra, hret]
      · rw [mem17, u12.self.zero, digits2Mem, ite_eq_right hn2', show digits2Of (m.mem p) (m.mem (p + 1)) =
          some (((m.mem p).toNat - 0x30) * 10 + ((m.mem (p + 1)).toNat - 0x30)) by
            unfold digits2Of; rw [← Mp0, ← Mp1, hg0, hg1]; exact ite_eq_left ⟨rfl, rfl⟩]
        dsimp only
        rw [← hM1, ← Mp0, ← Mp1, Nat.zero_mul, Nat.zero_add, ← hM1]; rfl
      · rw [regs17, u13.regs, upd_ne' (fun e => by subst e; revert hq; decide) u12.self.zero, u12.regs]; exact kk11 q hq

end C3.RV32
