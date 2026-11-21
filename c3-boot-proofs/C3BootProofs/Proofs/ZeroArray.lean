import C3BootProofs.Proofs.Sha2Final

/-!
# `hybrid_array`'s zeroing `from_fn` for 48 and 64 bytes, as compiled

These are `shaZero32_correct`'s function for 48 and 64 bytes: the same code
with a larger frame and count.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem za48_at_0 : fetchRel zeroArray48Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem za48_at_2 : fetchRel zeroArray48Code 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem za48_at_4 : fetchRel zeroArray48Code 0x4 = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem za48_at_6 : fetchRel zeroArray48Code 0x6 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem za48_at_a : fetchRel zeroArray48Code 0xA = some (.branch .beq a2 x0 0xC, 2) := by decide
theorem za48_at_c : fetchRel zeroArray48Code 0xC = some (.store .sb a1 x0 0x0, 4) := by decide
theorem za48_at_10 : fetchRel zeroArray48Code 0x10 = some (.aluImm .add a1 a1 0x1, 2) := by decide
theorem za48_at_12 : fetchRel zeroArray48Code 0x12 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem za48_at_14 : fetchRel zeroArray48Code 0x14 = some (.branch .bne a2 x0 0xFFFFFFF8, 2) := by decide
theorem za48_at_16 : fetchRel zeroArray48Code 0x16 = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem za48_at_18 : fetchRel zeroArray48Code 0x18 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem za48_at_1c : fetchRel zeroArray48Code 0x1C = some (.auipc ra 0x7000, 4) := by decide
theorem za48_at_20 : fetchRel zeroArray48Code 0x20 = some (.jalr ra ra 0x142, 4) := by decide
theorem za48_at_24 : fetchRel zeroArray48Code 0x24 = some (.load .lw ra sp 0x3C, 2) := by decide
theorem za48_at_26 : fetchRel zeroArray48Code 0x26 = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem za48_at_28 : fetchRel zeroArray48Code 0x28 = some (.jalr x0 ra 0x0, 2) := by decide
theorem za64_at_0 : fetchRel zeroArray64Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFB0, 2) := by decide
theorem za64_at_2 : fetchRel zeroArray64Code 0x2 = some (.store .sw sp ra 0x4C, 2) := by decide
theorem za64_at_4 : fetchRel zeroArray64Code 0x4 = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem za64_at_6 : fetchRel zeroArray64Code 0x6 = some (.aluImm .add a2 x0 0x40, 4) := by decide
theorem za64_at_a : fetchRel zeroArray64Code 0xA = some (.branch .beq a2 x0 0xC, 2) := by decide
theorem za64_at_c : fetchRel zeroArray64Code 0xC = some (.store .sb a1 x0 0x0, 4) := by decide
theorem za64_at_10 : fetchRel zeroArray64Code 0x10 = some (.aluImm .add a1 a1 0x1, 2) := by decide
theorem za64_at_12 : fetchRel zeroArray64Code 0x12 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem za64_at_14 : fetchRel zeroArray64Code 0x14 = some (.branch .bne a2 x0 0xFFFFFFF8, 2) := by decide
theorem za64_at_16 : fetchRel zeroArray64Code 0x16 = some (.aluImm .add a1 sp 0xC, 2) := by decide
theorem za64_at_18 : fetchRel zeroArray64Code 0x18 = some (.aluImm .add a2 x0 0x40, 4) := by decide
theorem za64_at_1c : fetchRel zeroArray64Code 0x1C = some (.auipc ra 0x7000, 4) := by decide
theorem za64_at_20 : fetchRel zeroArray64Code 0x20 = some (.jalr ra ra 0x16C, 4) := by decide
theorem za64_at_24 : fetchRel zeroArray64Code 0x24 = some (.load .lw ra sp 0x4C, 2) := by decide
theorem za64_at_26 : fetchRel zeroArray64Code 0x26 = some (.aluImm .add sp sp 0x50, 2) := by decide
theorem za64_at_28 : fetchRel zeroArray64Code 0x28 = some (.jalr x0 ra 0x0, 2) := by decide
end

set_option maxRecDepth 20000 in
/-- `from_fn`'s loop, from offset 0xC: it stores a zero byte and moves on,
until the count runs out. -/
theorem zero_loop48 {M1 : Word → BitVec 8} {B : Word}
    (hc : ∀ j, j ≤ 48 → CodeIn (fillBytes M1 B 0 j) (BitVec.ofNat 32 zeroArray48Address) zeroArray48Code) :
    ∀ k q (n : Machine), q + k = 48 → 0 < k →
      St (fillBytes M1 B 0 q) (BitVec.ofNat 32 zeroArray48Address) n 0xC (reg n) →
      reg n a2 = BitVec.ofNat 32 k → reg n a1 = B + BitVec.ofNat 32 q →
      ∃ n', Steps n n' ∧ St (fillBytes M1 B 0 48) (BitVec.ofNat 32 zeroArray48Address) n' 0x16 (reg n') ∧
        ∀ r, r ≠ a1 → r ≠ a2 → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro q n hqe _ s ha2 ha1
    have hcq := hc q (by omega)
    have hcq1 := hc (q + 1) (by omega)
    obtain ⟨n1, d1, u1⟩ := s.sb hcq za48_at_c (off' := 0x10) (by decide)
    rw [ha1, add_lit_zero, s.zero, show (0 : Word).extractLsb' 0 8 = (0 : BitVec 8) from rfl,
      fillBytes_succ (by omega)] at u1
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hcq1 za48_at_10 (off' := 0x12) (by decide)
    obtain ⟨n3, d3, u3⟩ := u2.aluImm hcq1 za48_at_12 (off' := 0x14) (by decide)
    have r3 : ∀ r, reg n3 r = upd (upd (reg n) a1 (B + BitVec.ofNat 32 (q + 1))) a2 (BitVec.ofNat 32 k) r := by
      intro r
      rw [u3.regs]
      simp only [upd, show (a2 : Fin 32) ≠ a1 by decide, ite_false, ha2, ha1,
        dec_ofNat_succ (show k + 1 < 2 ^ 32 by omega), show (12 : Fin 32).val ≠ 0 by decide]
      rw [show aluEval .add (B + BitVec.ofNat 32 q) 1 = B + BitVec.ofNat 32 (q + 1) from add_ofNat_assoc B q 1]
    have frame : ∀ r, r ≠ a1 → r ≠ a2 → reg n3 r = reg n r := fun r h1 h2 => by
      rw [r3]; simp only [upd, h1, h2, ite_false]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp; exact s.zero.symm
      · simp [h0]
    have c3 : reg n3 a2 = BitVec.ofNat 32 k := by rw [r3]; simp +decide [upd]
    have p3 : reg n3 a1 = B + BitVec.ofNat 32 (q + 1) := by rw [r3]; simp +decide [upd]
    have z3 : reg n3 x0 = 0 := u3.self.zero
    have u3' : St (fillBytes M1 B 0 (q + 1)) (BitVec.ofNat 32 zeroArray48Address) n3 0x14 (reg n3) := u3.self
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n4, d4, u4⟩ := u3'.notTaken hcq1 0x16 za48_at_14 (by decide) (by simp [branchTaken, c3, z3])
      have hq : q + 1 = 48 := by omega
      rw [hq] at u4
      exact ⟨n4, .cons d1 (.cons d2 (.cons d3 (.single d4))), u4.self,
        fun r h1 h2 => by rw [u4.regs, frame r h1 h2]⟩
    · obtain ⟨n4, d4, u4⟩ := u3'.taken hcq1 0xC za48_at_14 (by decide) (by
        simp only [branchTaken, c3, z3, bne_iff_ne, ne_eq]
        intro h; exact hk (ofNat_inj (by omega) (by decide) h))
      obtain ⟨n5, c5, u5, f5⟩ := ih (q + 1) n4 (by omega) (by omega) u4.self
        (by rw [u4.regs, c3]) (by rw [u4.regs, p3])
      exact ⟨n5, .cons d1 (.cons d2 (.cons d3 (.cons d4 c5))), u5,
        fun r h1 h2 => by rw [f5 r h1 h2, u4.regs, frame r h1 h2]⟩


set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **`hybrid_array`'s zeroing `from_fn` for 48 bytes, as compiled.** Called
with `d`, it zeroes the 48 bytes at `d`: it fills 48 bytes of its stack
frame with zeros, one byte at a time, and copies them to `d` with `memcpy`.
It returns with `sp` restored and changes no memory outside `d` and the 0x50
bytes of stack below `sp`. Both `d` and the stack are below 0x40000000,
apart from the code. -/
theorem zeroArray48_correct (m : Machine) {d T retAddr : Word}
    (hc : CodeIn m.mem (BitVec.ofNat 32 zeroArray48Address) zeroArray48Code)
    (hMS : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode)
    (hMB : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode)
    (hpc : m.pc = BitVec.ofNat 32 zeroArray48Address) (ha0 : reg m a0 = d) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = T) (hTa : T.toNat % 16 = 0)
    (hTl : 0x50 ≤ T.toNat) (hTw : T.toNat ≤ 0x40000000) (hdw : d.toNat + 48 ≤ 0x40000000)
    (hdT : Sep d 48 (T + 0xFFFFFFB0) 0x50) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = T ∧
      (∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
        r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → reg m' r = reg m r) ∧
      ∀ x, Sep (T + 0xFFFFFFB0) 0x50 x 1 → m'.mem x = fillBytes m.mem d 0 48 x := by
  let Z := BitVec.ofNat 32 zeroArray48Address
  let M0 := m.mem
  let R := T + 0xFFFFFFB0
  have hRn : R.toNat = T.toNat - 0x50 := by
    show (T + 0xFFFFFFB0).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFFB0 : Word).toNat = 2 ^ 32 - 0x50 from rfl]; omega
  have hRc : ∀ c, c < 0x50 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- Data below 0x40000000 is apart from code above it.
  have dc : ∀ (a : Word) (k : Nat) (b : Word) (l : Nat), a.toNat + k ≤ 0x40000000 → 0x40000000 ≤ b.toNat →
      b.toNat + l ≤ 2 ^ 32 → Sep a k b l := fun a k b l h1 h2 h3 => data_code h1 h2 h3
  have st0 : St M0 Z m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  obtain ⟨n1, d1, u1⟩ := st0.aluImm hc za48_at_0 (off' := 2) (by decide)
  have K1 := u1.upd_ne st0.zero
  have u1' : St M0 Z n1 2 (reg n1) := u1.self
  have sp1 : reg n1 sp = R + BitVec.ofNat 32 0x10 := by
    rw [u1.upd_eq (by decide), hsp]
    show T + 0xFFFFFFC0 = T + 0xFFFFFFB0 + BitVec.ofNat 32 0x10; rw [BitVec.add_assoc]; rfl
  obtain ⟨n2, d2, u2⟩ := u1'.sw hc za48_at_2 (off' := 4) (by decide)
    (by rw [sp1, show (0x3C : Word) = BitVec.ofNat 32 0x3C from rfl, add_ofNat_assoc, hRc _ (by omega)]; have := hTa; omega)
  rw [sp1, show (0x3C : Word) = BitVec.ofNat 32 0x3C from rfl, add_ofNat_assoc, K1 ra (by decide), hra] at u2
  let M1 := memStore32 M0 (R + BitVec.ofNat 32 (0x10 + 0x3C)) retAddr
  have cM1 : ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn M1 b code := fun b code h hb hbl =>
    h.store32 (dc _ _ _ _ (by rw [hRc _ (by omega)]; omega) hb hbl)
  have hc1 := cM1 _ _ hc (by decide) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.aluImm hc1 za48_at_4 (off' := 6) (by decide)
  have K3 := u3.upd_ne u1'.zero
  have u3' : St M1 Z n3 6 (reg n3) := u3.self
  obtain ⟨n4, d4, u4⟩ := u3'.aluImm hc1 za48_at_6 (off' := 0xA) (by decide)
  have K4' := u4.upd_ne u3'.zero
  have K4 : ∀ r, r ≠ a1 → r ≠ a2 → reg n4 r = reg n1 r := fun r q1 q2 => by rw [K4' r q2, K3 r q1]
  have a2_4 : reg n4 a2 = BitVec.ofNat 32 48 := by rw [u4.upd_eq (by decide), u3'.zero]; rfl
  have a1_4 : reg n4 a1 = R + BitVec.ofNat 32 0x1C := by
    rw [K4' a1 (by decide), u3.upd_eq (by decide), sp1]
    show R + BitVec.ofNat 32 0x10 + BitVec.ofNat 32 0xC = _; rw [add_ofNat_assoc]
  have u4' : St M1 Z n4 0xA (reg n4) := u4.self
  obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc1 0xC za48_at_a (by decide) (by
    simp only [branchTaken]; rw [a2_4, u4'.zero]; decide)
  let B := R + BitVec.ofNat 32 0x1C
  have hBs : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 → Sep B 48 b l :=
    fun b l hb hbl => dc _ _ _ _ (by rw [hRc _ (by omega)]; omega) hb hbl
  have hcF : ∀ j, j ≤ 48 → CodeIn (fillBytes M1 B 0 j) Z zeroArray48Code := fun j hj =>
    hc1.fillBytes (hBs _ _ (by decide) (by decide)) hj
  rw [← fillBytes_zero M1 B 0] at u5
  obtain ⟨n6, c6, u6, K6⟩ := zero_loop48 hcF 48 0 n5 rfl (by decide) u5.self
    (by rw [u5.regs, a2_4]) (by rw [u5.regs, a1_4, add_ofNat_zero])
  let Mf := fillBytes M1 B 0 48
  have hcf := hcF 48 (Nat.le_refl 48)
  obtain ⟨n7, d7, u7⟩ := u6.aluImm hcf za48_at_16 (off' := 0x18) (by decide)
  obtain ⟨n8, d8, u8⟩ := u7.aluImm hcf za48_at_18 (off' := 0x1C) (by decide)
  obtain ⟨n9, d9, u9⟩ := u8.auipc hcf za48_at_1c (off' := 0x20) (by decide)
  obtain ⟨n10, d10, pc10, mem10, regs10⟩ := u9.call hcf za48_at_20
  have K6' : ∀ r, r ≠ a1 → r ≠ a2 → reg n6 r = reg n1 r := fun r q1 q2 => by
    rw [K6 r q1 q2, u5.regs, K4 r q1 q2]
  have sp6 : reg n6 sp = R + BitVec.ofNat 32 0x10 := by rw [K6' sp (by decide) (by decide), sp1]
  have r10 : ∀ r, reg n10 r = upd (upd (upd (upd (reg n6) a1 (B)) a2 (BitVec.ofNat 32 48)) ra
      (Z + BitVec.ofNat 32 0x1C + 0x7000)) ra (Z + BitVec.ofNat 32 0x24) r := by
    intro r
    rw [regs10]
    have e1 : aluEval .add (reg n6 sp) 0xC = B := by
      rw [sp6]; show R + BitVec.ofNat 32 0x10 + BitVec.ofNat 32 0xC = R + BitVec.ofNat 32 0x1C
      rw [add_ofNat_assoc]
    have e2 : aluEval .add (upd (reg n6) a1 (aluEval .add (reg n6 sp) 0xC) x0) 0x30 = BitVec.ofNat 32 48 := by
      simp only [upd, show (x0 : Fin 32).val = 0 from rfl, ite_true]; rfl
    rw [e2, e1, show Z + BitVec.ofNat 32 0x20 + 4 = Z + BitVec.ofNat 32 0x24 from by
      rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]]
  have K10 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ ra → reg n10 r = reg n1 r := fun r q1 q2 q3 => by
    rw [r10]; simp only [upd, q1, q2, q3, ite_false]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp; exact (K6' 0 (by decide) (by decide)).trans u1'.zero |>.symm
    · simp [h0, K6' r q1 q2]
  have pc10' : n10.pc = BitVec.ofNat 32 memcpyStubAddress := by
    rw [pc10, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
    decide
  have sp10 : reg n10 sp = R + BitVec.ofNat 32 0x10 := by
    rw [K10 sp (by decide) (by decide) (by decide), sp1]
  have eF : R + BitVec.ofNat 32 0x10 + 0xFFFFFFF0 = R := by
    rw [BitVec.add_assoc]; exact BitVec.add_zero R
  obtain ⟨n11, c11, pc11, sp11, a011, mem11, K11⟩ := memcpy_correct n10 (BitVec.ofNat 32 memcpyStubAddress)
    (Z + BitVec.ofNat 32 0x24) d B 48
    (fun i hi => by
      show n10.mem _ = _; rw [mem10]
      exact ((cM1 _ _ hMS (by decide) (by decide)).fillBytes (hBs _ _ (by decide) (by decide)) (Nat.le_refl 48)) i hi)
    (by decide) pc10'
    (by rw [K10 a0 (by decide) (by decide) (by decide), K1 a0 (by decide), ha0])
    (by rw [r10]; simp +decide [upd])
    (by rw [r10]; simp +decide [upd])
    (by rw [r10]; simp +decide [upd]) (by decide)
    (by
      rw [mem10, sp10, eF]
      exact { code := (cM1 _ _ hMB (by decide) (by decide)).fillBytes (hBs _ _ (by decide) (by decide))
                (Nat.le_refl 48)
              hDC := dc _ _ _ _ hdw (by decide) (by decide)
              hFC := dc _ _ _ _ (by omega) (by decide) (by decide)
              hdF := by have h := hdT.subR (c := 0) (l := 16) (by omega); rwa [add_ofNat_zero] at h
              hsF := by
                have h := sep_offsets R (c := 0x1C) (n := 48) (d := 0) (k := 16) (Or.inr (by omega)) (by omega)
                  (by omega)
                rwa [add_ofNat_zero] at h
              hsep := hdT.subR (c := 0x1C) (l := 48) (by omega)
              hF := by rw [hRn]; omega
              hFw := by omega
              hdw := by omega
              hsw := by rw [hRc _ (by omega)]; omega })
  rw [sp10, eF, mem10] at mem11
  let MA := n11.mem
  have mA : ∀ x, Sep R 16 x 1 → MA x = copyBytes Mf d B 48 x := mem11
  have cA : ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn MA b code := fun b code h hb hbl i hi => by
    rw [mA _ ((dc R 16 b code.length (by omega) hb hbl).subR (c := i) (l := 1) (by omega)),
      copyBytes_sep ((dc d 48 b code.length hdw hb hbl).subR (c := i) (l := 1) (by omega)) (Nat.le_refl 48)]
    exact (cM1 _ _ h hb hbl).fillBytes (hBs _ _ hb hbl) (Nat.le_refl 48) i hi
  have hcA := cA _ _ hc (by decide) (by decide)
  have u11 : St MA Z n11 0x24 (reg n11) := ⟨by rw [pc11], rfl, fun _ => rfl⟩
  have sp11' : reg n11 sp = R + BitVec.ofNat 32 0x10 := by rw [sp11, sp10]
  obtain ⟨n12, d12, u12⟩ := u11.lw hcA za48_at_24 (off' := 0x26) (by decide)
    (by rw [sp11', show (0x3C : Word) = BitVec.ofNat 32 0x3C from rfl, add_ofNat_assoc, hRc _ (by omega)]; have := hTa; omega)
  have slot : memLoad32 MA (reg n11 sp + 0x3C) = retAddr := by
    rw [sp11', show (0x3C : Word) = BitVec.ofNat 32 0x3C from rfl, add_ofNat_assoc, ← memLoad32_store32_same M0 (R + BitVec.ofNat 32 (0x10 + 0x3C)) retAddr]
    apply memLoad32_congr; intro j hj
    rw [add_ofNat_assoc]
    have hx1 : Sep R 16 (R + BitVec.ofNat 32 (0x10 + 0x3C + j)) 1 :=
      sep_offsets R (c := 0) (n := 16) (d := 0x10 + 0x3C + j) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
        |> fun h => by rwa [add_ofNat_zero] at h
    rw [mA _ hx1, copyBytes_sep ((hdT.subR (c := 0x10 + 0x3C + j) (l := 1) (by omega))) (Nat.le_refl 48)]
    show fillBytes M1 B 0 48 _ = _
    exact fillBytes_sep (sep_offsets R (c := 0x1C) (n := 48) (d := 0x10 + 0x3C + j) (k := 1) (Or.inl (by omega))
      (by omega) (by omega)) (Nat.le_refl 48)
  rw [slot] at u12
  have K12 := u12.upd_ne u11.zero
  have u12' : St MA Z n12 0x26 (reg n12) := u12.self
  obtain ⟨n13, d13, u13⟩ := u12'.aluImm hcA za48_at_26 (off' := 0x28) (by decide)
  have K13 := u13.upd_ne u12'.zero
  have u13' : St MA Z n13 0x28 (reg n13) := u13.self
  obtain ⟨n14, d14, pc14, mem14, regs14⟩ := u13'.jalr hcA za48_at_28
  have ra13 : reg n13 ra = retAddr := by rw [K13 ra (by decide), u12.upd_eq (by decide)]
  have sp13 : reg n13 sp = T := by
    rw [u13.upd_eq (by decide), K12 sp (by decide), sp11']
    show R + BitVec.ofNat 32 0x10 + 0x40 = T
    rw [BitVec.add_assoc]; show T + 0xFFFFFFB0 + (BitVec.ofNat 32 0x10 + 0x40) = T
    rw [BitVec.add_assoc]; exact BitVec.add_zero T
  have k11 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg n11 r = reg n10 r := K11
  refine ⟨n14, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (c6.trans (.cons d7 (.cons d8 (.cons d9
    (.cons d10 (c11.trans (.cons d12 (.cons d13 (.single d14))))))))))))), ?_, ?_,
    fun r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 => ?_, fun x hx => ?_⟩
  · rw [pc14, ra13, add_lit_zero, hret]
  · rw [regs14, sp13]
  · rw [regs14]
    by_cases hra' : r = ra
    · subst hra'; rw [ra13, hra]
    by_cases hsp' : r = sp
    · subst hsp'; rw [sp13, hsp]
    rw [K13 r hsp', K12 r hra', k11 r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 hsp', K10 r q11 q12 hra',
      K1 r hsp']
  · rw [mem14]
    show MA x = _
    rw [mA x (hx.sub (c := 0) (l := 16) (by omega) |> fun h => by rwa [add_ofNat_zero] at h)]
    unfold copyBytes fillBytes
    by_cases hin : (x - d).toNat < 48
    · rw [ite_eq_left hin, ite_eq_left hin]
      show fillBytes M1 B 0 48 _ = _
      unfold fillBytes
      rw [BitVec.add_comm B, BitVec.add_sub_cancel, ite_eq_left hin]
    · rw [ite_eq_right hin, ite_eq_right hin]
      show fillBytes M1 B 0 48 x = M0 x
      rw [fillBytes_sep (hx.sub (c := 0x1C) (l := 48) (by omega)) (Nat.le_refl 48)]
      exact memStore32_ne fun i hi e => hx (0x10 + 0x3C + i) (by omega) 0 (by decide)
        (by rw [add_ofNat_zero, ← add_ofNat_assoc]; exact e.symm)


set_option maxRecDepth 20000 in
/-- `from_fn`'s loop, from offset 0xC: it stores a zero byte and moves on,
until the count runs out. -/
theorem zero_loop64 {M1 : Word → BitVec 8} {B : Word}
    (hc : ∀ j, j ≤ 64 → CodeIn (fillBytes M1 B 0 j) (BitVec.ofNat 32 zeroArray64Address) zeroArray64Code) :
    ∀ k q (n : Machine), q + k = 64 → 0 < k →
      St (fillBytes M1 B 0 q) (BitVec.ofNat 32 zeroArray64Address) n 0xC (reg n) →
      reg n a2 = BitVec.ofNat 32 k → reg n a1 = B + BitVec.ofNat 32 q →
      ∃ n', Steps n n' ∧ St (fillBytes M1 B 0 64) (BitVec.ofNat 32 zeroArray64Address) n' 0x16 (reg n') ∧
        ∀ r, r ≠ a1 → r ≠ a2 → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro q n hqe _ s ha2 ha1
    have hcq := hc q (by omega)
    have hcq1 := hc (q + 1) (by omega)
    obtain ⟨n1, d1, u1⟩ := s.sb hcq za64_at_c (off' := 0x10) (by decide)
    rw [ha1, add_lit_zero, s.zero, show (0 : Word).extractLsb' 0 8 = (0 : BitVec 8) from rfl,
      fillBytes_succ (by omega)] at u1
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hcq1 za64_at_10 (off' := 0x12) (by decide)
    obtain ⟨n3, d3, u3⟩ := u2.aluImm hcq1 za64_at_12 (off' := 0x14) (by decide)
    have r3 : ∀ r, reg n3 r = upd (upd (reg n) a1 (B + BitVec.ofNat 32 (q + 1))) a2 (BitVec.ofNat 32 k) r := by
      intro r
      rw [u3.regs]
      simp only [upd, show (a2 : Fin 32) ≠ a1 by decide, ite_false, ha2, ha1,
        dec_ofNat_succ (show k + 1 < 2 ^ 32 by omega), show (12 : Fin 32).val ≠ 0 by decide]
      rw [show aluEval .add (B + BitVec.ofNat 32 q) 1 = B + BitVec.ofNat 32 (q + 1) from add_ofNat_assoc B q 1]
    have frame : ∀ r, r ≠ a1 → r ≠ a2 → reg n3 r = reg n r := fun r h1 h2 => by
      rw [r3]; simp only [upd, h1, h2, ite_false]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp; exact s.zero.symm
      · simp [h0]
    have c3 : reg n3 a2 = BitVec.ofNat 32 k := by rw [r3]; simp +decide [upd]
    have p3 : reg n3 a1 = B + BitVec.ofNat 32 (q + 1) := by rw [r3]; simp +decide [upd]
    have z3 : reg n3 x0 = 0 := u3.self.zero
    have u3' : St (fillBytes M1 B 0 (q + 1)) (BitVec.ofNat 32 zeroArray64Address) n3 0x14 (reg n3) := u3.self
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n4, d4, u4⟩ := u3'.notTaken hcq1 0x16 za64_at_14 (by decide) (by simp [branchTaken, c3, z3])
      have hq : q + 1 = 64 := by omega
      rw [hq] at u4
      exact ⟨n4, .cons d1 (.cons d2 (.cons d3 (.single d4))), u4.self,
        fun r h1 h2 => by rw [u4.regs, frame r h1 h2]⟩
    · obtain ⟨n4, d4, u4⟩ := u3'.taken hcq1 0xC za64_at_14 (by decide) (by
        simp only [branchTaken, c3, z3, bne_iff_ne, ne_eq]
        intro h; exact hk (ofNat_inj (by omega) (by decide) h))
      obtain ⟨n5, c5, u5, f5⟩ := ih (q + 1) n4 (by omega) (by omega) u4.self
        (by rw [u4.regs, c3]) (by rw [u4.regs, p3])
      exact ⟨n5, .cons d1 (.cons d2 (.cons d3 (.cons d4 c5))), u5,
        fun r h1 h2 => by rw [f5 r h1 h2, u4.regs, frame r h1 h2]⟩


set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **`hybrid_array`'s zeroing `from_fn` for 64 bytes, as compiled.** Called
with `d`, it zeroes the 64 bytes at `d`: it fills 64 bytes of its stack
frame with zeros, one byte at a time, and copies them to `d` with `memcpy`.
It returns with `sp` restored and changes no memory outside `d` and the 0x60
bytes of stack below `sp`. Both `d` and the stack are below 0x40000000,
apart from the code. -/
theorem zeroArray64_correct (m : Machine) {d T retAddr : Word}
    (hc : CodeIn m.mem (BitVec.ofNat 32 zeroArray64Address) zeroArray64Code)
    (hMS : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode)
    (hMB : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode)
    (hpc : m.pc = BitVec.ofNat 32 zeroArray64Address) (ha0 : reg m a0 = d) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = T) (hTa : T.toNat % 16 = 0)
    (hTl : 0x60 ≤ T.toNat) (hTw : T.toNat ≤ 0x40000000) (hdw : d.toNat + 64 ≤ 0x40000000)
    (hdT : Sep d 64 (T + 0xFFFFFFA0) 0x60) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = T ∧
      (∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
        r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → reg m' r = reg m r) ∧
      ∀ x, Sep (T + 0xFFFFFFA0) 0x60 x 1 → m'.mem x = fillBytes m.mem d 0 64 x := by
  let Z := BitVec.ofNat 32 zeroArray64Address
  let M0 := m.mem
  let R := T + 0xFFFFFFA0
  have hRn : R.toNat = T.toNat - 0x60 := by
    show (T + 0xFFFFFFA0).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFFA0 : Word).toNat = 2 ^ 32 - 0x60 from rfl]; omega
  have hRc : ∀ c, c < 0x60 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- Data below 0x40000000 is apart from code above it.
  have dc : ∀ (a : Word) (k : Nat) (b : Word) (l : Nat), a.toNat + k ≤ 0x40000000 → 0x40000000 ≤ b.toNat →
      b.toNat + l ≤ 2 ^ 32 → Sep a k b l := fun a k b l h1 h2 h3 => data_code h1 h2 h3
  have st0 : St M0 Z m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  obtain ⟨n1, d1, u1⟩ := st0.aluImm hc za64_at_0 (off' := 2) (by decide)
  have K1 := u1.upd_ne st0.zero
  have u1' : St M0 Z n1 2 (reg n1) := u1.self
  have sp1 : reg n1 sp = R + BitVec.ofNat 32 0x10 := by
    rw [u1.upd_eq (by decide), hsp]
    show T + 0xFFFFFFB0 = T + 0xFFFFFFA0 + BitVec.ofNat 32 0x10; rw [BitVec.add_assoc]; rfl
  obtain ⟨n2, d2, u2⟩ := u1'.sw hc za64_at_2 (off' := 4) (by decide)
    (by rw [sp1, show (0x4C : Word) = BitVec.ofNat 32 0x4C from rfl, add_ofNat_assoc, hRc _ (by omega)]; have := hTa; omega)
  rw [sp1, show (0x4C : Word) = BitVec.ofNat 32 0x4C from rfl, add_ofNat_assoc, K1 ra (by decide), hra] at u2
  let M1 := memStore32 M0 (R + BitVec.ofNat 32 (0x10 + 0x4C)) retAddr
  have cM1 : ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn M1 b code := fun b code h hb hbl =>
    h.store32 (dc _ _ _ _ (by rw [hRc _ (by omega)]; omega) hb hbl)
  have hc1 := cM1 _ _ hc (by decide) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.aluImm hc1 za64_at_4 (off' := 6) (by decide)
  have K3 := u3.upd_ne u1'.zero
  have u3' : St M1 Z n3 6 (reg n3) := u3.self
  obtain ⟨n4, d4, u4⟩ := u3'.aluImm hc1 za64_at_6 (off' := 0xA) (by decide)
  have K4' := u4.upd_ne u3'.zero
  have K4 : ∀ r, r ≠ a1 → r ≠ a2 → reg n4 r = reg n1 r := fun r q1 q2 => by rw [K4' r q2, K3 r q1]
  have a2_4 : reg n4 a2 = BitVec.ofNat 32 64 := by rw [u4.upd_eq (by decide), u3'.zero]; rfl
  have a1_4 : reg n4 a1 = R + BitVec.ofNat 32 0x1C := by
    rw [K4' a1 (by decide), u3.upd_eq (by decide), sp1]
    show R + BitVec.ofNat 32 0x10 + BitVec.ofNat 32 0xC = _; rw [add_ofNat_assoc]
  have u4' : St M1 Z n4 0xA (reg n4) := u4.self
  obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc1 0xC za64_at_a (by decide) (by
    simp only [branchTaken]; rw [a2_4, u4'.zero]; decide)
  let B := R + BitVec.ofNat 32 0x1C
  have hBs : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 → Sep B 64 b l :=
    fun b l hb hbl => dc _ _ _ _ (by rw [hRc _ (by omega)]; omega) hb hbl
  have hcF : ∀ j, j ≤ 64 → CodeIn (fillBytes M1 B 0 j) Z zeroArray64Code := fun j hj =>
    hc1.fillBytes (hBs _ _ (by decide) (by decide)) hj
  rw [← fillBytes_zero M1 B 0] at u5
  obtain ⟨n6, c6, u6, K6⟩ := zero_loop64 hcF 64 0 n5 rfl (by decide) u5.self
    (by rw [u5.regs, a2_4]) (by rw [u5.regs, a1_4, add_ofNat_zero])
  let Mf := fillBytes M1 B 0 64
  have hcf := hcF 64 (Nat.le_refl 64)
  obtain ⟨n7, d7, u7⟩ := u6.aluImm hcf za64_at_16 (off' := 0x18) (by decide)
  obtain ⟨n8, d8, u8⟩ := u7.aluImm hcf za64_at_18 (off' := 0x1C) (by decide)
  obtain ⟨n9, d9, u9⟩ := u8.auipc hcf za64_at_1c (off' := 0x20) (by decide)
  obtain ⟨n10, d10, pc10, mem10, regs10⟩ := u9.call hcf za64_at_20
  have K6' : ∀ r, r ≠ a1 → r ≠ a2 → reg n6 r = reg n1 r := fun r q1 q2 => by
    rw [K6 r q1 q2, u5.regs, K4 r q1 q2]
  have sp6 : reg n6 sp = R + BitVec.ofNat 32 0x10 := by rw [K6' sp (by decide) (by decide), sp1]
  have r10 : ∀ r, reg n10 r = upd (upd (upd (upd (reg n6) a1 (B)) a2 (BitVec.ofNat 32 64)) ra
      (Z + BitVec.ofNat 32 0x1C + 0x7000)) ra (Z + BitVec.ofNat 32 0x24) r := by
    intro r
    rw [regs10]
    have e1 : aluEval .add (reg n6 sp) 0xC = B := by
      rw [sp6]; show R + BitVec.ofNat 32 0x10 + BitVec.ofNat 32 0xC = R + BitVec.ofNat 32 0x1C
      rw [add_ofNat_assoc]
    have e2 : aluEval .add (upd (reg n6) a1 (aluEval .add (reg n6 sp) 0xC) x0) 0x40 = BitVec.ofNat 32 64 := by
      simp only [upd, show (x0 : Fin 32).val = 0 from rfl, ite_true]; rfl
    rw [e2, e1, show Z + BitVec.ofNat 32 0x20 + 4 = Z + BitVec.ofNat 32 0x24 from by
      rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]]
  have K10 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ ra → reg n10 r = reg n1 r := fun r q1 q2 q3 => by
    rw [r10]; simp only [upd, q1, q2, q3, ite_false]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp; exact (K6' 0 (by decide) (by decide)).trans u1'.zero |>.symm
    · simp [h0, K6' r q1 q2]
  have pc10' : n10.pc = BitVec.ofNat 32 memcpyStubAddress := by
    rw [pc10, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
    decide
  have sp10 : reg n10 sp = R + BitVec.ofNat 32 0x10 := by
    rw [K10 sp (by decide) (by decide) (by decide), sp1]
  have eF : R + BitVec.ofNat 32 0x10 + 0xFFFFFFF0 = R := by
    rw [BitVec.add_assoc]; exact BitVec.add_zero R
  obtain ⟨n11, c11, pc11, sp11, a011, mem11, K11⟩ := memcpy_correct n10 (BitVec.ofNat 32 memcpyStubAddress)
    (Z + BitVec.ofNat 32 0x24) d B 64
    (fun i hi => by
      show n10.mem _ = _; rw [mem10]
      exact ((cM1 _ _ hMS (by decide) (by decide)).fillBytes (hBs _ _ (by decide) (by decide)) (Nat.le_refl 64)) i hi)
    (by decide) pc10'
    (by rw [K10 a0 (by decide) (by decide) (by decide), K1 a0 (by decide), ha0])
    (by rw [r10]; simp +decide [upd])
    (by rw [r10]; simp +decide [upd])
    (by rw [r10]; simp +decide [upd]) (by decide)
    (by
      rw [mem10, sp10, eF]
      exact { code := (cM1 _ _ hMB (by decide) (by decide)).fillBytes (hBs _ _ (by decide) (by decide))
                (Nat.le_refl 64)
              hDC := dc _ _ _ _ hdw (by decide) (by decide)
              hFC := dc _ _ _ _ (by omega) (by decide) (by decide)
              hdF := by have h := hdT.subR (c := 0) (l := 16) (by omega); rwa [add_ofNat_zero] at h
              hsF := by
                have h := sep_offsets R (c := 0x1C) (n := 64) (d := 0) (k := 16) (Or.inr (by omega)) (by omega)
                  (by omega)
                rwa [add_ofNat_zero] at h
              hsep := hdT.subR (c := 0x1C) (l := 64) (by omega)
              hF := by rw [hRn]; omega
              hFw := by omega
              hdw := by omega
              hsw := by rw [hRc _ (by omega)]; omega })
  rw [sp10, eF, mem10] at mem11
  let MA := n11.mem
  have mA : ∀ x, Sep R 16 x 1 → MA x = copyBytes Mf d B 64 x := mem11
  have cA : ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn MA b code := fun b code h hb hbl i hi => by
    rw [mA _ ((dc R 16 b code.length (by omega) hb hbl).subR (c := i) (l := 1) (by omega)),
      copyBytes_sep ((dc d 64 b code.length hdw hb hbl).subR (c := i) (l := 1) (by omega)) (Nat.le_refl 64)]
    exact (cM1 _ _ h hb hbl).fillBytes (hBs _ _ hb hbl) (Nat.le_refl 64) i hi
  have hcA := cA _ _ hc (by decide) (by decide)
  have u11 : St MA Z n11 0x24 (reg n11) := ⟨by rw [pc11], rfl, fun _ => rfl⟩
  have sp11' : reg n11 sp = R + BitVec.ofNat 32 0x10 := by rw [sp11, sp10]
  obtain ⟨n12, d12, u12⟩ := u11.lw hcA za64_at_24 (off' := 0x26) (by decide)
    (by rw [sp11', show (0x4C : Word) = BitVec.ofNat 32 0x4C from rfl, add_ofNat_assoc, hRc _ (by omega)]; have := hTa; omega)
  have slot : memLoad32 MA (reg n11 sp + 0x4C) = retAddr := by
    rw [sp11', show (0x4C : Word) = BitVec.ofNat 32 0x4C from rfl, add_ofNat_assoc, ← memLoad32_store32_same M0 (R + BitVec.ofNat 32 (0x10 + 0x4C)) retAddr]
    apply memLoad32_congr; intro j hj
    rw [add_ofNat_assoc]
    have hx1 : Sep R 16 (R + BitVec.ofNat 32 (0x10 + 0x4C + j)) 1 :=
      sep_offsets R (c := 0) (n := 16) (d := 0x10 + 0x4C + j) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
        |> fun h => by rwa [add_ofNat_zero] at h
    rw [mA _ hx1, copyBytes_sep ((hdT.subR (c := 0x10 + 0x4C + j) (l := 1) (by omega))) (Nat.le_refl 64)]
    show fillBytes M1 B 0 64 _ = _
    exact fillBytes_sep (sep_offsets R (c := 0x1C) (n := 64) (d := 0x10 + 0x4C + j) (k := 1) (Or.inl (by omega))
      (by omega) (by omega)) (Nat.le_refl 64)
  rw [slot] at u12
  have K12 := u12.upd_ne u11.zero
  have u12' : St MA Z n12 0x26 (reg n12) := u12.self
  obtain ⟨n13, d13, u13⟩ := u12'.aluImm hcA za64_at_26 (off' := 0x28) (by decide)
  have K13 := u13.upd_ne u12'.zero
  have u13' : St MA Z n13 0x28 (reg n13) := u13.self
  obtain ⟨n14, d14, pc14, mem14, regs14⟩ := u13'.jalr hcA za64_at_28
  have ra13 : reg n13 ra = retAddr := by rw [K13 ra (by decide), u12.upd_eq (by decide)]
  have sp13 : reg n13 sp = T := by
    rw [u13.upd_eq (by decide), K12 sp (by decide), sp11']
    show R + BitVec.ofNat 32 0x10 + 0x50 = T
    rw [BitVec.add_assoc]; show T + 0xFFFFFFA0 + (BitVec.ofNat 32 0x10 + 0x50) = T
    rw [BitVec.add_assoc]; exact BitVec.add_zero T
  have k11 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg n11 r = reg n10 r := K11
  refine ⟨n14, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (c6.trans (.cons d7 (.cons d8 (.cons d9
    (.cons d10 (c11.trans (.cons d12 (.cons d13 (.single d14))))))))))))), ?_, ?_,
    fun r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 => ?_, fun x hx => ?_⟩
  · rw [pc14, ra13, add_lit_zero, hret]
  · rw [regs14, sp13]
  · rw [regs14]
    by_cases hra' : r = ra
    · subst hra'; rw [ra13, hra]
    by_cases hsp' : r = sp
    · subst hsp'; rw [sp13, hsp]
    rw [K13 r hsp', K12 r hra', k11 r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 hsp', K10 r q11 q12 hra',
      K1 r hsp']
  · rw [mem14]
    show MA x = _
    rw [mA x (hx.sub (c := 0) (l := 16) (by omega) |> fun h => by rwa [add_ofNat_zero] at h)]
    unfold copyBytes fillBytes
    by_cases hin : (x - d).toNat < 64
    · rw [ite_eq_left hin, ite_eq_left hin]
      show fillBytes M1 B 0 64 _ = _
      unfold fillBytes
      rw [BitVec.add_comm B, BitVec.add_sub_cancel, ite_eq_left hin]
    · rw [ite_eq_right hin, ite_eq_right hin]
      show fillBytes M1 B 0 64 x = M0 x
      rw [fillBytes_sep (hx.sub (c := 0x1C) (l := 64) (by omega)) (Nat.le_refl 64)]
      exact memStore32_ne fun i hi e => hx (0x10 + 0x4C + i) (by omega) 0 (by decide)
        (by rw [add_ofNat_zero, ← add_ofNat_assoc]; exact e.symm)


end C3.RV32
