import C3BootProofs.Proofs.Ed25519VerifyP6b

/-!
# `ed25519_verify`, offsets 0x16CC to 0x189C: the passes of the loop

`ladder` is the loop over the digit indices from `i` down to 0, and
`ev_ladder` runs the compiled loop from its head to its exit.
-/

namespace C3.RV32

open C3.Image

theorem nafGo_range (X : Nat) : ∀ (n pos carry : Nat) (nf : Nat → BitVec 8), carry ≤ 1 →
    (∀ k, (nf k).toNat ≤ 15 ∨ 241 ≤ (nf k).toNat) →
    ∀ k, (nafGo X n pos carry nf k).toNat ≤ 15 ∨ 241 ≤ (nafGo X n pos carry nf k).toNat := by
  intro n
  induction n with
  | zero => intro _ _ _ _ hnf; exact hnf
  | succ n ih =>
    intro pos carry nf hc hnf
    simp only [nafGo]
    split
    · exact hnf
    · split
      · exact ih _ _ _ hc hnf
      · rename_i hodd
        refine ih _ _ _ ?_ ?_
        · split
          · exact Nat.zero_le _
          · exact Nat.le_refl _
        · intro k
          split
          · split
            · rename_i hlt
              left; rw [BitVec.toNat_ofNat]; omega
            · rename_i hge
              right
              have hw : X / 2 ^ pos % 32 < 32 := Nat.mod_lt _ (by decide)
              rw [BitVec.toNat_ofNat]; omega
          · exact hnf k

/-- Each NAF digit is a byte between -15 and 15. -/
theorem nafSpec_range (X k : Nat) : (nafSpec X k).toNat ≤ 15 ∨ 241 ≤ (nafSpec X k).toNat :=
  nafGo_range X 256 0 0 _ (Nat.zero_le _) (fun _ => Or.inl (by decide)) k

/-- `as_projective` of a completed point. -/
def projC (p : Pt) : List Nat × List Nat × List Nat :=
  (mulL p.1 p.2.2.2, mulL p.2.1 p.2.2.1, mulL p.2.2.1 p.2.2.2)

/-- One pass: double `r`, then take the two digits' steps. -/
def ladStep (TA TB : Nat → Pt) (a b : BitVec 8) (r : List Nat × List Nat × List Nat) :
    List Nat × List Nat × List Nat :=
  projC (digStep TB b (digStep TA a (edDoubleSpec r.1 r.2.1 r.2.2)))

/-- The passes for digit indices `k - 1` down to 0. -/
def ladder (TA TB : Nat → Pt) (aN bN : Nat → BitVec 8) :
    Nat → List Nat × List Nat × List Nat → List Nat × List Nat × List Nat
  | 0, r => r
  | k + 1, r => ladder TA TB aN bN k (ladStep TA TB (aN k) (bN k) r)

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- One pass of the loop, from its head at 0x16CC to the exit test at 0x1890. -/
theorem ev_body (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x16CC)
    {TA TB : Nat → Pt} {a b : BitVec 8} {i : Nat} (hi : i < 256)
    (h9 : reg n 9 = F + BitVec.ofNat 32 (0x7F0 + i)) (h21 : reg n 21 = F + BitVec.ofNat 32 (0x8F0 + i))
    (h22 : reg n 22 = 1) (hA : M (F + BitVec.ofNat 32 (0x7F0 + i)) = a) (hB : M (F + BitVec.ofNat 32 (0x8F0 + i)) = b)
    (ha : a.toNat ≤ 15 ∨ 241 ≤ a.toNat) (hb : b.toNat ≤ 15 ∨ 241 ≤ b.toNat)
    (hTA : ∀ j, j < 8 → ptAt M (F + BitVec.ofNat 32 (0x9F0 + 160 * j)) = TA j)
    (hTB : ∀ j, j < 8 → ptAt M (F + BitVec.ofNat 32 (0xEF0 + 160 * j)) = TB j) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x1890 ∧ (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → reg n' q = reg n q) ∧
      prAt M' (F + BitVec.ofNat 32 0x13F0) = ladStep TA TB a b (prAt M (F + BitVec.ofNat 32 0x13F0)) ∧
      ∀ c, c < 0x16A0 → (c < 0x13F0 ∨ 0x1648 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x16DC)
    ((.lui a0 0x1000) :: (.aluImm .add a0 a0 0x468) :: (.alu .add a0 a0 sp) :: (.lui a1 0x1000) ::
      (.aluImm .add a1 a1 0x3F0) :: (.alu .add a1 a1 sp) :: [])
    (blockEnd_cons' (off' := 0x16CE) ev_at_16cc rfl (blockEnd_cons' (off' := 0x16D2) ev_at_16ce rfl
      (blockEnd_cons' (off' := 0x16D4) ev_at_16d2 rfl (blockEnd_cons' (off' := 0x16D6) ev_at_16d4 rfl
      (blockEnd_cons' (off' := 0x16DA) ev_at_16d6 rfl (blockEnd_cons' (off' := 0x16DC) ev_at_16da rfl rfl))))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have k1 : ∀ q : Fin 32, q.val ∈ evKeep → reg n1 q = reg n q := fun q hq => by
    rw [hr1, evb_reg q D.st.zero (by revert hq; revert q; decide)]
  obtain ⟨n2, c2, D2, k2, w2, f2⟩ := D1.dbl C (d := 0x1468) (e := 0x13F0) ev_at_16dc ev_at_16e0 (by decide) (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; exact BitVec.add_comm _ _)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; exact BitVec.add_comm _ _)
    (by decide) (by decide) (by decide) (by decide)
  have g2 : ∀ c, c < 0x16A0 → (c < 0x1468 ∨ 0x1508 ≤ c) → n2.mem (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
    fun c hc hh => by
      rcases hh with hh | hh
      · exact f2 _ (C.zF (by omega)) (C.offs (Or.inr (by omega)) (by decide) (by omega))
      · exact f2 _ (C.zF (by omega)) (C.offs (Or.inl (by omega)) (by decide) (by omega))
  obtain ⟨n3, M3, c3, D3, k3, w3, f3⟩ := ev_digA C D2 (T := TA) (p := 0x7F0 + i)
    (by rw [k2 9 (by decide), k1 9 (by decide), h9]) (by omega)
    (by rw [g2 _ (by omega) (Or.inl (by omega)), hA]) ha
    (by rw [k2 22 (by decide), k1 22 (by decide), h22])
    (fun j hj => by
      rw [ptB (M := M) (c := 0x9F0 + 160 * j) (e := 0x9F0 + 160 * j) fun x hx => g2 _ (by omega) (Or.inl (by omega))]
      exact hTA j hj)
  obtain ⟨n4, M4, c4, D4, k4, w4, f4⟩ := ev_digB C D3 (T := TB) (p := 0x8F0 + i)
    (by rw [k3 21 (by decide) (by decide), k2 21 (by decide), k1 21 (by decide), h21]) (by omega)
    (by rw [f3 _ (by omega) (Or.inl (by omega)), g2 _ (by omega) (Or.inl (by omega)), hB]) hb
    (by rw [k3 22 (by decide) (by decide), k2 22 (by decide), k1 22 (by decide), h22])
    (fun j hj => by
      rw [ptB (M := M) (c := 0xEF0 + 160 * j) (e := 0xEF0 + 160 * j) fun x hx => by
        rw [f3 _ (by omega) (Or.inl (by omega)), g2 _ (by omega) (Or.inl (by omega))]]
      exact hTB j hj)
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x1888)
    ((.lui a0 0x1000) :: (.aluImm .add a0 a0 0x3F0) :: (.alu .add a0 a0 sp) :: (.lui a1 0x1000) ::
      (.aluImm .add a1 a1 0x468) :: (.alu .add a1 a1 sp) :: [])
    (blockEnd_cons' (off' := 0x187A) ev_at_1878 rfl (blockEnd_cons' (off' := 0x187E) ev_at_187a rfl
      (blockEnd_cons' (off' := 0x1880) ev_at_187e rfl (blockEnd_cons' (off' := 0x1882) ev_at_1880 rfl
      (blockEnd_cons' (off' := 0x1886) ev_at_1882 rfl (blockEnd_cons' (off' := 0x1888) ev_at_1886 rfl rfl))))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n6, c6, D6, k6, w6, f6⟩ := D5.ap C (d := 0x13F0) (e := 0x1468) ev_at_1888 ev_at_188c (by decide) (by decide)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; exact BitVec.add_comm _ _)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; exact BitVec.add_comm _ _)
    (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
  refine ⟨n6, n6.mem, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))), D6, fun q hq h8 => ?_, ?_,
    fun c hc hh => ?_⟩
  · rw [k6 q hq, hr5, evb_reg q D4.st.zero (by revert hq; revert q; decide), k4 q hq h8, k3 q hq h8, k2 q hq, k1 q hq]
  · rw [w6, w4, w3, w2]; rfl
  · have e6 : n6.mem (F + BitVec.ofNat 32 c) = M4 (F + BitVec.ofNat 32 c) := by
      rcases hh with hh | hh
      · exact f6 _ (C.zF (by omega)) (C.offs (Or.inr (by omega)) (by decide) (by omega))
      · exact f6 _ (C.zF (by omega)) (C.offs (Or.inl (by omega)) (by decide) (by omega))
    rcases hh with hh | hh
    · rw [e6, f4 c hc (Or.inl (by omega)), f3 c hc (Or.inl (by omega)), g2 c hc (Or.inl (by omega))]
    · rw [e6, f4 c hc (Or.inr hh), f3 c hc (Or.inr hh), g2 c hc (Or.inr (by omega))]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **The loop**, from its head at 0x16CC on index `i` to its exit at 0x189C. -/
theorem ev_ladder (C : EvCtx M0 F pk sig msg len) {TA TB : Nat → Pt} {aN bN : Nat → BitVec 8}
    (haR : ∀ k, (aN k).toNat ≤ 15 ∨ 241 ≤ (aN k).toNat) (hbR : ∀ k, (bN k).toNat ≤ 15 ∨ 241 ≤ (bN k).toNat) :
    ∀ i {M : Word → BitVec 8} {n : Machine}, i < 256 → EvSt M0 Ms F r0 M n 0x16CC →
      reg n 9 = F + BitVec.ofNat 32 (0x7F0 + i) → reg n 21 = F + BitVec.ofNat 32 (0x8F0 + i) →
      reg n 20 = 0 - BitVec.ofNat 32 i → reg n 22 = 1 →
      (∀ k, k < 256 → M (F + BitVec.ofNat 32 (0x7F0 + k)) = aN k) →
      (∀ k, k < 256 → M (F + BitVec.ofNat 32 (0x8F0 + k)) = bN k) →
      (∀ j, j < 8 → ptAt M (F + BitVec.ofNat 32 (0x9F0 + 160 * j)) = TA j) →
      (∀ j, j < 8 → ptAt M (F + BitVec.ofNat 32 (0xEF0 + 160 * j)) = TB j) →
      ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x189C ∧
        (∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 9, 20, 21] → reg n' q = reg n q) ∧
        prAt M' (F + BitVec.ofNat 32 0x13F0) = ladder TA TB aN bN (i + 1) (prAt M (F + BitVec.ofNat 32 0x13F0)) ∧
        ∀ c, c < 0x16A0 → (c < 0x13F0 ∨ 0x1648 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c)
  | 0, M, n, hi, D, h9, h21, h20, h22, hA, hB, hTA, hTB => by
    obtain ⟨n1, M1, c1, D1, k1, w1, f1⟩ := ev_body C D hi h9 h21 h22 (hA 0 hi) (hB 0 hi) (haR 0) (hbR 0) hTA hTB
    obtain ⟨n2, d2, u2⟩ := D1.st.taken (D1.code C) 0x189C ev_at_1890 (by decide)
      (by rw [k1 20 (by decide) (by decide), h20, D1.st.zero]; decide)
    refine ⟨n2, M1, c1.trans (Steps.single d2), D1.jmp u2, fun q hq hn => ?_, ?_, f1⟩
    · rw [u2.regs, k1 q hq (by revert hn; revert q; decide)]
    · rw [w1]; rfl
  | i + 1, M, n, hi, D, h9, h21, h20, h22, hA, hB, hTA, hTB => by
    obtain ⟨n1, M1, c1, D1, k1, w1, f1⟩ := ev_body C D hi h9 h21 h22 (hA _ hi) (hB _ hi) (haR _) (hbR _) hTA hTB
    obtain ⟨n2, d2, u2⟩ := D1.st.notTaken (D1.code C) 0x1894 ev_at_1890 (by decide) (by
      rw [k1 20 (by decide) (by decide), h20, D1.st.zero]
      exact beq_eq_false_iff_ne.mpr fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this
        exact absurd this (by omega))
    have D2 := D1.jmp u2
    obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0x189A)
      [.aluImm .add (20 : Fin 32) (20 : Fin 32) 0x1, .aluImm .add (21 : Fin 32) (21 : Fin 32) 0xFFFFFFFF,
        .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]
      (blockEnd_cons' (off' := 0x1896) ev_at_1894 rfl (blockEnd_cons' (off' := 0x1898) ev_at_1896 rfl
        (blockEnd_cons' (off' := 0x189A) ev_at_1898 rfl rfl))) ⟨trivial, trivial, trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n4, d4, u4⟩ := D3.st.jump (D3.code C) ev_at_189a (off' := 0x16CC) (by decide) (by rw [D3.st.pc]; decide)
    have D4 := D3.jmp u4
    have r2 : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → reg n2 q = reg n q := fun q hq h8 => by rw [u2.regs, k1 q hq h8]
    have r4 : ∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 9, 20, 21] → reg n4 q = reg n q := fun q hq hn => by
      rw [u4.regs, hr3, evb_reg q D2.st.zero (by revert hn; revert q; decide), r2 q hq (by revert hn; revert q; decide)]
    have fb : ∀ c, c < 0x13F0 → M1 (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
      fun c hc => f1 c (by omega) (Or.inl hc)
    obtain ⟨n5, M5, c5, D5, k5, w5, f5⟩ := ev_ladder C (TA := TA) (TB := TB) haR hbR i (M := M1) (n := n4) (by omega) D4
      (by
        rw [u4.regs, hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [r2 9 (by decide) (by decide), h9]
        show F + BitVec.ofNat 32 (0x7F0 + (i + 1)) + BitVec.ofNat 32 0xFFFFFFFF = _
        rw [add_ofNat_assoc]
        exact congrArg (fun x => F + x) (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)))
      (by
        rw [u4.regs, hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [r2 21 (by decide) (by decide), h21]
        show F + BitVec.ofNat 32 (0x8F0 + (i + 1)) + BitVec.ofNat 32 0xFFFFFFFF = _
        rw [add_ofNat_assoc]
        exact congrArg (fun x => F + x) (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)))
      (by
        rw [u4.regs, hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [r2 20 (by decide) (by decide), h20]
        apply BitVec.eq_of_toNat_eq
        show (0 - BitVec.ofNat 32 (i + 1) + 1).toNat = _
        rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          show (0 : Word).toNat = 0 from rfl, show (1 : Word).toNat = 1 from rfl]
        omega)
      (by rw [u4.regs, hr3, evb_reg 22 D2.st.zero (by decide), r2 22 (by decide) (by decide), h22])
      (fun k hk => by rw [fb _ (by omega), hA k hk])
      (fun k hk => by rw [fb _ (by omega), hB k hk])
      (fun j hj => by
        rw [ptB (M := M) (c := 0x9F0 + 160 * j) (e := 0x9F0 + 160 * j) fun x hx => fb _ (by omega)]; exact hTA j hj)
      (fun j hj => by
        rw [ptB (M := M) (c := 0xEF0 + 160 * j) (e := 0xEF0 + 160 * j) fun x hx => fb _ (by omega)]; exact hTB j hj)
    refine ⟨n5, M5, c1.trans ((Steps.single d2).trans (c3.trans ((Steps.single d4).trans c5))), D5,
      fun q hq hn => by rw [k5 q hq hn, r4 q hq hn], ?_, fun c hc hh => by rw [f5 c hc hh, f1 c hc hh]⟩
    rw [w5, w1]; rfl

end

end C3.RV32


