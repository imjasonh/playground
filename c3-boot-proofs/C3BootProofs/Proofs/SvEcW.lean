import C3BootProofs.Proofs.SvEcPt

/-!
# `sigstore::verify`: the P-256 check's wNAF digits

Before computing each scalar's width-5 NAF digits, the check clears a
257-byte buffer one byte at a time. `ec_zloop` proves that loop.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

def ecZ1 : List BInstr := [.sb a0 x0 0x0, .aluImm .add a0 a0 0x1, .aluImm .add a1 a1 0xFFFFFFFF]
theorem ecZ1_end : blockEnd sigstoreVerifyCode 0x184E ecZ1 = some 0x1856 := by decide

set_option maxHeartbeats 4000000 in
/-- **The clearing loop** at 0x184E: with `j` bytes left from frame offset
`c + i`, it zeroes them and leaves at 0x1858. -/
theorem ec_zloop {B : Word} (F : Fr B 0x3830) {c N : Nat} (hN : c + N ≤ 0x1690) :
    ∀ j i {m : Machine} {Mx : Word → BitVec 8}, i + j = N → 0 < j → CodeIn Mx SV sigstoreVerifyCode →
      St Mx SV m 0x184E (reg m) → reg m a0 = B + 0x21A0 + BitVec.ofNat 32 (c + i) → reg m a1 = BitVec.ofNat 32 j →
      ∃ m' Mx', Steps m m' ∧ St Mx' SV m' 0x1858 (reg m') ∧ CodeIn Mx' SV sigstoreVerifyCode ∧
        (∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg m' q = reg m q) ∧
        (∀ t, t < j → Mx' (B + 0x21A0 + BitVec.ofNat 32 (c + i + t)) = 0) ∧
        (∀ x, Sep (B + 0x21A0 + BitVec.ofNat 32 (c + i)) j x 1 → Mx' x = Mx x) := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  intro j
  induction j with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ j ih =>
    intro i m Mx hij _ hc st h0 h1
    have hz := st.zero
    have hsc : Sep (B + 0x21A0 + BitVec.ofNat 32 (c + i)) 1 SV sigstoreVerifyCode.length :=
      FS.sepHi (by omega) (by decide) (by decide)
    obtain ⟨m1, c1, u1⟩ := st.block ecZ1 hc ecZ1_end (by
      simp +decide only [BlockOk, BInstr.ok, ecZ1, and_true]
      rw [h0, show (0x0 : Word) = BitVec.ofNat 32 0 from rfl, add_ofNat_zero]; exact hsc)
    have M1 : (runBlock ecZ1 (Mx, reg m)).1 = memStore8 Mx (B + 0x21A0 + BitVec.ofNat 32 (c + i)) 0 := by
      simp +decide only [runBlock, BInstr.run, ecZ1, upd, ↓reduceIte]
      rw [h0, hz, show (0x0 : Word) = BitVec.ofNat 32 0 from rfl, add_ofNat_zero]; rfl
    have C1 : CodeIn (runBlock ecZ1 (Mx, reg m)).1 SV sigstoreVerifyCode := by rw [M1]; exact hc.store8 hsc
    have s1 : St (runBlock ecZ1 (Mx, reg m)).1 SV m1 0x1856 (reg m1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
    have r1a0 : reg m1 a0 = B + 0x21A0 + BitVec.ofNat 32 (c + (i + 1)) := by
      rw [u1.regs]; simp +decide only [runBlock, BInstr.run, ecZ1, upd, ↓reduceIte, aluEval]
      rw [h0, show (0x1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc, show c + i + 1 = c + (i + 1) by omega]
    have r1a1 : reg m1 a1 = BitVec.ofNat 32 j := by
      rw [u1.regs]; simp +decide only [runBlock, BInstr.run, ecZ1, upd, ↓reduceIte, aluEval]
      rw [h1]; exact ofNat_pred j
    have k1 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg m1 q = reg m q := fun q h0' h1' => by
      have hq : q ∉ ecZ1.filterMap BInstr.dst := by
        simp only [ecZ1, List.filterMap_cons, List.filterMap_nil, BInstr.dst, Option.some, List.mem_cons, List.mem_nil_iff,
          or_false, not_or]; exact ⟨h0', h1'⟩
      rw [u1.regs, runBlock_reg _ _ _ q hz hq]
    have fr1 : ∀ x, x ≠ B + 0x21A0 + BitVec.ofNat 32 (c + i) → (runBlock ecZ1 (Mx, reg m)).1 x = Mx x :=
      fun x hx => by rw [M1, memStore8_ne hx]
    have z1 : (runBlock ecZ1 (Mx, reg m)).1 (B + 0x21A0 + BitVec.ofNat 32 (c + i)) = 0 := by
      rw [M1, memStore8_same]
    by_cases hj : j = 0
    · subst hj
      obtain ⟨m2, d2, u2⟩ := s1.notTaken C1 0x1858 sv_at_1856 (by decide)
        (by show (reg m1 a1 != reg m1 x0) = false; rw [r1a1, s1.zero]; rfl)
      refine ⟨m2, _, c1.trans (.single d2), u2.self, C1, fun q h0' h1' => by rw [u2.regs, k1 q h0' h1'],
        fun t ht => by obtain rfl : t = 0 := by omega
                       exact z1, fun x hx => fr1 x fun e => ?_⟩
      have := hx 0 (by decide) 0 (by decide); rw [add_ofNat_zero, add_ofNat_zero] at this; exact this e.symm
    · have hne : reg m1 a1 ≠ 0 := by
        rw [r1a1]; intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show (0 : Word).toNat = 0 from rfl] at this
        exact hj this
      obtain ⟨m2, d2, u2⟩ := s1.taken C1 0x184E sv_at_1856 (by decide)
        (by show (reg m1 a1 != reg m1 x0) = true; rw [s1.zero, bne_iff_ne]; exact hne)
      obtain ⟨m3, M3, c3, s3, C3, k3, z3, f3⟩ := ih (i + 1) (by omega) (Nat.pos_of_ne_zero hj) C1 u2.self
        (by rw [u2.regs, r1a0]) (by rw [u2.regs, r1a1])
      refine ⟨m3, M3, c1.trans (.cons d2 c3), s3, C3, fun q h0' h1' => by rw [k3 q h0' h1', u2.regs, k1 q h0' h1'],
        fun t ht => ?_, fun x hx => ?_⟩
      · rcases t with _ | t
        · rw [Nat.add_zero, f3 _ (sepS (B + 0x21A0) (c := c + (i + 1)) (n := j) (d := c + i) (k := 1)
            (Or.inr (by omega)) (by omega) (by omega)), z1]
        · rw [show c + i + (t + 1) = c + (i + 1) + t by omega]; exact z3 t (by omega)
      · rw [f3 x (hx.sub (c := 1) (l := j) (by omega) |> fun h => by
            rw [add_ofNat_assoc, show c + i + 1 = c + (i + 1) by omega] at h; exact h)]
        exact fr1 x fun e => by
          have := hx 0 (by omega) 0 (by decide); rw [add_ofNat_zero, add_ofNat_zero] at this; exact this e.symm

end C3.RV32.Sv
