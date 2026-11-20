import C3BootProofs.Image.BootloaderData5
import C3BootProofs.Proofs.SvEcMl2

/-!
# `sigstore::verify`: the P-256 check's main loop, from its setup

The setup of the main loop, from 0x18F8: the longer of the two digit counts,
the point at infinity in the accumulator, and the loop's registers. Then the
loop, or the exit at 0x1A72 when both counts are zero. It follows
`Pv384G2.lean`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

/-- `wnafGo` on a number of `L` bits writes at most `L + 1 - pos` digits
from bit `pos`. -/
theorem wnafGo_len {N L : Nat} (hN : N < 2 ^ L) :
    ∀ fuel pos carry, carry ≤ 1 → pos ≤ L → (wnafGo N L fuel pos carry).length ≤ L + 1 - pos := by
  intro fuel
  induction fuel with
  | zero => intro pos carry _ _; simp only [wnafGo, List.length_nil]; exact Nat.zero_le _
  | succ fuel ih =>
    intro pos carry hc hp
    simp only [wnafGo]
    by_cases hlt : pos < L
    · rw [ite_eq_left hlt]
      by_cases he : (carry + N / 2 ^ pos % 32) % 2 = 0
      · rw [ite_eq_left he, List.length_cons]
        have := ih (pos + 1) carry hc hlt
        omega
      · rw [ite_eq_right he]
        have hb : pos + 1 = L → N / 2 ^ pos < 2 := fun h => by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos pos)]
          rw [← h, Nat.pow_succ] at hN; omega
        have hm : N / 2 ^ pos % 32 ≤ N / 2 ^ pos := Nat.mod_le _ _
        by_cases hw : carry + N / 2 ^ pos % 32 < 16
        · simp only [hw, ↓reduceIte, Nat.sub_zero, List.length_append, List.length_cons, List.length_replicate]
          have := ih (pos + min 5 (L - pos)) 0 (Nat.zero_le _) (by omega)
          omega
        · have hne : pos + 1 ≠ L := fun h => hw (by have := hb h; omega)
          simp only [hw, ↓reduceIte, List.length_append, List.length_cons, List.length_replicate]
          have := ih (pos + min 5 (L - 1 - pos)) 1 (Nat.le_refl _) (by omega)
          omega
    · rw [ite_eq_right hlt]
      split
      · simp only [List.length_nil]; exact Nat.zero_le _
      · simp only [List.length_cons, List.length_nil]; omega

/-- The point at infinity, as the image keeps it, in Montgomery form. -/
def idPt2 : Pt2 :=
  (dataVal p256IdentityData 0 8, dataVal p256IdentityData 0x20 8, dataVal p256IdentityData 0x40 8)

set_option exponentiation.threshold 600 in
theorem idPt2_lt : Pt2Lt idPt2 := by unfold idPt2 Pt2Lt p256; decide

/-- The main loop from the point at infinity over `L` positions. -/
def mlMain2 (T0 T1 : Nat → Pt2) (D0 D1 : List Nat) (L : Nat) : Option (Pt2 × Bool) :=
  mlLoop2 T0 T1 D0 D1 L (idPt2, false)

def mlS0 : List BInstr := [.aluImm .add a1 x0 0x0, .aluImm .and a1 a1 0x1]
theorem mlS0_end : blockEnd sigstoreVerifyCode 0x18F8 mlS0 = some 0x18FC := by decide
def mlS1 : List BInstr := [.alu .add (9 : Fin 32) x0 a0]
theorem mlS1_end : blockEnd sigstoreVerifyCode 0x1902 mlS1 = some 0x1904 := by decide
def mlS2 : List BInstr := [.aluImm .add a1 x0 0x1]
theorem mlS2_end : blockEnd sigstoreVerifyCode 0x1904 mlS2 = some 0x1906 := by decide
def mlS3 : List BInstr := [.aluImm .and a1 a1 0x1]
theorem mlS3_end : blockEnd sigstoreVerifyCode 0x18FA mlS3 = some 0x18FC := by decide
def mlS4 : List BInstr := [.lui a1 0x3FCC4000, .aluImm .add a1 a1 0x560, .lui a0 0x1000, .aluImm .add a0 a0 0x480,
  .alu .add a0 a0 sp, .aluImm .add a2 x0 0x60, .aluImm .add (20 : Fin 32) x0 0x60]
theorem mlS4_end : blockEnd sigstoreVerifyCode 0x1918 mlS4 = some 0x1930 := by decide
def mlS5 : List BInstr := [.aluImm .add (8 : Fin 32) x0 0x0, .aluImm .add (21 : Fin 32) sp 0x7FF,
  .aluImm .add (21 : Fin 32) (21 : Fin 32) 0x241, .lui a0 0x1000, .aluImm .add a0 a0 0x20, .alu .add a0 a0 sp,
  .aluImm .add (24 : Fin 32) sp 0x7FF, .aluImm .add (24 : Fin 32) (24 : Fin 32) 0x261, .alu .add a0 a0 (9 : Fin 32),
  .aluImm .add (22 : Fin 32) a0 0x3]
theorem mlS5_end : blockEnd sigstoreVerifyCode 0x1938 mlS5 = some 0x1958 := by decide

theorem s6_val2 (S : Word) (x : Nat) :
    (0x1000 : Word) + 0x20 + S + BitVec.ofNat 32 x + 3 = S + BitVec.ofNat 32 (0x1023 + x) := by
  sv_addr

theorem sp_a40 (S : Word) : S + 0x7FF + 0x241 = S + BitVec.ofNat 32 0xA40 := by
  rw [BitVec.add_assoc]; rfl

theorem sp_a60 (S : Word) : S + 0x7FF + 0x261 = S + BitVec.ofNat 32 0xA60 := by
  rw [BitVec.add_assoc]; rfl

set_option maxHeartbeats 32000000 in
/-- **The setup of the main loop**, from 0x18F8: the longer digit count,
the point at infinity in the accumulator, and the loop's registers; then the
loop head, or the exit when both counts are zero. -/
theorem ml2_pre {B : Word} {T0 T1 : Nat → Pt2} {D0 D1 : List Nat} {L0 L1 : Nat} {m : Machine}
    (F : Fr B 0x3830) (E : MlEnv m.mem) (RS : SvRoSep B)
    (hid : CodeIn m.mem (BitVec.ofNat 32 p256IdentityAddress) p256IdentityData)
    (s : St m.mem SV m 0x18F8 (reg m)) (hsp : reg m sp = B + 0x21A0)
    (h9 : reg m (9 : Fin 32) = BitVec.ofNat 32 L0) (ha0 : reg m a0 = BitVec.ofNat 32 L1)
    (h27 : reg m (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (hL0 : L0 ≤ 0x101) (hL1 : L1 ≤ 0x101) (M : GM2 B m.mem T0 T1 D0 D1) :
    ∃ m', Steps m m' ∧ MlEnv m'.mem ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧ SvKeepL B m.mem m'.mem mlW ∧
      St m'.mem SV m' (if max L0 L1 = 0 then 0x1A72 else 0x195C) (reg m') ∧
      GX2 B m' (reg m (3 : Fin 32)) (reg m (4 : Fin 32)) (reg m (18 : Fin 32)) (reg m (19 : Fin 32))
        (reg m (26 : Fin 32)) ∧
      reg m' (9 : Fin 32) = BitVec.ofNat 32 (max L0 L1) ∧
      reg m' (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x1023 + max L0 L1) ∧
      reg m' (25 : Fin 32) = reg m (25 : Fin 32) ∧ reg m' (8 : Fin 32) = 0 ∧
      GM2 B m'.mem T0 T1 D0 D1 ∧ ptF m'.mem B 0x1480 = idPt2 := by
  have C := E.C.self
  obtain ⟨n1, c1, u1⟩ := s.block mlS0 C mlS0_end ⟨trivial, trivial, trivial⟩
  have s1 : St m.mem SV n1 0x18FC (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q ≠ a1 → reg n1 q = reg m q := fun q h => by
    rw [u1.regs, runBlock_reg _ _ _ q s.zero (by simp [mlS0, BInstr.dst, h])]
  have a11 : reg n1 a1 = 0 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, mlS0, upd, ↓reduceIte, aluEval]; rw [s.zero]; rfl
  obtain ⟨n2, d2, u2⟩ := s1.notTaken C 0x18FE sv_at_18fc (by decide) (by rw [a11, s1.zero]; rfl)
  have s2 : St m.mem SV n2 0x18FE (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have e2 : reg n2 = reg n1 := funext u2.regs
  -- the longer count in s1, then back to 0x18FA and out at 0x1918
  have hmax : ∃ n3, Steps n2 n3 ∧ St m.mem SV n3 0x1904 (reg n3) ∧
      reg n3 (9 : Fin 32) = BitVec.ofNat 32 (max L0 L1) ∧ ∀ q : Fin 32, q ≠ (9 : Fin 32) → reg n3 q = reg n2 q := by
    by_cases hlt : L1 < L0
    · obtain ⟨n3, d3, u3⟩ := s2.taken C 0x1904 sv_at_18fe (by decide)
        (by rw [e2, k1 _ (by decide), ha0, k1 _ (by decide), h9]; simp only [branchTaken]
            rw [Pv.ult_ofNat (by omega) (by omega)]; exact decide_eq_true hlt)
      exact ⟨n3, .single d3, ⟨u3.pc, u3.mem, fun _ => rfl⟩,
        by rw [u3.regs, e2, k1 _ (by decide), h9, Nat.max_eq_left (by omega)], fun q _ => u3.regs q⟩
    · obtain ⟨n3, d3, u3⟩ := s2.notTaken C 0x1902 sv_at_18fe (by decide)
        (by rw [e2, k1 _ (by decide), ha0, k1 _ (by decide), h9]; simp only [branchTaken]
            rw [Pv.ult_ofNat (by omega) (by omega)]; exact decide_eq_false hlt)
      have s3 : St m.mem SV n3 0x1902 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
      obtain ⟨n4, c4, u4⟩ := s3.block mlS1 C mlS1_end ⟨trivial, trivial⟩
      refine ⟨n4, .cons d3 c4, ⟨u4.pc, u4.mem, fun _ => rfl⟩, ?_, fun q h => ?_⟩
      · rw [u4.regs]; simp +decide only [runBlock, BInstr.run, mlS1, upd, ↓reduceIte, aluEval]
        rw [s3.zero, u3.regs, e2, k1 _ (by decide), ha0, Nat.max_eq_right (by omega)]; exact BitVec.zero_add _
      · rw [u4.regs, runBlock_reg _ _ _ q s3.zero (by simp [mlS1, BInstr.dst, h]), u3.regs]
  obtain ⟨n3, c3, s3, r93, k3⟩ := hmax
  obtain ⟨n4, c4, u4⟩ := s3.block mlS2 C mlS2_end ⟨trivial, trivial⟩
  have s4 : St m.mem SV n4 0x1906 (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
  obtain ⟨n5, d5, u5⟩ := s4.jump C sv_at_1906 (off' := 0x18FA) (by decide) (by rw [s4.pc]; decide)
  have s5 : St m.mem SV n5 0x18FA (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
  obtain ⟨n6, c6, u6⟩ := s5.block mlS3 C mlS3_end ⟨trivial, trivial⟩
  have s6 : St m.mem SV n6 0x18FC (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
  have a16 : reg n6 a1 = 1 := by
    rw [u6.regs]; simp +decide only [runBlock, BInstr.run, mlS3, upd, ↓reduceIte, aluEval]
    rw [u5.regs, u4.regs]; simp +decide only [runBlock, BInstr.run, mlS2, upd, ↓reduceIte, aluEval]
    rw [s3.zero]; rfl
  have k6 : ∀ q : Fin 32, q ≠ a1 → reg n6 q = reg n3 q := fun q h => by
    rw [u6.regs, runBlock_reg _ _ _ q s5.zero (by simp [mlS3, BInstr.dst, h]), u5.regs, u4.regs,
      runBlock_reg _ _ _ q s3.zero (by simp [mlS2, BInstr.dst, h])]
  obtain ⟨n7, d7, u7⟩ := s6.taken C 0x1918 sv_at_18fc (by decide) (by rw [a16, s6.zero]; decide)
  have s7 : St m.mem SV n7 0x1918 (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
  have k7 : ∀ q : Fin 32, q ≠ a1 → q ≠ (9 : Fin 32) → reg n7 q = reg m q := fun q h1 h9 => by
    rw [u7.regs, k6 q h1, k3 q h9, e2, k1 q h1]
  have r97 : reg n7 (9 : Fin 32) = BitVec.ofNat 32 (max L0 L1) := by rw [u7.regs, k6 _ (by decide), r93]
  -- the point at infinity into the accumulator
  obtain ⟨n8, c8, u8⟩ := s7.block mlS4 C mlS4_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m8 : n8.mem = m.mem := u8.mem
  have s8 : St n8.mem SV n8 0x1930 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have k8 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (20 : Fin 32) → reg n8 q = reg n7 q :=
    fun q h0 h1 h2 h20 => by rw [u8.regs, runBlock_reg _ _ _ q s7.zero (by simp [mlS4, BInstr.dst, h0, h1, h2, h20])]
  have sp7 : reg n7 sp = B + 0x21A0 := by rw [k7 _ (by decide) (by decide), hsp]
  have sp8 : reg n8 sp = B + 0x21A0 := by rw [k8 _ (by decide) (by decide) (by decide) (by decide), sp7]
  have a08 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [u8.regs]; simp +decide only [runBlock, BInstr.run, mlS4, upd, ↓reduceIte, aluEval]; rw [sp7]
    exact sp_1480 _
  have a18 : reg n8 a1 = BitVec.ofNat 32 p256IdentityAddress := by
    rw [u8.regs]; simp +decide only [runBlock, BInstr.run, mlS4, upd, ↓reduceIte, aluEval]; try decide
  have a28 : reg n8 a2 = BitVec.ofNat 32 0x60 := by
    rw [u8.regs]; simp +decide only [runBlock, BInstr.run, mlS4, upd, ↓reduceIte, aluEval]; try rw [s7.zero]; try rfl
  have r208 : reg n8 (20 : Fin 32) = 0x60 := by
    rw [u8.regs]; simp +decide only [runBlock, BInstr.run, mlS4, upd, ↓reduceIte, aluEval]; try rw [s7.zero]; try rfl
  have E8 : MlEnv n8.mem := by rw [m8]; exact E
  obtain ⟨n9, P9, K9, X9⟩ := sv_mcRo2 (c := 0x1480) (N := 0x60) F RS E8.C s8 sv_at_1930 sv_at_1934
    (by decide) (by decide) sp8 a08 a18 a28 (by decide) (.inr ⟨by decide, by decide⟩)
  have E9 : MlEnv n9.mem := E8.fr F P9.fr
  have hid8 : CodeIn n8.mem (BitVec.ofNat 32 p256IdentityAddress) p256IdentityData := by rw [m8]; exact hid
  have hA : ptF n9.mem B 0x1480 = idPt2 := by
    unfold ptF idPt2
    rw [accV_KD (M := n8.mem) (K := BitVec.ofNat 32 p256IdentityAddress) (d := 0) 8 fun q hq => by
        have := X9 q (by omega); rwa [Nat.zero_add],
      code_accV hid8 0 8 (by decide),
      accV_KD (M := n8.mem) (K := BitVec.ofNat 32 p256IdentityAddress) (d := 0x20) 8 fun q hq => by
        have := X9 (0x20 + q) (by omega)
        rwa [show 0x1480 + (0x20 + q) = 0x1480 + 0x20 + q by omega] at this,
      code_accV hid8 0x20 8 (by decide),
      accV_KD (M := n8.mem) (K := BitVec.ofNat 32 p256IdentityAddress) (d := 0x40) 8 fun q hq => by
        have := X9 (0x40 + q) (by omega)
        rwa [show 0x1480 + (0x40 + q) = 0x1480 + 0x40 + q by omega] at this,
      code_accV hid8 0x40 8 (by decide)]
  have K9' : SvKeepL B m.mem n9.mem mlW := by
    rw [← m8]; exact (SvKeepL.of K9).wider (mlW_dup fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; simp [mlW])
  -- the loop's registers
  obtain ⟨n10, c10, u10⟩ := P9.st.block mlS5 E9.C.self mlS5_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0x1958 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have z9 := P9.st.zero
  have k10 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 18, 19, 20, 25, 26, 27] → reg n10 q = reg n9 q := fun q hq => by
    rw [u10.regs, runBlock_reg _ _ _ q z9 (by revert hq; revert q; decide)]
  have rm : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 25, 26, 27] → reg n10 q = reg m q := fun q hq => by
    rw [k10 q (by revert hq; revert q; decide), P9.regs q (by revert hq; revert q; decide),
      k8 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide),
      k7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  have r99 : reg n9 (9 : Fin 32) = BitVec.ofNat 32 (max L0 L1) := by
    rw [P9.regs _ (by decide), k8 _ (by decide) (by decide) (by decide) (by decide), r97]
  have sp9 : reg n9 sp = B + 0x21A0 := by rw [P9.regs _ (by decide), sp8]
  have r910 : reg n10 (9 : Fin 32) = BitVec.ofNat 32 (max L0 L1) := by rw [k10 _ (by decide), r99]
  have X10 : GX2 B n10 (reg m (3 : Fin 32)) (reg m (4 : Fin 32)) (reg m (18 : Fin 32)) (reg m (19 : Fin 32))
      (reg m (26 : Fin 32)) := by
    refine ⟨by rw [rm sp (by decide), hsp], rm _ (by decide), rm _ (by decide), rm _ (by decide), rm _ (by decide),
      by rw [k10 _ (by decide), P9.regs _ (by decide), r208], ?_, ?_, rm _ (by decide), by rw [rm _ (by decide), h27]⟩
    · rw [u10.regs]; simp +decide only [runBlock, BInstr.run, mlS5, upd, ↓reduceIte, aluEval]; rw [sp9]
      exact sp_a40 _
    · rw [u10.regs]; simp +decide only [runBlock, BInstr.run, mlS5, upd, ↓reduceIte, aluEval]; rw [sp9]
      exact sp_a60 _
  have r2210 : reg n10 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 (0x1023 + max L0 L1) := by
    rw [u10.regs]; simp +decide only [runBlock, BInstr.run, mlS5, upd, ↓reduceIte, aluEval]; rw [sp9, r99]
    exact s6_val2 _ _
  have r810 : reg n10 (8 : Fin 32) = 0 := by
    rw [u10.regs]; simp +decide only [runBlock, BInstr.run, mlS5, upd, ↓reduceIte, aluEval]; try rw [z9]; try rfl
  have st : Steps m n10 := c1.trans (.cons d2 (c3.trans (c4.trans (.cons d5 (c6.trans (.cons d7 (c8.trans
    (P9.steps.trans c10))))))))
  have E10 : MlEnv n10.mem := by rw [m10]; exact E9
  have fr : ∀ x, SvR B x → n10.mem x = m.mem x := fun x hx => by rw [m10, P9.fr x hx, m8]
  have K10 : SvKeepL B m.mem n10.mem mlW := by rw [m10]; exact K9'
  have M10 : GM2 B n10.mem T0 T1 D0 D1 := M.keep K10
  have A10 : ptF n10.mem B 0x1480 = idPt2 := by rw [m10]; exact hA
  by_cases h0 : max L0 L1 = 0
  · obtain ⟨n11, d11, u11⟩ := s10.taken E10.C.self 0x1A72 sv_at_1958 (by decide) (by rw [r910, h0, s10.zero]; rfl)
    rw [ite_eq_left h0]
    exact ⟨n11, st.trans (.single d11), by rw [u11.mem]; exact E10, fun x hx => by rw [u11.mem, fr x hx],
      by rw [u11.mem]; exact K10, ⟨u11.pc, rfl, fun _ => rfl⟩, X10.of fun q _ => u11.regs q, by rw [u11.regs, r910],
      by rw [u11.regs, r2210], by rw [u11.regs, rm _ (by decide)], by rw [u11.regs, r810],
      by rw [u11.mem]; exact M10, by rw [u11.mem]; exact A10⟩
  · obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.C.self 0x195C sv_at_1958 (by decide)
      (by rw [r910, s10.zero]; exact br_beq_f (Pv.ofNat_ne0 (by omega) (by omega)))
    rw [ite_eq_right h0]
    exact ⟨n11, st.trans (.single d11), by rw [u11.mem]; exact E10, fun x hx => by rw [u11.mem, fr x hx],
      by rw [u11.mem]; exact K10, ⟨u11.pc, rfl, fun _ => rfl⟩, X10.of fun q _ => u11.regs q, by rw [u11.regs, r910],
      by rw [u11.regs, r2210], by rw [u11.regs, rm _ (by decide)], by rw [u11.regs, r810],
      by rw [u11.mem]; exact M10, by rw [u11.mem]; exact A10⟩

set_option maxHeartbeats 16000000 in
/-- **The main loop with its setup**, from 0x18F8 to 0x1A72: `mlMain2`
over the longer digit count. -/
theorem ml2_main {B : Word} {T0 T1 : Nat → Pt2} {D0 D1 : List Nat} {L0 L1 : Nat} {m : Machine}
    (F : Fr B 0x3830) (E : MlEnv m.mem) (RS : SvRoSep B)
    (hid : CodeIn m.mem (BitVec.ofNat 32 p256IdentityAddress) p256IdentityData)
    (s : St m.mem SV m 0x18F8 (reg m)) (hsp : reg m sp = B + 0x21A0)
    (h9 : reg m (9 : Fin 32) = BitVec.ofNat 32 L0) (ha0 : reg m a0 = BitVec.ofNat 32 L1)
    (h27 : reg m (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (hL0 : L0 ≤ 0x101) (hL1 : L1 ≤ 0x101) (M : GM2 B m.mem T0 T1 D0 D1) :
    (mlMain2 T0 T1 D0 D1 (max L0 L1) = none ∧ Panics m) ∨
    (∃ st, mlMain2 T0 T1 D0 D1 (max L0 L1) = some st ∧
      ∃ m', Steps m m' ∧ MlEnv m'.mem ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧ SvKeepL B m.mem m'.mem mlW ∧
        St m'.mem SV m' 0x1A72 (reg m') ∧
        GX2 B m' (reg m (3 : Fin 32)) (reg m (4 : Fin 32)) (reg m (18 : Fin 32)) (reg m (19 : Fin 32))
          (reg m (26 : Fin 32)) ∧
        reg m' (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1023 ∧
        reg m' (8 : Fin 32) = (if st.2 then 1 else 0) ∧
        GM2 B m'.mem T0 T1 D0 D1 ∧ ptF m'.mem B 0x1480 = st.1 ∧ Pt2Lt st.1) := by
  obtain ⟨n1, c1, E1, fr1, K1, s1, X1, r91, r221, r251, r81, M1, A1⟩ :=
    ml2_pre F E RS hid s hsp h9 ha0 h27 hL0 hL1 M
  unfold mlMain2
  by_cases h0 : max L0 L1 = 0
  · rw [ite_eq_left h0] at s1
    rw [h0] at r221 ⊢
    exact .inr ⟨_, rfl, n1, c1, E1, fr1, K1, s1, X1, r221, by rw [r81]; rfl, M1, A1, idPt2_lt⟩
  rw [ite_eq_right h0] at s1
  obtain ⟨k, hk⟩ : ∃ k, max L0 L1 = k + 1 := ⟨max L0 L1 - 1, by omega⟩
  rw [hk] at r91 r221 ⊢
  have R1 : GR2 B n1 (reg m (3 : Fin 32)) (reg m (4 : Fin 32)) (reg m (18 : Fin 32)) (reg m (19 : Fin 32))
      (reg m (25 : Fin 32)) (reg m (26 : Fin 32)) k :=
    X1.gr r91 (by rw [r221, show 0x1023 + (k + 1) = 0x1024 + k by omega]) r251
  rcases ml2_loop (st := (idPt2, false)) F k E1 s1 R1 (by rw [r81]; rfl) M1 A1 idPt2_lt (by omega) with
    ⟨hn, hp⟩ | ⟨st, h2, n2, c2, E2, fr2, K2, s2, X2, r222, r82, M2, A2, l2⟩
  · exact .inl ⟨hn, Panics.of_steps c1 hp⟩
  exact .inr ⟨st, h2, n2, c1.trans c2, E2, fun x hx => by rw [fr2 x hx, fr1 x hx],
    (K1.trans K2).wider (mlW_dup fun p hp => by simp only [List.mem_append, or_self] at hp; exact hp),
    s2, X2, r222, r82, M2, A2, l2⟩

end C3.RV32.Sv
