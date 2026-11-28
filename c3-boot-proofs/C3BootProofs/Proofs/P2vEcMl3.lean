import C3BootProofs.Proofs.P2vEcMl2

/-!
# `p256VerifyPrehash`: the main loop's setup

From 0x998 to the loop's exit at 0xB00: the longer digit count, the point at
infinity in the accumulator, the loop's registers, and then `ml2_loop`. It
follows `ml_pre` in `Pv384G2.lean`.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Sv

set_option maxRecDepth 100000

def mlS0 : List BInstr := [.aluImm .add a1 x0 0x0, .aluImm .and a1 a1 0x1]
theorem mlS0_end : blockEnd p256VerifyPrehashCode 0x998 mlS0 = some 0x99C := by decide
def mlS1 : List BInstr := [.alu .add (9 : Fin 32) x0 a0]
theorem mlS1_end : blockEnd p256VerifyPrehashCode 0x9A2 mlS1 = some 0x9A4 := by decide
def mlS2 : List BInstr := [.aluImm .add a1 x0 0x1]
theorem mlS2_end : blockEnd p256VerifyPrehashCode 0x9A4 mlS2 = some 0x9A6 := by decide
def mlS3 : List BInstr := [.aluImm .and a1 a1 0x1]
theorem mlS3_end : blockEnd p256VerifyPrehashCode 0x99A mlS3 = some 0x99C := by decide
def mlS4 : List BInstr := [.lui a1 0x3FCC4000, .aluImm .add a1 a1 0x3D0, .aluImm .add a0 sp 0x7FF,
  .aluImm .add a0 a0 0x181, .aluImm .add a2 x0 0x60, .aluImm .add (20 : Fin 32) x0 0x60]
theorem mlS4_end : blockEnd p256VerifyPrehashCode 0x9A8 mlS4 = some 0x9C0 := by decide
def mlS5 : List BInstr := [.aluImm .add (21 : Fin 32) x0 0x0, .lui a0 0x1000, .aluImm .add a0 a0 0xE4,
  .alu .add a0 a0 sp, .alu .add a0 a0 (9 : Fin 32), .aluImm .add (23 : Fin 32) a0 0x3,
  .aluImm .add (22 : Fin 32) x0 0x108, .aluImm .add (8 : Fin 32) x0 0x2, .aluImm .add (24 : Fin 32) x0 0x101,
  .aluImm .add (25 : Fin 32) x0 0x300, .aluImm .add (26 : Fin 32) sp 0x300, .aluImm .add (27 : Fin 32) x0 0x10]
theorem mlS5_end : blockEnd p256VerifyPrehashCode 0x9C8 mlS5 = some 0x9EC := by decide

theorem s7_val2 (S : Word) (x : Nat) (hx : 1 ≤ x) :
    (4096 : Word) + 228 + S + BitVec.ofNat 32 x + 3 = S + BitVec.ofNat 32 (4328 + (x - 1)) := by
  pv_addr

set_option maxHeartbeats 32000000 in
/-- **The setup of the main loop**, from 0x998: the longer digit count, the
point at infinity in the accumulator, and the loop's registers; then the
loop head, or the exit when both counts are zero. -/
theorem ml2_pre {B : Word} {T0 T1 : Nat → Pt2} {D0 D1 : List Nat} {L0 L1 : Nat} {m : Machine}
    (F : Fr B 0x3590) (E : MlEnv m.mem) (RS : P2vRoSep B)
    (hid : CodeIn m.mem (BitVec.ofNat 32 (img% p256IdentityAddress)) p256IdentityData)
    (s : St m.mem P2V m 0x998 (reg m)) (hsp : reg m sp = B + 0x21A0)
    (h9 : reg m (9 : Fin 32) = BitVec.ofNat 32 L0) (ha0 : reg m a0 = BitVec.ofNat 32 L1)
    (hL0 : L0 ≤ 0x101) (hL1 : L1 ≤ 0x101) (M : GM2 B m.mem T0 T1 D0 D1) :
    ∃ m', Steps m m' ∧ MlEnv m'.mem ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧ P2vKeepL B m.mem m'.mem mlW ∧
      St m'.mem P2V m' (if max L0 L1 = 0 then 0xB00 else 0x9F0) (reg m') ∧
      (max L0 L1 ≠ 0 → GH2 B m' (reg m (3 : Fin 32)) (reg m (4 : Fin 32)) (max L0 L1 - 1)) ∧
      reg m' sp = B + 0x21A0 ∧ reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧
      reg m' (21 : Fin 32) = 0 ∧ GM2 B m'.mem T0 T1 D0 D1 ∧ ptF m'.mem B 0x980 = idPt2 := by
  have C := E.C.self
  obtain ⟨n1, c1, u1⟩ := s.block mlS0 C mlS0_end ⟨trivial, trivial, trivial⟩
  have s1 : St m.mem P2V n1 0x99C (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q ≠ a1 → reg n1 q = reg m q := fun q h => by
    rw [u1.regs, runBlock_reg _ _ _ q s.zero (by simp [mlS0, BInstr.dst, h])]
  have a11 : reg n1 a1 = 0 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, mlS0, upd, ↓reduceIte, aluEval]; rw [s.zero]; rfl
  obtain ⟨n2, d2, u2⟩ := s1.notTaken C 0x99E p2v_at_99c (by decide) (by rw [a11, s1.zero]; rfl)
  have s2 : St m.mem P2V n2 0x99E (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have e2 : reg n2 = reg n1 := funext u2.regs
  have hmax : ∃ n3, Steps n2 n3 ∧ St m.mem P2V n3 0x9A4 (reg n3) ∧
      reg n3 (9 : Fin 32) = BitVec.ofNat 32 (max L0 L1) ∧ ∀ q : Fin 32, q ≠ (9 : Fin 32) → reg n3 q = reg n2 q := by
    by_cases hlt : L1 < L0
    · obtain ⟨n3, d3, u3⟩ := s2.taken C 0x9A4 p2v_at_99e (by decide)
        (by rw [e2, k1 _ (by decide), ha0, k1 _ (by decide), h9]; simp only [branchTaken]
            rw [Pv.ult_ofNat (by omega) (by omega)]; simp [hlt])
      exact ⟨n3, .single d3, ⟨u3.pc, u3.mem, fun _ => rfl⟩,
        by rw [u3.regs, e2, k1 _ (by decide), h9, Nat.max_eq_left (by omega)], fun q _ => u3.regs q⟩
    · obtain ⟨n3, d3, u3⟩ := s2.notTaken C 0x9A2 p2v_at_99e (by decide)
        (by rw [e2, k1 _ (by decide), ha0, k1 _ (by decide), h9]; simp only [branchTaken]
            rw [Pv.ult_ofNat (by omega) (by omega)]; simp [hlt])
      have s3 : St m.mem P2V n3 0x9A2 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
      obtain ⟨n4, c4, u4⟩ := s3.block mlS1 C mlS1_end ⟨trivial, trivial⟩
      refine ⟨n4, .cons d3 c4, ⟨u4.pc, u4.mem, fun _ => rfl⟩, ?_, fun q h => ?_⟩
      · rw [u4.regs]; simp +decide only [runBlock, BInstr.run, mlS1, upd, ↓reduceIte, aluEval]
        rw [s3.zero, u3.regs, e2, k1 _ (by decide), ha0, Nat.max_eq_right (by omega)]; exact BitVec.zero_add _
      · rw [u4.regs, runBlock_reg _ _ _ q s3.zero (by simp [mlS1, BInstr.dst, h]), u3.regs]
  obtain ⟨n3, c3, s3, r93, k3⟩ := hmax
  obtain ⟨n4, c4, u4⟩ := s3.block mlS2 C mlS2_end ⟨trivial, trivial⟩
  have s4 : St m.mem P2V n4 0x9A6 (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
  obtain ⟨n5, d5, u5⟩ := s4.jump C p2v_at_9a6 (off' := 0x99A) (by decide) (by rw [s4.pc]; decide)
  have s5 : St m.mem P2V n5 0x99A (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
  obtain ⟨n6, c6, u6⟩ := s5.block mlS3 C mlS3_end ⟨trivial, trivial⟩
  have s6 : St m.mem P2V n6 0x99C (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
  have a16 : reg n6 a1 = 1 := by
    rw [u6.regs]; simp +decide only [runBlock, BInstr.run, mlS3, upd, ↓reduceIte, aluEval]
    rw [u5.regs, u4.regs]; simp +decide only [runBlock, BInstr.run, mlS2, upd, ↓reduceIte, aluEval]
    rw [s3.zero]; rfl
  have k6 : ∀ q : Fin 32, q ≠ a1 → reg n6 q = reg n3 q := fun q h => by
    rw [u6.regs, runBlock_reg _ _ _ q s5.zero (by simp [mlS3, BInstr.dst, h]), u5.regs, u4.regs,
      runBlock_reg _ _ _ q s3.zero (by simp [mlS2, BInstr.dst, h])]
  obtain ⟨n7, d7, u7⟩ := s6.taken C 0x9A8 p2v_at_99c (by decide) (by rw [a16, s6.zero]; decide)
  have s7 : St m.mem P2V n7 0x9A8 (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
  have k7 : ∀ q : Fin 32, q ≠ a1 → q ≠ (9 : Fin 32) → reg n7 q = reg m q := fun q h1 h9 => by
    rw [u7.regs, k6 q h1, k3 q h9, e2, k1 q h1]
  have r97 : reg n7 (9 : Fin 32) = BitVec.ofNat 32 (max L0 L1) := by rw [u7.regs, k6 _ (by decide), r93]
  obtain ⟨n8, c8, u8⟩ := s7.block mlS4 C mlS4_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m8 : n8.mem = m.mem := s7.mem ▸ u8.mem
  have s8 : St n8.mem P2V n8 0x9C0 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have k8 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (20 : Fin 32) → reg n8 q = reg n7 q :=
    fun q h0 h1 h2 h20 => by rw [u8.regs, runBlock_reg _ _ _ q s7.zero (by simp [mlS4, BInstr.dst, h0, h1, h2, h20])]
  have sp7 : reg n7 sp = B + 0x21A0 := by rw [k7 _ (by decide) (by decide), hsp]
  have sp8 : reg n8 sp = B + 0x21A0 := by rw [k8 _ (by decide) (by decide) (by decide) (by decide), sp7]
  have a08 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x980 := by
    rw [u8.regs]; simp +decide only [runBlock, BInstr.run, mlS4, upd, ↓reduceIte, aluEval]; rw [sp7]
    exact sp_980 _
  have a18 : reg n8 a1 = BitVec.ofNat 32 (img% p256IdentityAddress) := by
    rw [u8.regs]; simp +decide only [runBlock, BInstr.run, mlS4, upd, ↓reduceIte, aluEval]; try decide
  have a28 : reg n8 a2 = BitVec.ofNat 32 0x60 := by
    rw [u8.regs]; simp +decide only [runBlock, BInstr.run, mlS4, upd, ↓reduceIte, aluEval]; try rw [s7.zero]; try rfl
  have r208 : reg n8 (20 : Fin 32) = 0x60 := by
    rw [u8.regs]; simp +decide only [runBlock, BInstr.run, mlS4, upd, ↓reduceIte, aluEval]; try rw [s7.zero]; try rfl
  have E8 : MlEnv n8.mem := by rw [m8]; exact E
  obtain ⟨n9, P9, K9, X9⟩ := p2v_mcRo2 (c := 0x980) (N := 0x60) F RS E8.C s8 p2v_at_9c0 p2v_at_9c4
    (by decide) (by decide) sp8 a08 a18 a28 (by decide) (.inr ⟨by decide, by decide⟩)
  have E9 : MlEnv n9.mem := E8.fr F P9.fr
  have hid8 : CodeIn n8.mem (BitVec.ofNat 32 (img% p256IdentityAddress)) p256IdentityData := by rw [m8]; exact hid
  have hA : ptF n9.mem B 0x980 = idPt2 := by
    unfold ptF idPt2
    rw [accV_KD (M := n8.mem) (K := BitVec.ofNat 32 (img% p256IdentityAddress)) (d := 0) 8 fun q hq => by
        have := X9 q (by omega); rwa [Nat.zero_add],
      code_accV hid8 0 8 (by decide),
      accV_KD (M := n8.mem) (K := BitVec.ofNat 32 (img% p256IdentityAddress)) (d := 0x20) 8 fun q hq => by
        have := X9 (0x20 + q) (by omega)
        rwa [show 0x980 + (0x20 + q) = 0x980 + 0x20 + q by omega] at this,
      code_accV hid8 0x20 8 (by decide),
      accV_KD (M := n8.mem) (K := BitVec.ofNat 32 (img% p256IdentityAddress)) (d := 0x40) 8 fun q hq => by
        have := X9 (0x40 + q) (by omega)
        rwa [show 0x980 + (0x40 + q) = 0x980 + 0x40 + q by omega] at this,
      code_accV hid8 0x40 8 (by decide)]
  have K9' : P2vKeepL B m.mem n9.mem mlW := by
    rw [← m8]; exact (P2vKeepL.of K9).wider (by decide)
  obtain ⟨n10, c10, u10⟩ := P9.st.block mlS5 E9.C.self mlS5_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem P2V n10 0x9EC (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have z9 := P9.st.zero
  have r99 : reg n9 (9 : Fin 32) = BitVec.ofNat 32 (max L0 L1) := by
    rw [P9.regs _ (by decide), k8 _ (by decide) (by decide) (by decide) (by decide), r97]
  have sp9 : reg n9 sp = B + 0x21A0 := by rw [P9.regs _ (by decide), sp8]
  have k10 : ∀ q : Fin 32, q.val ∈ [2, 3, 4] → reg n10 q = reg m q := fun q hq => by
    rw [u10.regs, runBlock_reg _ _ _ q z9 (by revert hq; revert q; decide), P9.regs q (by revert hq; revert q; decide),
      k8 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide), k7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  have r910 : reg n10 (9 : Fin 32) = BitVec.ofNat 32 (max L0 L1) := by
    rw [u10.regs, runBlock_reg _ _ _ _ z9 (by decide), r99]
  have r21 : reg n10 (21 : Fin 32) = 0 := by
    rw [u10.regs]; simp +decide only [runBlock, BInstr.run, mlS5, upd, ↓reduceIte, aluEval]; rw [z9]; rfl
  have st : Steps m n10 := c1.trans (.cons d2 (c3.trans (c4.trans (.cons d5 (c6.trans (.cons d7 (c8.trans
    (P9.steps.trans c10))))))))
  have E10 : MlEnv n10.mem := by rw [m10]; exact E9
  have fr : ∀ x, P2vR B x → n10.mem x = m.mem x := fun x hx => by rw [m10, P9.fr x hx, m8]
  have K10 : P2vKeepL B m.mem n10.mem mlW := by rw [m10]; exact K9'
  have M10 : GM2 B n10.mem T0 T1 D0 D1 := M.keep K10
  have A10 : ptF n10.mem B 0x980 = idPt2 := by rw [m10]; exact hA
  by_cases h0 : max L0 L1 = 0
  · obtain ⟨n11, d11, u11⟩ := s10.taken E10.C.self 0xB00 p2v_at_9ec (by decide) (by rw [r910, h0, s10.zero]; rfl)
    rw [ite_eq_left h0]
    exact ⟨n11, st.trans (.single d11), by rw [u11.mem]; exact E10, fun x hx => by rw [u11.mem, fr x hx],
      by rw [u11.mem]; exact K10, ⟨u11.pc, rfl, fun _ => rfl⟩, fun h => absurd h0 h,
      by rw [u11.regs, k10 sp (by decide), hsp], by rw [u11.regs, k10 _ (by decide)],
      by rw [u11.regs, k10 _ (by decide)], by rw [u11.regs, r21], by rw [u11.mem]; exact M10,
      by rw [u11.mem]; exact A10⟩
  · obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.C.self 0x9F0 p2v_at_9ec (by decide)
      (by rw [r910, s10.zero]; simp only [branchTaken]
          exact beq_eq_false_iff_ne.2 (ofNat_ne0 (by omega) (by omega)))
    rw [ite_eq_right h0]
    have hv : ∀ q : Fin 32, reg n11 q = (runBlock mlS5 (n9.mem, reg n9)).2 q := fun q => by rw [u11.regs, u10.regs]
    refine ⟨n11, st.trans (.single d11), by rw [u11.mem]; exact E10, fun x hx => by rw [u11.mem, fr x hx],
      by rw [u11.mem]; exact K10, ⟨u11.pc, rfl, fun _ => rfl⟩, fun _ => ?_,
      by rw [u11.regs, k10 sp (by decide), hsp], by rw [u11.regs, k10 _ (by decide)],
      by rw [u11.regs, k10 _ (by decide)], by rw [u11.regs, r21], by rw [u11.mem]; exact M10,
      by rw [u11.mem]; exact A10⟩
    have r20 : reg n9 (20 : Fin 32) = 0x60 := by rw [P9.regs _ (by decide), r208]
    refine ⟨by rw [u11.regs, k10 sp (by decide), hsp], by rw [u11.regs, k10 _ (by decide)],
      by rw [u11.regs, k10 _ (by decide)], ?_, by rw [u11.regs, r910, show max L0 L1 - 1 + 1 = max L0 L1 by omega],
      by rw [hv, runBlock_reg _ _ _ _ z9 (by decide), r20], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hv]; simp +decide only [runBlock, BInstr.run, mlS5, upd, ↓reduceIte, aluEval]
    · rw [hv]; simp +decide only [runBlock, BInstr.run, mlS5, upd, ↓reduceIte, aluEval]
    · rw [hv]; simp +decide only [runBlock, BInstr.run, mlS5, upd, ↓reduceIte, aluEval]
      rw [sp9, r99]; exact s7_val2 _ _ (by omega)
    · rw [hv]; simp +decide only [runBlock, BInstr.run, mlS5, upd, ↓reduceIte, aluEval]
    · rw [hv]; simp +decide only [runBlock, BInstr.run, mlS5, upd, ↓reduceIte, aluEval]
    · rw [hv]; simp +decide only [runBlock, BInstr.run, mlS5, upd, ↓reduceIte, aluEval, sp9]; rfl
    · rw [hv]; simp +decide only [runBlock, BInstr.run, mlS5, upd, ↓reduceIte, aluEval]

set_option maxHeartbeats 16000000 in
/-- **The main loop with its setup**, from 0x998 to 0xB00: `mlMain2` over
the longer digit count. -/
theorem ml2_main {B : Word} {T0 T1 : Nat → Pt2} {D0 D1 : List Nat} {L0 L1 : Nat} {m : Machine}
    (F : Fr B 0x3590) (E : MlEnv m.mem) (RS : P2vRoSep B)
    (hid : CodeIn m.mem (BitVec.ofNat 32 (img% p256IdentityAddress)) p256IdentityData)
    (s : St m.mem P2V m 0x998 (reg m)) (hsp : reg m sp = B + 0x21A0)
    (h9 : reg m (9 : Fin 32) = BitVec.ofNat 32 L0) (ha0 : reg m a0 = BitVec.ofNat 32 L1)
    (hL0 : L0 ≤ 0x101) (hL1 : L1 ≤ 0x101) (M : GM2 B m.mem T0 T1 D0 D1) :
    (mlMain2 T0 T1 D0 D1 (max L0 L1) = none ∧ Panics m) ∨
    (∃ st, mlMain2 T0 T1 D0 D1 (max L0 L1) = some st ∧
      ∃ m', Steps m m' ∧ MlEnv m'.mem ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧ P2vKeepL B m.mem m'.mem mlW ∧
        St m'.mem P2V m' 0xB00 (reg m') ∧ reg m' sp = B + 0x21A0 ∧
        reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧
        reg m' (21 : Fin 32) = (if st.2 then 1 else 0) ∧
        GM2 B m'.mem T0 T1 D0 D1 ∧ ptF m'.mem B 0x980 = st.1 ∧ Pt2Lt st.1) := by
  obtain ⟨n1, c1, E1, fr1, K1, s1, G1, sp1, g31, g41, r21, M1, A1⟩ :=
    ml2_pre F E RS hid s hsp h9 ha0 hL0 hL1 M
  unfold mlMain2
  by_cases h0 : max L0 L1 = 0
  · rw [ite_eq_left h0] at s1
    rw [h0]
    exact .inr ⟨_, rfl, n1, c1, E1, fr1, K1, s1, sp1, g31, g41, by rw [r21]; rfl, M1, A1, idPt2_lt⟩
  rw [ite_eq_right h0] at s1
  obtain ⟨k, hk⟩ : ∃ k, max L0 L1 = k + 1 := ⟨max L0 L1 - 1, by omega⟩
  have G1' := G1 h0
  rw [hk, show k + 1 - 1 = k by omega] at G1'
  rw [hk]
  rcases ml2_loop (st := (idPt2, false)) F k E1 s1 G1' (by rw [r21]; rfl) M1 A1 idPt2_lt (by omega) with
    ⟨hn, hp⟩ | ⟨st, h2, n2, c2, E2, fr2, K2, s2, sp2, g32, g42, r212, M2, A2, l2⟩
  · exact .inl ⟨hn, Panics.of_steps c1 hp⟩
  exact .inr ⟨st, h2, n2, c1.trans c2, E2, fun x hx => by rw [fr2 x hx, fr1 x hx],
    (K1.trans K2).wider (by decide), s2, sp2, g32, g42, r212, M2, A2, l2⟩

end C3.RV32.P2v
