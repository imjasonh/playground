import C3BootProofs.Proofs.SvZDs3

/-!
# `sigstore::verify`: the constant-time divstep loop

The two halves of the loop body at 0x1BA4, composed: the body takes the
state in `ZtRegs` to `ZtRegs` of `dsStep` of it. The loop at 0x1B9E runs the
body once per step left in the slot at 0x48 and leaves at 0x1D62.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
/-- One constant-time divstep, from 0x1BA4 to the jump back at 0x1D60. -/
theorem zt_body {B : Word} {m : Machine} {s : Ds} {cnt : Word}
    (F : Fr B 0x3830) (E : SvCode m.mem) (IC : SvIvCode m.mem) (st : St m.mem SV m 0x1BA4 (reg m))
    (hsp : reg m sp = B + 0x21A0) (h27 : reg m (27 : Fin 32) = B + 0x21A0 + 0xA20)
    (hcnt : memLoad32 m.mem (B + 0x21A0 + 0x48) = cnt) (hc : ZtRegs B m.mem (reg m) s) :
    ∃ m', Steps m m' ∧ SvCode m'.mem ∧ SvIvCode m'.mem ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧
      SvKeepL B m.mem m'.mem ztL ∧ St m'.mem SV m' 0x1D60 (reg m') ∧ reg m' sp = B + 0x21A0 ∧
      reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧
      (∀ q : Fin 32, q.val ∈ [18, 19, 26] → reg m' q = reg m q) ∧
      reg m' (27 : Fin 32) = B + 0x21A0 + 0xA20 ∧
      memLoad32 m'.mem (B + 0x21A0 + 0x48) = cnt + 0xFFFFFFFF ∧ ZtRegs B m'.mem (reg m') (dsStep s) := by
  obtain ⟨δ, f, g, u, v, q, r⟩ := s
  obtain ⟨hδ, hf, hg, hu, hv, hq, hr⟩ := hc
  dsimp only at hδ hf hg hu hv hq hr
  subst hδ hf hg hu hv hq hr
  obtain ⟨n1, c1, E1, IC1, fr1, K1, s1, sp1, r1_3, r1_4, r1_k, r1_27, r1_23, r1_24, r1_21, r1_9, r1_22, q1, w1_10, w1_c,
      w1_48, w1_44, w1_40, w1_70, w1_60, w1_5c, w1_74, d1, f1, g1⟩ :=
    zt_partA F E IC st hsp h27 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hcnt
  obtain ⟨n2, c2, E2, IC2, fr2, K2, s2, sp2, r2_3, r2_4, r2_k, r2_27, k2, w2_48, u2, v2, q2, rr2⟩ :=
    zt_partB F E1 IC1 s1 sp1 r1_27 r1_23 r1_24 r1_21 r1_9 r1_22 w1_10 w1_c w1_48 w1_44 w1_40 w1_5c w1_74
  obtain ⟨A1, A2, A3, A4, A5, A6, A7⟩ := ct_arith (memLoad32 m.mem (B + 0x21A0 + 0x34))
    (memLoad32 m.mem (B + 0x21A0 + 0x38)) (memLoad32 m.mem (B + 0x21A0 + 0x30))
    (memLoad32 m.mem (B + 0x21A0 + 0x2C)) (memLoad32 m.mem (B + 0x21A0 + 0x24))
    (memLoad32 m.mem (B + 0x21A0 + 0x28)) (reg m (24 : Fin 32)) (memLoad32 m.mem (B + 0x21A0 + 0x3C))
    (memLoad32 m.mem (B + 0x21A0 + 0x44)) (memLoad32 m.mem (B + 0x21A0 + 0x40))
    (memLoad32 m.mem (B + 0x21A0 + 0x70)) (memLoad32 m.mem (B + 0x21A0 + 0x60))
    (memLoad32 m.mem (B + 0x21A0 + 0x5C)) (memLoad32 m.mem (B + 0x21A0 + 0x74))
  refine ⟨n2, c1.trans c2, E2, IC2, fun x hx => by rw [fr2 x hx, fr1 x hx],
    fun e he hL => by rw [K2 e he hL, K1 e he hL], s2, sp2, by rw [r2_3, r1_3], by rw [r2_4, r1_4],
    fun q hq => by rw [r2_k q hq, r1_k q hq], r2_27, w2_48,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k2 _ (by decide) (by decide) (by decide), k2 _ (by decide) (by decide) (by decide), d1, A1]
  · rw [k2 _ (by decide) (by decide) (by decide), k2 _ (by decide) (by decide) (by decide), f1, A2]
  · rw [k2 _ (by decide) (by decide) (by decide), k2 _ (by decide) (by decide) (by decide), g1, A3]
  · rw [u2, q1, A4]
  · rw [v2, A5]
  · rw [q2, A6]
  · rw [rr2, A7]

theorem ZtRegs.of {B : Word} {M M' : Word → BitVec 8} {f f' : Fin 32 → Word} {s : Ds} (h : ZtRegs B M f s)
    (hm : M' = M) (hf : f' (24 : Fin 32) = f (24 : Fin 32)) : ZtRegs B M' f' s := by
  subst hm; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, by rw [hf]; exact h4, h5, h6, h7⟩

set_option maxHeartbeats 8000000 in
/-- The constant-time divstep loop: `k` divsteps from its head at 0x1B9E,
then out at 0x1D62. -/
theorem zt_loop {B : Word} (F : Fr B 0x3830) :
    ∀ k {m : Machine} {s : Ds}, SvCode m.mem → SvIvCode m.mem → St m.mem SV m 0x1B9E (reg m) →
      reg m sp = B + 0x21A0 → reg m (27 : Fin 32) = B + 0x21A0 + 0xA20 →
      memLoad32 m.mem (B + 0x21A0 + 0x48) = BitVec.ofNat 32 k → k < 2 ^ 32 → ZtRegs B m.mem (reg m) s →
      ∃ m', Steps m m' ∧ SvCode m'.mem ∧ SvIvCode m'.mem ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧
        SvKeepL B m.mem m'.mem ztL ∧ St m'.mem SV m' 0x1D62 (reg m') ∧ reg m' sp = B + 0x21A0 ∧
        reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧
        (∀ q : Fin 32, q.val ∈ [18, 19, 26] → reg m' q = reg m q) ∧
        reg m' (27 : Fin 32) = B + 0x21A0 + 0xA20 ∧ memLoad32 m'.mem (B + 0x21A0 + 0x48) = 0 ∧
        ZtRegs B m'.mem (reg m') (dsIter k s) := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  intro k
  induction k with
  | zero =>
    intro m s E IC st hsp h27 hcnt _ hc
    obtain ⟨n1, d1, u1⟩ := st.lw E.self sv_at_1b9e (off' := 0x1BA0) (by decide)
      (by rw [hsp]; exact zfr_al FS (by decide) (by decide))
    rw [hsp, hcnt] at u1
    obtain ⟨n2, d2, u2⟩ := u1.taken E.self 0x1D62 sv_at_1ba0 (by decide)
      (by rw [upd_same (by decide), updz st.zero (by decide), st.zero]; rfl)
    have m2 : n2.mem = m.mem := u2.mem
    have e2 : ∀ q : Fin 32, q ≠ a0 → reg n2 q = reg m q := fun q h => by rw [u2.regs, updz st.zero h]
    exact ⟨n2, .cons d1 (.single d2), by rw [m2]; exact E, by rw [m2]; exact IC, fun x _ => by rw [m2],
      fun e _ _ => by rw [m2], ⟨u2.pc, rfl, fun _ => rfl⟩, by rw [e2 _ (by decide), hsp],
      e2 _ (by decide), e2 _ (by decide), fun q hq => e2 q (by revert hq; revert q; decide),
      by rw [e2 _ (by decide), h27], by rw [m2, hcnt]; try rfl,
      hc.of m2 (e2 _ (by decide))⟩
  | succ k ih =>
    intro m s E IC st hsp h27 hcnt hk hc
    obtain ⟨n1, d1, u1⟩ := st.lw E.self sv_at_1b9e (off' := 0x1BA0) (by decide)
      (by rw [hsp]; exact zfr_al FS (by decide) (by decide))
    rw [hsp, hcnt] at u1
    obtain ⟨n2, d2, u2⟩ := u1.notTaken E.self 0x1BA4 sv_at_1ba0 (by decide)
      (by rw [upd_same (by decide), updz st.zero (by decide), st.zero]
          exact br_beq_f (Pv.ofNat_ne0 (by omega) hk))
    have m2 : n2.mem = m.mem := u2.mem
    have e2 : ∀ q : Fin 32, q ≠ a0 → reg n2 q = reg m q := fun q h => by rw [u2.regs, updz st.zero h]
    have s2 : St n2.mem SV n2 0x1BA4 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
    obtain ⟨n3, c3, E3, IC3, fr3, K3, s3, sp3, r3_3, r3_4, r3_k, r3_27, w3, Z3⟩ :=
      zt_body F (by rw [m2]; exact E) (by rw [m2]; exact IC) s2 (by rw [e2 _ (by decide), hsp])
        (by rw [e2 _ (by decide), h27]) (by rw [m2, hcnt]) (hc.of m2 (e2 _ (by decide)))
    obtain ⟨n4, d4, u4⟩ := s3.jump E3.self sv_at_1d60 (off' := 0x1B9E) (by decide) (by rw [s3.pc]; decide)
    have m4 : n4.mem = n3.mem := u4.mem
    have s4 : St n4.mem SV n4 0x1B9E (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    obtain ⟨n5, c5, E5, IC5, fr5, K5, s5, sp5, r5_3, r5_4, r5_k, r5_27, w5, Z5⟩ :=
      ih (s := dsStep s) (by rw [m4]; exact E3) (by rw [m4]; exact IC3) s4 (by rw [u4.regs, sp3])
        (by rw [u4.regs, r3_27]) (by rw [m4, w3, ofNat_succ_dec]) (by omega) (Z3.of m4 (u4.regs _))
    exact ⟨n5, .cons d1 (.cons d2 (c3.trans (.cons d4 c5))), E5, IC5,
      fun x hx => by rw [fr5 x hx, m4, fr3 x hx, m2],
      fun e he hL => by rw [K5 e he hL, m4, K3 e he hL, m2], s5, sp5,
      by rw [r5_3, u4.regs, r3_3, e2 _ (by decide)], by rw [r5_4, u4.regs, r3_4, e2 _ (by decide)],
      fun q hq => by rw [r5_k q hq, u4.regs, r3_k q hq, e2 q (by revert hq; revert q; decide)], r5_27, w5, Z5⟩

end C3.RV32.Sv
