import C3BootProofs.Proofs.P2vZDs3

/-!
# `p256_verify_prehash`: one constant-time divstep

The two halves of the loop body at 0xC3C, composed: the body takes the
state in `CtRegs2` to `CtRegs2` of `dsStep` of it.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

/-- One constant-time divstep, from 0xC3C to the loop's branch at 0xE02. -/
theorem ct2_body {B : Word} {m : Machine} {n : Nat} {s : Ds}
    (F : Fr B 0x3590) (C : P2vCode m.mem) (IC : P2vIvCode m.mem) (st : St m.mem P2V m 0xC3C (reg m)) (hsp : reg m sp = B + 0x21A0)
    (h8 : reg m (8 : Fin 32) = B + 0x21A0 + 0x920) (hcnt : reg m a4 = BitVec.ofNat 32 (n + 1))
    (hc : CtRegs2 B m.mem (reg m) s) :
    ∃ m', Steps m m' ∧ P2vCode m'.mem ∧ P2vIvCode m'.mem ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧
      (∀ e, e + 1 ≤ 0x13F0 → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0xC80 →
        m'.mem (B + 0x21A0 + BitVec.ofNat 32 e) = m.mem (B + 0x21A0 + BitVec.ofNat 32 e)) ∧
      St m'.mem P2V m' 0xE02 (reg m') ∧ reg m' sp = B + 0x21A0 ∧ reg m' (8 : Fin 32) = B + 0x21A0 + 0x920 ∧
      reg m' a4 = BitVec.ofNat 32 n ∧ reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧
      reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧ CtRegs2 B m'.mem (reg m') (dsStep s) := by
  obtain ⟨δ, f, g, u, v, q, r⟩ := s
  obtain ⟨hδ, hf, hg, hu, hv, hq, hr⟩ := hc
  dsimp only at hδ hf hg hu hv hq hr
  subst hδ hf hg hu hv hq hr
  obtain ⟨n1, c1, E1, IE1, fr1, fk1, s1, sp1, r1_3, r1_4, a0_1, a1_1, a2_1, a3_1, a4_1, r1_8, r1_18, r1_19, r1_21,
      r1_22, r1_23, r1_25, r1_26, r1_27, w3c_1, w24_1, d1, f1, g1, u1⟩ :=
    ct2_partA (n := n) F C IC st hsp h8 hcnt rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨n2, c2, E2, IE2, fr2, fk2, s2, sp2, r2_8, r2_a4, r2_3, r2_4, w40, w50, w48, w44, w4c, r2_24, r2_23, r2_26,
      v2, q2, rr2⟩ :=
    ct2_partB (n := n) F E1 IE1 s1 sp1 a0_1 a1_1 a2_1 a3_1 a4_1 r1_8 r1_18 r1_19 r1_21 r1_22 r1_23 r1_25 r1_26 r1_27
      w3c_1 w24_1
  obtain ⟨A1, A2, A3, A4, A5, A6, A7⟩ := ct_arith (memLoad32 m.mem (B + 0x21A0 + 0x40)) (reg m (24 : Fin 32))
    (memLoad32 m.mem (B + 0x21A0 + 0x50)) (memLoad32 m.mem (B + 0x21A0 + 0x48))
    (memLoad32 m.mem (B + 0x21A0 + 0x44)) (memLoad32 m.mem (B + 0x21A0 + 0x4C))
    (reg m (23 : Fin 32)) (reg m (26 : Fin 32)) (reg m (20 : Fin 32)) (reg m (25 : Fin 32))
    (memLoad32 m.mem (B + 0x21A0 + 0x54)) (reg m (18 : Fin 32)) (reg m (22 : Fin 32)) (reg m (13 : Fin 32))
  refine ⟨n2, c1.trans c2, E2, IE2, fun x hx => by rw [fr2 x hx, fr1 x hx],
    fun e he h1 h2 => by rw [fk2 e he h1 h2, fk1 e he h1 h2], s2, sp2, r2_8, r2_a4,
    by rw [r2_3, r1_3], by rw [r2_4, r1_4], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [w40, r2_24, d1, A1]
  · rw [w50, w48, f1, A2]
  · rw [w44, w4c, g1, A3]
  · rw [r2_23, r2_26, u1, A4]
  · rw [v2, A5]
  · rw [q2, A6]
  · rw [rr2, A7]

/-- The constant-time divstep loop: `k + 1` divsteps from 0xC3C, then on to
0xE06. -/
theorem ct2_loop {B : Word} (F : Fr B 0x3590) :
    ∀ k {m : Machine} {s : Ds}, P2vCode m.mem → P2vIvCode m.mem → St m.mem P2V m 0xC3C (reg m) → reg m sp = B + 0x21A0 →
      reg m (8 : Fin 32) = B + 0x21A0 + 0x920 → reg m a4 = BitVec.ofNat 32 (k + 1) → k + 1 < 2 ^ 32 →
      CtRegs2 B m.mem (reg m) s →
      ∃ m', Steps m m' ∧ P2vCode m'.mem ∧ P2vIvCode m'.mem ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧
        (∀ e, e + 1 ≤ 0x13F0 → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0xC80 →
          m'.mem (B + 0x21A0 + BitVec.ofNat 32 e) = m.mem (B + 0x21A0 + BitVec.ofNat 32 e)) ∧
        St m'.mem P2V m' 0xE06 (reg m') ∧ reg m' sp = B + 0x21A0 ∧ reg m' (8 : Fin 32) = B + 0x21A0 + 0x920 ∧
        reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧
        CtRegs2 B m'.mem (reg m') (dsIter (k + 1) s)
  | 0, m, s, E, IE, st, hsp, h8, hcnt, hk, hc => by
    obtain ⟨n1, c1, E1, IE1, fr1, fk1, s1, sp1, r1_8, r1_a4, r1_3, r1_4, C1⟩ := ct2_body F E IE st hsp h8 hcnt hc
    · obtain ⟨n2, d2, u2⟩ := s1.notTaken E1.self 0xE06 p2v_at_e02 (by decide)
        (by rw [r1_a4, s1.zero]; rfl)
      refine ⟨n2, c1.trans (.single d2), by rw [u2.mem]; exact E1, by rw [u2.mem]; exact IE1, fun x hx => by rw [u2.mem, fr1 x hx],
        fun e he h1 h2 => by rw [u2.mem, fk1 e he h1 h2], ⟨u2.pc, rfl, fun _ => rfl⟩, by rw [u2.regs, sp1],
        by rw [u2.regs, r1_8], by rw [u2.regs, r1_3], by rw [u2.regs, r1_4], C1.of u2.mem u2.regs⟩
  | k + 1, m, s, E, IE, st, hsp, h8, hcnt, hk, hc => by
    obtain ⟨n1, c1, E1, IE1, fr1, fk1, s1, sp1, r1_8, r1_a4, r1_3, r1_4, C1⟩ := ct2_body F E IE st hsp h8 hcnt hc
    · obtain ⟨n2, d2, u2⟩ := s1.taken E1.self 0xC3C p2v_at_e02 (by decide)
        (by rw [r1_a4, s1.zero]; exact bne_iff_ne.mpr (umin_ne0' (by omega) (by omega)))
      have s2 : St n2.mem P2V n2 0xC3C (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
      obtain ⟨n3, c3, E3, IE3, fr3, fk3, s3, sp3, r3_8, r3_3, r3_4, C3⟩ :=
        ct2_loop F k (s := dsStep s) (by rw [u2.mem]; exact E1) (by rw [u2.mem]; exact IE1) s2 (by rw [u2.regs, sp1])
          (by rw [u2.regs, r1_8]) (by rw [u2.regs, r1_a4]) (by omega) (C1.of u2.mem u2.regs)
      refine ⟨n3, c1.trans (.cons d2 c3), E3, IE3, fun x hx => by rw [fr3 x hx, u2.mem, fr1 x hx],
        fun e he h1 h2 => by rw [fk3 e he h1 h2, u2.mem, fk1 e he h1 h2], s3, sp3, r3_8,
        by rw [r3_3, u2.regs, r1_3], by rw [r3_4, u2.regs, r1_4], C3⟩

end C3.RV32.P2v

