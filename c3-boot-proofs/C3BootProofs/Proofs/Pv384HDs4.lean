import C3BootProofs.Proofs.Pv384HDs3

/-!
# `p384_verify_prehash`: one constant-time divstep

The two halves of the loop body at 0xD36, composed: the body takes the
state in `CtRegs` to `CtRegs` of `dsStep` of it.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

theorem ite01_ff (c : Prop) [Decidable c] : ((if c then 0 else 1 : Word) &&& 0xFF) = if c then 0 else 1 := by
  by_cases h : c
  · rw [ite_eq_left h]; rfl
  · rw [ite_eq_right h]; rfl

theorem umin_ne0 {rem : Nat} (h : rem ≠ 0) : BitVec.ofNat 32 (min rem 62) ≠ 0 := fun h' => by
  have := congrArg BitVec.toNat h'
  rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this; omega

theorem umin_ne0' {k : Nat} (h0 : 0 < k) (h1 : k < 2 ^ 32) : BitVec.ofNat 32 k ≠ 0 := fun h' => by
  have := congrArg BitVec.toNat h'
  rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this; omega

theorem w64_lt (lo hi : Word) : W64 lo hi < 2 ^ 64 := by
  have := lo.isLt; have := hi.isLt; simp only [W64]; omega

theorem w64_odd {gl gh : Word} : (gl &&& 1 = 1) ↔ W64 gl gh % 2 = 1 := by
  rw [gb_one]; simp only [W64]
  exact ⟨fun h => by omega, fun h => by omega⟩

theorem ctC1_eq (dl dh : Word) : ctC1 dl dh = if dsPos (W64 dl dh) then 1 else 0 := ct_c1 dl dh

theorem ctC3_eq (gl dl dh : Word) :
    ctC3 gl dl dh = if gl &&& 1 = 1 ∧ dsPos (W64 dl dh) then 1 else 0 := by
  show (gl &&& 1) &&& ctC1 dl dh = _
  rw [ctC1_eq]
  rcases gb01 gl with h | h <;> rw [h]
  · have : ¬((0 : Word) = 1 ∧ dsPos (W64 dl dh)) := fun h' => absurd h'.1 (by decide)
    rw [ite_eq_right this]
    by_cases hp : dsPos (W64 dl dh)
    · rw [ite_eq_left hp]; rfl
    · rw [ite_eq_right hp]; rfl
  · by_cases hp : dsPos (W64 dl dh)
    · rw [ite_eq_left hp, ite_eq_left ⟨rfl, hp⟩]; rfl
    · rw [ite_eq_right hp, ite_eq_right fun h' => hp h'.2]; rfl

/-- The constant-time body's arithmetic is `dsStep`. -/
theorem ct_arith (dl dh fl fh gl gh ul uh vl vh ql qh rl rh : Word) :
    let s : Ds := ⟨W64 dl dh, W64 fl fh, W64 gl gh, W64 ul uh, W64 vl vh, W64 ql qh, W64 rl rh⟩
    (dsStep s).δ = (if ctC3 gl dl dh = 1 then (2 + 2 ^ 64 - W64 dl dh) % 2 ^ 64 else (W64 dl dh + 2) % 2 ^ 64) ∧
    (dsStep s).f = (if ctC3 gl dl dh = 1 then W64 gl gh else W64 fl fh) ∧
    (dsStep s).g = asr64 (if ctC3 gl dl dh = 1 then (W64 gl gh + 2 ^ 64 - W64 (fl &&& ctMk gl) (fh &&& ctMk gl)) % 2 ^ 64
          else (W64 (fl &&& ctMk gl) (fh &&& ctMk gl) + W64 gl gh) % 2 ^ 64) ∧
    (dsStep s).u = 2 * (if ctC3 gl dl dh = 1 then W64 ql qh else W64 ul uh) % 2 ^ 64 ∧
    (dsStep s).v = 2 * (if ctC3 gl dl dh = 1 then W64 rl rh else W64 vl vh) % 2 ^ 64 ∧
    (dsStep s).q = (W64 ql qh + (if gl &&& 1 = 1 then
          (if ctC1 dl dh = 1 then (2 ^ 64 - W64 ul uh) % 2 ^ 64 else W64 ul uh) else 0)) % 2 ^ 64 ∧
    (dsStep s).r = (W64 rl rh + (if gl &&& 1 = 1 then
          (if ctC1 dl dh = 1 then (2 ^ 64 - W64 vl vh) % 2 ^ 64 else W64 vl vh) else 0)) % 2 ^ 64 := by
  intro s
  have hm : W64 (fl &&& ctMk gl) (fh &&& ctMk gl) = if gl &&& 1 = 1 then W64 fl fh else 0 := w64_mask fl fh _
  rw [hm]
  have := w64_lt gl gh; have := w64_lt fl fh; have := w64_lt ul uh; have := w64_lt vl vh
  have := w64_lt ql qh; have := w64_lt rl rh
  by_cases ho : gl &&& 1 = 1
  · have ho' : ¬(W64 gl gh % 2 = 0) := by rw [w64_odd.mp ho]; decide
    by_cases hp : dsPos (W64 dl dh)
    · have hc3 : ctC3 gl dl dh = 1 := by rw [ctC3_eq, ite_eq_left ⟨ho, hp⟩]
      have hc1 : ctC1 dl dh = 1 := by rw [ctC1_eq, ite_eq_left hp]
      have e : dsStep s = ⟨(2 + 2 ^ 64 - W64 dl dh) % 2 ^ 64, W64 gl gh,
          asr64 ((W64 gl gh + 2 ^ 64 - W64 fl fh) % 2 ^ 64), 2 * W64 ql qh % 2 ^ 64, 2 * W64 rl rh % 2 ^ 64,
          (W64 ql qh + 2 ^ 64 - W64 ul uh) % 2 ^ 64, (W64 rl rh + 2 ^ 64 - W64 vl vh) % 2 ^ 64⟩ := by
        simp only [dsStep, s]; rw [ite_eq_right ho', ite_eq_left hp]
      simp +decide only [e, hc3, hc1, ho, ↓reduceIte, and_true, true_and]
      constructor <;> omega
    · have hc3 : ctC3 gl dl dh = 0 := by rw [ctC3_eq, ite_eq_right fun h => hp h.2]
      have hc1 : ctC1 dl dh = 0 := by rw [ctC1_eq, ite_eq_right hp]
      have e : dsStep s = ⟨(W64 dl dh + 2) % 2 ^ 64, W64 fl fh, asr64 ((W64 gl gh + W64 fl fh) % 2 ^ 64),
          2 * W64 ul uh % 2 ^ 64, 2 * W64 vl vh % 2 ^ 64, (W64 ql qh + W64 ul uh) % 2 ^ 64,
          (W64 rl rh + W64 vl vh) % 2 ^ 64⟩ := by
        simp only [dsStep, s]; rw [ite_eq_right ho', ite_eq_right hp]
      simp +decide only [e, hc3, hc1, ho, ↓reduceIte, and_true, true_and]
      rw [Nat.add_comm (W64 fl fh)]
  · have he : W64 gl gh % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (W64 gl gh) with h | h
      · exact h
      · exact absurd (w64_odd.mpr h) ho
    have hc3 : ctC3 gl dl dh = 0 := by rw [ctC3_eq, ite_eq_right fun h => ho h.1]
    have e : dsStep s = ⟨(W64 dl dh + 2) % 2 ^ 64, W64 fl fh, asr64 (W64 gl gh), 2 * W64 ul uh % 2 ^ 64,
        2 * W64 vl vh % 2 ^ 64, W64 ql qh, W64 rl rh⟩ := by
      simp only [dsStep, s]; rw [ite_eq_left he]
    simp +decide only [e, hc3, ho, ↓reduceIte, and_true, true_and]
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.zero_add, Nat.mod_eq_of_lt (w64_lt gl gh)]
    · omega
    · omega

/-- One constant-time divstep, from 0xD36 to the loop's branch at 0xEFE. -/
theorem ct_body {B : Word} {m : Machine} {n : Nat} {s : Ds}
    (F : Fr B 0x21A0) (E : PvEnv3 m.mem) (st : St m.mem PV m 0xD36 (reg m)) (hsp : reg m sp = B + 0x420)
    (h8 : reg m (8 : Fin 32) = B + 0x420 + 0xD80) (hcnt : reg m a4 = BitVec.ofNat 32 (n + 1))
    (hc : CtRegs B m.mem (reg m) s) :
    ∃ m', Steps m m' ∧ PvEnv3 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
      (∀ e, e + 1 ≤ 0x1D4C → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0x1294 →
        m'.mem (B + 0x420 + BitVec.ofNat 32 e) = m.mem (B + 0x420 + BitVec.ofNat 32 e)) ∧
      St m'.mem PV m' 0xEFE (reg m') ∧ reg m' sp = B + 0x420 ∧ reg m' (8 : Fin 32) = B + 0x420 + 0xD80 ∧
      reg m' a4 = BitVec.ofNat 32 n ∧ reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧
      reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧ CtRegs B m'.mem (reg m') (dsStep s) := by
  obtain ⟨δ, f, g, u, v, q, r⟩ := s
  obtain ⟨hδ, hf, hg, hu, hv, hq, hr⟩ := hc
  dsimp only at hδ hf hg hu hv hq hr
  subst hδ hf hg hu hv hq hr
  obtain ⟨n1, c1, E1, fr1, fk1, s1, sp1, r1_3, r1_4, a0_1, a1_1, a2_1, a3_1, a4_1, r1_8, r1_18, r1_19, r1_21,
      r1_22, r1_23, r1_25, r1_26, r1_27, w3c_1, w24_1, d1, f1, g1, u1⟩ :=
    ct_partA (n := n) F E st hsp h8 hcnt rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨n2, c2, E2, fr2, fk2, s2, sp2, r2_8, r2_a4, r2_3, r2_4, w40, w50, w48, w44, w4c, r2_24, r2_23, r2_26,
      v2, q2, rr2⟩ :=
    ct_partB (n := n) F E1 s1 sp1 a0_1 a1_1 a2_1 a3_1 a4_1 r1_8 r1_18 r1_19 r1_21 r1_22 r1_23 r1_25 r1_26 r1_27
      w3c_1 w24_1
  obtain ⟨A1, A2, A3, A4, A5, A6, A7⟩ := ct_arith (memLoad32 m.mem (B + 0x420 + 0x40)) (reg m (24 : Fin 32))
    (memLoad32 m.mem (B + 0x420 + 0x50)) (memLoad32 m.mem (B + 0x420 + 0x48))
    (memLoad32 m.mem (B + 0x420 + 0x44)) (memLoad32 m.mem (B + 0x420 + 0x4C))
    (reg m (23 : Fin 32)) (reg m (26 : Fin 32)) (reg m (20 : Fin 32)) (reg m (25 : Fin 32))
    (memLoad32 m.mem (B + 0x420 + 0x54)) (reg m (18 : Fin 32)) (reg m (22 : Fin 32)) (reg m (13 : Fin 32))
  refine ⟨n2, c1.trans c2, E2, fun x hx => by rw [fr2 x hx, fr1 x hx],
    fun e he h1 h2 => by rw [fk2 e he h1 h2, fk1 e he h1 h2], s2, sp2, r2_8, r2_a4,
    by rw [r2_3, r1_3], by rw [r2_4, r1_4], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [w40, r2_24, d1, A1]
  · rw [w50, w48, f1, A2]
  · rw [w44, w4c, g1, A3]
  · rw [r2_23, r2_26, u1, A4]
  · rw [v2, A5]
  · rw [q2, A6]
  · rw [rr2, A7]

theorem CtRegs.of {B : Word} {M M' : Word → BitVec 8} {f f' : Fin 32 → Word} {s : Ds} (h : CtRegs B M f s)
    (hm : M' = M) (hf : ∀ q, f' q = f q) : CtRegs B M' f' s := by
  subst hm; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨by rw [hf]; exact h1, h2, h3, by rw [hf, hf]; exact h4, by rw [hf, hf]; exact h5,
    by rw [hf]; exact h6, by rw [hf, hf]; exact h7⟩

/-- The constant-time divstep loop: `k + 1` divsteps from 0xD36, then on to
0xF02. -/
theorem ct_loop {B : Word} (F : Fr B 0x21A0) :
    ∀ k {m : Machine} {s : Ds}, PvEnv3 m.mem → St m.mem PV m 0xD36 (reg m) → reg m sp = B + 0x420 →
      reg m (8 : Fin 32) = B + 0x420 + 0xD80 → reg m a4 = BitVec.ofNat 32 (k + 1) → k + 1 < 2 ^ 32 →
      CtRegs B m.mem (reg m) s →
      ∃ m', Steps m m' ∧ PvEnv3 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
        (∀ e, e + 1 ≤ 0x1D4C → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0x1294 →
          m'.mem (B + 0x420 + BitVec.ofNat 32 e) = m.mem (B + 0x420 + BitVec.ofNat 32 e)) ∧
        St m'.mem PV m' 0xF02 (reg m') ∧ reg m' sp = B + 0x420 ∧ reg m' (8 : Fin 32) = B + 0x420 + 0xD80 ∧
        reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧
        CtRegs B m'.mem (reg m') (dsIter (k + 1) s)
  | 0, m, s, E, st, hsp, h8, hcnt, hk, hc => by
    obtain ⟨n1, c1, E1, fr1, fk1, s1, sp1, r1_8, r1_a4, r1_3, r1_4, C1⟩ := ct_body F E st hsp h8 hcnt hc
    · obtain ⟨n2, d2, u2⟩ := s1.notTaken E1.E.C.self 0xF02 pv_at_efe (by decide)
        (by rw [r1_a4, s1.zero]; rfl)
      refine ⟨n2, c1.trans (.single d2), by rw [u2.mem]; exact E1, fun x hx => by rw [u2.mem, fr1 x hx],
        fun e he h1 h2 => by rw [u2.mem, fk1 e he h1 h2], ⟨u2.pc, rfl, fun _ => rfl⟩, by rw [u2.regs, sp1],
        by rw [u2.regs, r1_8], by rw [u2.regs, r1_3], by rw [u2.regs, r1_4], C1.of u2.mem u2.regs⟩
  | k + 1, m, s, E, st, hsp, h8, hcnt, hk, hc => by
    obtain ⟨n1, c1, E1, fr1, fk1, s1, sp1, r1_8, r1_a4, r1_3, r1_4, C1⟩ := ct_body F E st hsp h8 hcnt hc
    · obtain ⟨n2, d2, u2⟩ := s1.taken E1.E.C.self 0xD36 pv_at_efe (by decide)
        (by rw [r1_a4, s1.zero]; exact bne_iff_ne.mpr (umin_ne0' (by omega) (by omega)))
      have s2 : St n2.mem PV n2 0xD36 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
      obtain ⟨n3, c3, E3, fr3, fk3, s3, sp3, r3_8, r3_3, r3_4, C3⟩ :=
        ct_loop F k (s := dsStep s) (by rw [u2.mem]; exact E1) s2 (by rw [u2.regs, sp1])
          (by rw [u2.regs, r1_8]) (by rw [u2.regs, r1_a4]) (by omega) (C1.of u2.mem u2.regs)
      refine ⟨n3, c1.trans (.cons d2 c3), E3, fun x hx => by rw [fr3 x hx, u2.mem, fr1 x hx],
        fun e he h1 h2 => by rw [fk3 e he h1 h2, u2.mem, fk1 e he h1 h2], s3, sp3, r3_8,
        by rw [r3_3, u2.regs, r1_3], by rw [r3_4, u2.regs, r1_4], C3⟩

end C3.RV32.Pv
