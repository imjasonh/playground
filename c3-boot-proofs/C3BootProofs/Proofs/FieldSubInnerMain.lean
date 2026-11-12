import C3BootProofs.Proofs.FieldSubInner
import C3BootProofs.Image.Bootloader

/-! # `sub_inner`, end to end -/

namespace C3.RV32

open C3.Image

theorem addBack_length (d0 d1 d2 d3 d4 d5 d6 d7 m : Word) : (addBack d0 d1 d2 d3 d4 d5 d6 d7 m).length = 8 := rfl

theorem limbVal9 (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Word) :
    limbVal [x0, x1, x2, x3, x4, x5, x6, x7, x8] = limbVal [x0, x1, x2, x3, x4, x5, x6, x7] + 2 ^ 256 * x8.toNat := by
  simp only [limbVal]; omega

theorem maskBit_zero {b : Word} (hb : b = 0 ∨ b = 0xFFFFFFFF) : (maskBit b = 0) = (b = 0) := by
  rcases hb with rfl | rfl <;> decide

theorem wordsAt_length (M : Word → BitVec 8) (a : Word) (n : Nat) : (wordsAt M a n).length = n := by
  simp [wordsAt]

theorem maskBit_le1 (b : Word) : maskBit b ≤ 1 := by unfold maskBit; split <;> decide

/-- A store at word offset `c` from `b` leaves the word at a different
offset `d`. -/
theorem memLoad32_store32_off {M : Word → BitVec 8} {b v : Word} {c d : Nat} (hcd : (c == d) = false)
    (hc : c % 4 = 0) (hd : d % 4 = 0) (hcb : c + 4 ≤ 2 ^ 32) (hdb : d + 4 ≤ 2 ^ 32) :
    memLoad32 (memStore32 M (b + BitVec.ofNat 32 c) v) (b + BitVec.ofNat 32 d) = memLoad32 M (b + BitVec.ofNat 32 d) :=
  memLoad32_store32_sep (sep_offsets b (by
    have := beq_eq_false_iff_ne.mp hcd
    by_cases h : c < d
    · exact .inl (by omega)
    · exact .inr (by omega)) hcb hdb)

set_option exponentiation.threshold 300 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `sub_inner`**, called with the result at `out` and the
9-limb operands `L` at `lp` and `R` at `rp`. It stores `subGen L R`, which is
`L - R` with `p` added back when it borrows, in the result's first eight
words and the borrow mask, all ones exactly when `L < R`, in the ninth. It
returns with `sp` and every register but `a0` through `a5` and `t0` as they
were, and changes no memory outside the 0x34 bytes of stack below `sp` and
the result. -/
theorem subInner_gen (m : Machine) {P sp0 out lp rp retAddr : Word}
    (env : SIEnvG m.mem P sp0 out lp rp) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = lp)
    (ha2 : reg m a2 = rp) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ t0 → reg m' q = reg m q) ∧
      limbVal (wordsAt m'.mem out 8) = subGen (limbVal (wordsAt m.mem lp 9)) (limbVal (wordsAt m.mem rp 9)) ∧
      memLoad32 m'.mem (out + 32) =
        (if limbVal (wordsAt m.mem lp 9) < limbVal (wordsAt m.mem rp 9) then 0xFFFFFFFF else 0) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → Sep out 36 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have F_eq : sp0 + 0xFFFFFFD0 = sp0 + 0xFFFFFFCC + 4 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code si_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0) sp = sp0 + 0xFFFFFFD0 := by
    simp +decide [upd, hsp]; rfl
  have hF : (sp0 + 0xFFFFFFD0).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFFD0) (by decide)
  have sF : ∀ c n, c + n ≤ 0x30 → Sep (sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 c) n P subInnerCode.length :=
    fun c n h => by
      rw [F_eq, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
      exact env.sSC.sub (c := 4 + c) (l := n) (by omega)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock siPs) u1 env.code siSave_end (saveBlock_ok _ siPs _ fun q hq => by
      rw [sp1]
      simp only [siPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add hF (by decide), sF _ 4 (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  -- the stack region holds every write until the add-back
  have inS : ∀ c n, c + n ≤ 0x30 → ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 →
      Sep (sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 c) n x 1 := fun c n h x hx => by
    rw [F_eq, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
    exact hx.sub (c := 4 + c) (l := n) (by omega)
  have M2out : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 →
      saveMem m.mem (sp0 + 0xFFFFFFD0) (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0)) siPs x = m.mem x :=
    fun x hx => saveMem_outside siPs fun q hq => by
      simp only [siPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact inS _ 4 (by decide) x hx
  have codeS : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFFCC) 0x34 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by
      have h1 : Sep (sp0 + 0xFFFFFFCC) 0x34 (_ + BitVec.ofNat 32 i) 1 := hs.subR (c := i) (l := 1) (by omega)
      rw [hM _ h1]; exact hc i hi
  have Fm4 : sp0 + 0xFFFFFFD0 + 0xFFFFFFFC = sp0 + 0xFFFFFFCC := by rw [BitVec.add_assoc]; rfl
  have hsB : Sep (sp0 + 0xFFFFFFD0 + 0xFFFFFFFC) 4 (siBsub P) borrowingSubCode.length := by
    rw [Fm4]; exact env.sSB.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h
  have bS : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → Sep (sp0 + 0xFFFFFFD0 + 0xFFFFFFFC) 4 x 1 := fun x hx => by
    rw [Fm4]; exact hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h
  have wS : ∀ c, c + 4 ≤ 0x30 → ∀ (M' : Word → BitVec 8) v x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 →
      memStore32 M' (sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 c) v x = M' x :=
    fun c h M' v x hx => memStore32_get_sep (inS c 4 h x hx)
  have u2' := u2.self
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q1]
  have sp2 : reg m2 sp = sp0 + 0xFFFFFFD0 := by rw [u2.regs]; exact sp1
  have I2 : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 →
      saveMem m.mem (sp0 + 0xFFFFFFD0) (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0)) siPs x = m.mem x :=
    M2out
  have cc2 := codeS env.code env.sSC I2
  obtain ⟨m3, d3, u3⟩ := u2'.sw cc2 si_at_14 (off' := 0x16) (by decide)
    (by rw [sp2]; exact aligned_add hF (k := 8) (by decide))
  rw [sp2] at u3
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 (saveMem m.mem (sp0 + 0xFFFFFFD0)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0)) siPs) (sp0 + 0xFFFFFFD0 + 8) (reg m2 24) = M3 :=
    ⟨_, rfl⟩
  rw [hM3] at u3
  have I3 : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3]; exact (wS 8 (by decide) _ _ x hx).trans (I2 x hx)
  obtain ⟨m4, d4, u4⟩ := u3.sw (codeS env.code env.sSC I3) si_at_16 (off' := 0x18) (by decide)
    (by rw [sp2]; exact aligned_add hF (k := 4) (by decide))
  rw [sp2] at u4
  obtain ⟨M4, hM4⟩ : ∃ M4, memStore32 M3 (sp0 + 0xFFFFFFD0 + 4) (reg m2 25) = M4 := ⟨_, rfl⟩
  rw [hM4] at u4
  have I4 : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → M4 x = m.mem x := fun x hx => by
    rw [← hM4]; exact (wS 4 (by decide) _ _ x hx).trans (I3 x hx)
  obtain ⟨m5, d5, u5⟩ := u4.sw (codeS env.code env.sSC I4) si_at_18 (off' := 0x1A) (by decide)
    (by rw [sp2, add_lit_zero]; exact hF)
  rw [sp2] at u5
  obtain ⟨M5, hM5⟩ : ∃ M5, memStore32 M4 (sp0 + 0xFFFFFFD0 + 0) (reg m2 26) = M5 := ⟨_, rfl⟩
  rw [hM5] at u5
  have I5 : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → M5 x = m.mem x := fun x hx => by
    rw [← hM5]; exact (wS 0 (by decide) _ _ x hx).trans (I4 x hx)
  have opW : ∀ {a : Word}, Sep a 36 (sp0 + 0xFFFFFFCC) 0x34 → ∀ (M' : Word → BitVec 8),
      (∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → M' x = m.mem x) → ∀ i, i < 9 →
      memLoad32 M' (a + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (a + BitVec.ofNat 32 (4 * i)) :=
    fun ha M' hM i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact hM _ (ha.sub (c := 4 * i + j) (l := 1) (by omega)).symm
  have c5 := codeS env.code env.sSC I5
  have z2 : reg m2 0 = 0 := u2'.zero
  have z2' : reg m2 x0 = 0 := u2'.zero
  obtain ⟨n1, e1, v1⟩ := u5.alu c5 si_at_1a (off' := 0x1C) (by decide)
  obtain ⟨n2, e2, v2⟩ := v1.alu c5 si_at_1c (off' := 0x1E) (by decide)
  have g2a1 : reg m2 a1 = lp := by rw [r2 a1 (by decide), ha1]
  have g2a2 : reg m2 a2 = rp := by rw [r2 a2 (by decide), ha2]
  have g2a0 : reg m2 a0 = out := by rw [r2 a0 (by decide), ha0]
  obtain ⟨n3, e3, v3⟩ := v2.lw c5 si_at_1e (off' := 0x20) (by decide)
    (by simp +decide only [upd, ite_false]; rw [g2a1, add_lit_zero]; exact env.hlp)
  obtain ⟨n4, e4, v4⟩ := v3.lw c5 si_at_20 (off' := 0x22) (by decide)
    (by simp +decide only [upd, ite_false, ite_true, aluEval, z2]; rw [show (0 : Word) + reg m2 a2 = reg m2 a2 from BitVec.zero_add _, g2a2, add_lit_zero]; exact env.hrp)
  obtain ⟨n5, e5, v5⟩ := v4.alu c5 si_at_22 (off' := 0x24) (by decide)
  obtain ⟨n6, e6, v6⟩ := v5.alu c5 si_at_24 (off' := 0x26) (by decide)
  obtain ⟨n7, e7, v7⟩ := v6.aluImm c5 si_at_26 (off' := 0x28) (by decide)
  have r7 : ∀ q, q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ a2 → q ≠ a1 → q ≠ (18 : Fin 32) → q ≠ a0 →
      reg n7 q = reg m2 q := fun q q9 q8 q2 q1 q18 q0 => by
    rw [v7.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, z2]
    · simp [upd, h0, q9, q8, q2, q1, q18, q0]
  have n7s0 : reg n7 (8 : Fin 32) = lp := by rw [v7.regs]; simp +decide [upd, alu_zadd, g2a1]
  have n7s1 : reg n7 (9 : Fin 32) = rp := by rw [v7.regs]; simp +decide [upd, z2', alu_zadd, g2a2]
  have n7s2 : reg n7 (18 : Fin 32) = out := by rw [v7.regs]; simp +decide [upd, alu_zadd, g2a0]
  have n7a0 : reg n7 a0 = memLoad32 m.mem (lp + BitVec.ofNat 32 (4 * 0)) := by
    rw [v7.regs]; simp +decide [upd, alu_zadd, g2a1]
    have h := opW env.sLS M5 I5 0 (by decide)
    rwa [show (4 : Nat) * 0 = 0 from rfl, add_ofNat_zero] at h
  have n7a1 : reg n7 a1 = memLoad32 m.mem (rp + BitVec.ofNat 32 (4 * 0)) := by
    rw [v7.regs]; simp +decide [upd, z2', alu_zadd, g2a2]
    have h := opW env.sRS M5 I5 0 (by decide)
    rwa [show (4 : Nat) * 0 = 0 from rfl, add_ofNat_zero] at h
  have n7a2 : reg n7 a2 = 0 := by rw [v7.regs]; simp +decide [upd, alu_zadd]
  have n7sp : reg n7 sp = sp0 + 0xFFFFFFD0 := by rw [r7 sp (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), sp2]
  have b5 : CodeIn M5 (siBsub P) borrowingSubCode := codeS env.bsub env.sSB I5
  have hcb0 : P + BitVec.ofNat 32 0x28 + 0xFFFF1000 + 0xFFFFF890 = siBsub P := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  obtain ⟨n8, c8, w0, w0a0, w0a1, w0sp, fr0, mem0⟩ := si_bsub v7.self c5 b5 env.hP si_at_28 si_at_2c hcb0
    (even_at P env.hP 0x30 (by decide)) n7sp hF hsB
  rw [n7a0, n7a1, n7a2] at w0a0 w0a1
  have I8 : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → n8.mem x = m.mem x := fun x hx => by
    rw [mem0 x (bS x hx)]; exact I5 x hx
  have k8 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) →
      q ≠ (18 : Fin 32) → reg n8 q = reg m2 q := fun q q0 q1 q2 q3 q4 qr q9 q8 q18 => by
    rw [fr0 q q0 q1 q2 q3 q4 qr, r7 q q9 q8 q2 q1 q18 q0]
  have s0_0 : reg n8 (8 : Fin 32) = lp := by
    rw [fr0 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), n7s0]
  have s1_0 : reg n8 (9 : Fin 32) = rp := by
    rw [fr0 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), n7s1]
  have s2_0 : reg n8 (18 : Fin 32) = out := by
    rw [fr0 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), n7s2]
  have hcb1 : P + BitVec.ofNat 32 0x3C + 0xFFFF1000 + 0xFFFFF87C = siBsub P := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  obtain ⟨p1, cp1, w1, K1, a0_1, a1_1, sp1, fr1, mem1⟩ := si_round (K := (19 : Fin 32)) (i := 1)
    w0 (codeS env.code env.sSC I8) (codeS env.bsub env.sSB I8) env.hP
    si_at_30 si_at_32 si_at_34 si_at_36 si_at_38 si_at_3a si_at_3c si_at_40 hcb1
    (even_at P env.hP 0x44 (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s0_0 s1_0 w0sp hF
    (aligned_add env.hlp (by decide)) (aligned_add env.hrp (by decide)) hsB
  have Ip1 : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → p1.mem x = m.mem x := fun x hx => by
    rw [mem1 x (bS x hx)]; exact I8 x hx
  have s0_1 : reg p1 (8 : Fin 32) = lp := by rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s0_0]
  have s1_1 : reg p1 (9 : Fin 32) = rp := by rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s1_0]
  have s2_1 : reg p1 (18 : Fin 32) = out := by rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s2_0]
  have hcb2 : P + BitVec.ofNat 32 0x50 + 0xFFFF1000 + 0xFFFFF868 = siBsub P := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  obtain ⟨p2, cp2, w2, K2, a0_2, a1_2, sp2, fr2, mem2⟩ := si_round (K := (20 : Fin 32)) (i := 2)
    w1 (codeS env.code env.sSC Ip1) (codeS env.bsub env.sSB Ip1) env.hP
    si_at_44 si_at_46 si_at_48 si_at_4a si_at_4c si_at_4e si_at_50 si_at_54 hcb2
    (even_at P env.hP 0x58 (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s0_1 s1_1 sp1 hF
    (aligned_add env.hlp (by decide)) (aligned_add env.hrp (by decide)) hsB
  have Ip2 : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → p2.mem x = m.mem x := fun x hx => by
    rw [mem2 x (bS x hx)]; exact Ip1 x hx
  have s0_2 : reg p2 (8 : Fin 32) = lp := by rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s0_1]
  have s1_2 : reg p2 (9 : Fin 32) = rp := by rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s1_1]
  have s2_2 : reg p2 (18 : Fin 32) = out := by rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s2_1]
  have hcb3 : P + BitVec.ofNat 32 0x64 + 0xFFFF1000 + 0xFFFFF854 = siBsub P := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  obtain ⟨p3, cp3, w3, K3, a0_3, a1_3, sp3, fr3, mem3⟩ := si_round (K := (21 : Fin 32)) (i := 3)
    w2 (codeS env.code env.sSC Ip2) (codeS env.bsub env.sSB Ip2) env.hP
    si_at_58 si_at_5a si_at_5c si_at_5e si_at_60 si_at_62 si_at_64 si_at_68 hcb3
    (even_at P env.hP 0x6C (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s0_2 s1_2 sp2 hF
    (aligned_add env.hlp (by decide)) (aligned_add env.hrp (by decide)) hsB
  have Ip3 : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → p3.mem x = m.mem x := fun x hx => by
    rw [mem3 x (bS x hx)]; exact Ip2 x hx
  have s0_3 : reg p3 (8 : Fin 32) = lp := by rw [fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s0_2]
  have s1_3 : reg p3 (9 : Fin 32) = rp := by rw [fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s1_2]
  have s2_3 : reg p3 (18 : Fin 32) = out := by rw [fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s2_2]
  have hcb4 : P + BitVec.ofNat 32 0x78 + 0xFFFF1000 + 0xFFFFF840 = siBsub P := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  obtain ⟨p4, cp4, w4, K4, a0_4, a1_4, sp4, fr4, mem4⟩ := si_round (K := (22 : Fin 32)) (i := 4)
    w3 (codeS env.code env.sSC Ip3) (codeS env.bsub env.sSB Ip3) env.hP
    si_at_6c si_at_6e si_at_70 si_at_72 si_at_74 si_at_76 si_at_78 si_at_7c hcb4
    (even_at P env.hP 0x80 (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s0_3 s1_3 sp3 hF
    (aligned_add env.hlp (by decide)) (aligned_add env.hrp (by decide)) hsB
  have Ip4 : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → p4.mem x = m.mem x := fun x hx => by
    rw [mem4 x (bS x hx)]; exact Ip3 x hx
  have s0_4 : reg p4 (8 : Fin 32) = lp := by rw [fr4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s0_3]
  have s1_4 : reg p4 (9 : Fin 32) = rp := by rw [fr4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s1_3]
  have s2_4 : reg p4 (18 : Fin 32) = out := by rw [fr4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s2_3]
  have hcb5 : P + BitVec.ofNat 32 0x8C + 0xFFFF1000 + 0xFFFFF82C = siBsub P := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  obtain ⟨p5, cp5, w5, K5, a0_5, a1_5, sp5, fr5, mem5⟩ := si_round (K := (24 : Fin 32)) (i := 5)
    w4 (codeS env.code env.sSC Ip4) (codeS env.bsub env.sSB Ip4) env.hP
    si_at_80 si_at_82 si_at_84 si_at_86 si_at_88 si_at_8a si_at_8c si_at_90 hcb5
    (even_at P env.hP 0x94 (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s0_4 s1_4 sp4 hF
    (aligned_add env.hlp (by decide)) (aligned_add env.hrp (by decide)) hsB
  have Ip5 : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → p5.mem x = m.mem x := fun x hx => by
    rw [mem5 x (bS x hx)]; exact Ip4 x hx
  have s0_5 : reg p5 (8 : Fin 32) = lp := by rw [fr5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s0_4]
  have s1_5 : reg p5 (9 : Fin 32) = rp := by rw [fr5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s1_4]
  have s2_5 : reg p5 (18 : Fin 32) = out := by rw [fr5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s2_4]
  have hcb6 : P + BitVec.ofNat 32 0xA0 + 0xFFFF1000 + 0xFFFFF818 = siBsub P := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  obtain ⟨p6, cp6, w6, K6, a0_6, a1_6, sp6, fr6, mem6⟩ := si_round (K := (23 : Fin 32)) (i := 6)
    w5 (codeS env.code env.sSC Ip5) (codeS env.bsub env.sSB Ip5) env.hP
    si_at_94 si_at_96 si_at_98 si_at_9a si_at_9c si_at_9e si_at_a0 si_at_a4 hcb6
    (even_at P env.hP 0xA8 (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s0_5 s1_5 sp5 hF
    (aligned_add env.hlp (by decide)) (aligned_add env.hrp (by decide)) hsB
  have Ip6 : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → p6.mem x = m.mem x := fun x hx => by
    rw [mem6 x (bS x hx)]; exact Ip5 x hx
  have s0_6 : reg p6 (8 : Fin 32) = lp := by rw [fr6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s0_5]
  have s1_6 : reg p6 (9 : Fin 32) = rp := by rw [fr6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s1_5]
  have s2_6 : reg p6 (18 : Fin 32) = out := by rw [fr6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s2_5]
  have hcb7 : P + BitVec.ofNat 32 0xB4 + 0xFFFF1000 + 0xFFFFF804 = siBsub P := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  obtain ⟨p7, cp7, w7, K7, a0_7, a1_7, sp7, fr7, mem7⟩ := si_round (K := (25 : Fin 32)) (i := 7)
    w6 (codeS env.code env.sSC Ip6) (codeS env.bsub env.sSB Ip6) env.hP
    si_at_a8 si_at_aa si_at_ac si_at_ae si_at_b0 si_at_b2 si_at_b4 si_at_b8 hcb7
    (even_at P env.hP 0xBC (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s0_6 s1_6 sp6 hF
    (aligned_add env.hlp (by decide)) (aligned_add env.hrp (by decide)) hsB
  have Ip7 : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → p7.mem x = m.mem x := fun x hx => by
    rw [mem7 x (bS x hx)]; exact Ip6 x hx
  have s0_7 : reg p7 (8 : Fin 32) = lp := by rw [fr7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s0_6]
  have s1_7 : reg p7 (9 : Fin 32) = rp := by rw [fr7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s1_6]
  have s2_7 : reg p7 (18 : Fin 32) = out := by rw [fr7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s2_6]
  have hcb8 : P + BitVec.ofNat 32 0xC8 + 0xFFFF0000 + 0x7F0 = siBsub P := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  obtain ⟨p8, cp8, w8, K8, a0_8, a1_8, sp8, fr8, mem8⟩ := si_round (K := (26 : Fin 32)) (i := 8)
    w7 (codeS env.code env.sSC Ip7) (codeS env.bsub env.sSB Ip7) env.hP
    si_at_bc si_at_be si_at_c0 si_at_c2 si_at_c4 si_at_c6 si_at_c8 si_at_cc hcb8
    (even_at P env.hP 0xD0 (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s0_7 s1_7 sp7 hF
    (aligned_add env.hlp (by decide)) (aligned_add env.hrp (by decide)) hsB
  have Ip8 : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → p8.mem x = m.mem x := fun x hx => by
    rw [mem8 x (bS x hx)]; exact Ip7 x hx
  have s0_8 : reg p8 (8 : Fin 32) = lp := by rw [fr8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s0_7]
  have s1_8 : reg p8 (9 : Fin 32) = rp := by rw [fr8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s1_7]
  have s2_8 : reg p8 (18 : Fin 32) = out := by rw [fr8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s2_7]
  rw [opW env.sLS _ I8 1 (by decide), opW env.sRS _ I8 1 (by decide)] at a0_1 a1_1
  rw [opW env.sLS _ Ip1 2 (by decide), opW env.sRS _ Ip1 2 (by decide)] at a0_2 a1_2
  rw [opW env.sLS _ Ip2 3 (by decide), opW env.sRS _ Ip2 3 (by decide)] at a0_3 a1_3
  rw [opW env.sLS _ Ip3 4 (by decide), opW env.sRS _ Ip3 4 (by decide)] at a0_4 a1_4
  rw [opW env.sLS _ Ip4 5 (by decide), opW env.sRS _ Ip4 5 (by decide)] at a0_5 a1_5
  rw [opW env.sLS _ Ip5 6 (by decide), opW env.sRS _ Ip5 6 (by decide)] at a0_6 a1_6
  rw [opW env.sLS _ Ip6 7 (by decide), opW env.sRS _ Ip6 7 (by decide)] at a0_7 a1_7
  rw [opW env.sLS _ Ip7 8 (by decide), opW env.sRS _ Ip7 8 (by decide)] at a0_8 a1_8
  have k19 : reg p8 (19 : Fin 32) = reg n8 a0 := by rw [fr8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), K1]
  have k20 : reg p8 (20 : Fin 32) = reg p1 a0 := by rw [fr8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), K2]
  have k21 : reg p8 (21 : Fin 32) = reg p2 a0 := by rw [fr8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), K3]
  have k22 : reg p8 (22 : Fin 32) = reg p3 a0 := by rw [fr8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), K4]
  have k24 : reg p8 (24 : Fin 32) = reg p4 a0 := by rw [fr8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), K5]
  have k23 : reg p8 (23 : Fin 32) = reg p5 a0 := by rw [fr8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), fr7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), K6]
  have k25 : reg p8 (25 : Fin 32) = reg p6 a0 := by rw [fr8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), K7]
  have k26 : reg p8 (26 : Fin 32) = reg p7 a0 := by rw [K8]
  have wl : wordsAt m.mem lp 9 = [memLoad32 m.mem (lp + BitVec.ofNat 32 (4 * 0)), memLoad32 m.mem (lp + BitVec.ofNat 32 (4 * 1)), memLoad32 m.mem (lp + BitVec.ofNat 32 (4 * 2)), memLoad32 m.mem (lp + BitVec.ofNat 32 (4 * 3)), memLoad32 m.mem (lp + BitVec.ofNat 32 (4 * 4)), memLoad32 m.mem (lp + BitVec.ofNat 32 (4 * 5)), memLoad32 m.mem (lp + BitVec.ofNat 32 (4 * 6)), memLoad32 m.mem (lp + BitVec.ofNat 32 (4 * 7)), memLoad32 m.mem (lp + BitVec.ofNat 32 (4 * 8))] := rfl
  have wr : wordsAt m.mem rp 9 = [memLoad32 m.mem (rp + BitVec.ofNat 32 (4 * 0)), memLoad32 m.mem (rp + BitVec.ofNat 32 (4 * 1)), memLoad32 m.mem (rp + BitVec.ofNat 32 (4 * 2)), memLoad32 m.mem (rp + BitVec.ofNat 32 (4 * 3)), memLoad32 m.mem (rp + BitVec.ofNat 32 (4 * 4)), memLoad32 m.mem (rp + BitVec.ofNat 32 (4 * 5)), memLoad32 m.mem (rp + BitVec.ofNat 32 (4 * 6)), memLoad32 m.mem (rp + BitVec.ofNat 32 (4 * 7)), memLoad32 m.mem (rp + BitVec.ofNat 32 (4 * 8))] := rfl
  rw [← w0a0] at w0a1
  rw [← a0_1] at a1_1
  rw [← a0_2] at a1_2
  rw [← a0_3] at a1_3
  rw [← a0_4] at a1_4
  rw [← a0_5] at a1_5
  rw [← a0_6] at a1_6
  rw [← a0_7] at a1_7
  rw [← a0_8] at a1_8
  have hbc : bchain (wordsAt m.mem lp 9) (wordsAt m.mem rp 9) 0 = ([reg n8 a0, reg p1 a0, reg p2 a0, reg p3 a0, reg p4 a0, reg p5 a0, reg p6 a0, reg p7 a0, reg p8 a0], reg p8 a1) := by
    rw [wl, wr]
    simp only [bchain]
    rw [← w0a0, ← w0a1, ← a0_1, ← a1_1, ← a0_2, ← a1_2, ← a0_3, ← a1_3, ← a0_4, ← a1_4, ← a0_5, ← a1_5, ← a0_6, ← a1_6, ← a0_7, ← a1_7, ← a0_8, ← a1_8]
  have zp : reg p8 0 = 0 := w8.zero
  have s2v : reg p8 (18 : Fin 32) = out := s2_8
  have spv : reg p8 sp = sp0 + 0xFFFFFFD0 := sp8
  have ok : BlockOk P subInnerCode.length siAddBlock (p8.mem, reg p8) :=
    siAdd_ok s2v env.hout env.sOC
  have J : ∀ x, Sep (sp0 + 0xFFFFFFD0 + 0xFFFFFFFC) 4 x 1 → p8.mem x = M5 x := fun x hx =>
    (mem8 x hx).trans ((mem7 x hx).trans ((mem6 x hx).trans ((mem5 x hx).trans ((mem4 x hx).trans ((mem3 x hx).trans ((mem2 x hx).trans ((mem1 x hx).trans (mem0 x hx))))))))
  obtain ⟨m9, c9, u9⟩ := St.block siAddBlock w8 (codeS env.code env.sSC Ip8) siAddBlock_end ok
  obtain ⟨Mf, hMf⟩ : ∃ Mf, (runBlock siAddBlock (p8.mem, reg p8)).1 = Mf := ⟨_, rfl⟩
  obtain ⟨gf, hgf⟩ : ∃ gf, (runBlock siAddBlock (p8.mem, reg p8)).2 = gf := ⟨_, rfl⟩
  rw [hMf, hgf] at u9
  have eMf : Mf = storeWords out p8.mem 0 (addBack (reg p8 (19 : Fin 32)) (reg p8 (20 : Fin 32))
      (reg p8 (21 : Fin 32)) (reg p8 (22 : Fin 32)) (reg p8 (24 : Fin 32)) (reg p8 (23 : Fin 32))
      (reg p8 (25 : Fin 32)) (reg p8 (26 : Fin 32)) (reg p8 a1) ++ [reg p8 a1]) := by
    rw [← hMf]; exact siAdd_mem s2v
  have gk : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ (8 : Fin 32) → q ≠ (19 : Fin 32) →
      q ≠ (20 : Fin 32) → q ≠ (21 : Fin 32) → q ≠ (22 : Fin 32) → q ≠ (23 : Fin 32) → q ≠ (24 : Fin 32) →
      q ≠ (25 : Fin 32) → q ≠ (26 : Fin 32) → gf q = reg p8 q := by
    rw [← hgf]; exact siAdd_regs zp
  have gsp : gf sp = sp0 + 0xFFFFFFD0 := by
    rw [gk sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), spv]
  -- memory after the block: the result's words, and the stack as at the add-back
  have outS : ∀ x, Sep out 36 x 1 → Mf x = p8.mem x := fun x hx => by
    rw [eMf]; exact storeWords_outside _ 0 _ (by
      rw [add_ofNat_zero]; exact hx.sub (c := 0) (l := 4 * 9) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
  have IMf : ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → Sep out 36 x 1 → Mf x = m.mem x := fun x hS hO => by
    rw [outS x hO]; exact Ip8 x hS
  have codeMf : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep (sp0 + 0xFFFFFFCC) 0x34 b code.length →
      Sep out 36 b code.length → CodeIn Mf b code := fun hc hs ho i hi => by
    have h1 : Sep (sp0 + 0xFFFFFFCC) 0x34 (_ + BitVec.ofNat 32 i) 1 := hs.subR (c := i) (l := 1) (by omega)
    have h2 : Sep out 36 (_ + BitVec.ofNat 32 i) 1 := ho.subR (c := i) (l := 1) (by omega)
    rw [IMf _ h1 h2]
    exact hc i hi
  have cMf := codeMf env.code env.sSC env.sOC
  have hpsp : ∀ p ∈ siPs, p.1 ≠ sp := by decide
  obtain ⟨m10, c10, u10⟩ := St.block (restoreBlock siPs) u9 cMf siRestore_end
    (restoreBlock_ok Mf (sp0 + 0xFFFFFFD0) siPs gf gsp hpsp fun q hq => by
      simp only [siPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hF (by decide))
  simp only [restoreBlock_run Mf (sp0 + 0xFFFFFFD0) siPs gf gsp hpsp] at u10
  have rsp : restoreRegs Mf (sp0 + 0xFFFFFFD0) gf siPs sp = sp0 + 0xFFFFFFD0 := by
    rw [restoreRegs_sp _ _ _ _ hpsp]; exact gsp
  obtain ⟨m11, d11, u11⟩ := u10.lw cMf si_at_148 (off' := 0x14A) (by decide)
    (by rw [rsp]; exact aligned_add hF (k := 8) (by decide))
  obtain ⟨m12, d12, u12⟩ := u11.lw cMf si_at_14a (off' := 0x14C) (by decide)
    (by simp +decide only [upd, ↓reduceIte]; rw [rsp]; exact aligned_add hF (k := 4) (by decide))
  obtain ⟨m13, d13, u13⟩ := u12.lw cMf si_at_14c (off' := 0x14E) (by decide)
    (by simp +decide only [upd, ↓reduceIte]; rw [rsp, add_lit_zero]; exact hF)
  obtain ⟨m14, d14, u14⟩ := u13.aluImm cMf si_at_14e (off' := 0x150) (by decide)
  obtain ⟨m15, d15, pc15, mem15, regs15⟩ := u14.jalr cMf si_at_150
  have eM5 : M5 = memStore32 (memStore32 (memStore32 (saveMem m.mem (sp0 + 0xFFFFFFD0)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0)) siPs) (sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 8)
      (reg m2 24)) (sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 4) (reg m2 25)) (sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 0)
      (reg m2 26) := by rw [← hM5, ← hM4, ← hM3]; rfl
  have Mf5 : ∀ c, c + 4 ≤ 0x30 → memLoad32 Mf (sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 c) =
      memLoad32 M5 (sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 c) := fun c hc => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]
    have e : sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 (c + j) = sp0 + 0xFFFFFFCC + BitVec.ofNat 32 (4 + (c + j)) := by
      rw [F_eq, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
    rw [outS _ (by rw [e]; exact env.sOS.subR (c := 4 + (c + j)) (l := 1) (by omega)), J _ (by
      rw [e, Fm4]
      have := sep_offsets (sp0 + 0xFFFFFFCC) (c := 0) (n := 4) (d := 4 + (c + j)) (k := 1) (.inl (by omega))
        (by decide) (by omega)
      rwa [add_ofNat_zero] at this)]
  have g1v : ∀ q, q ≠ sp → upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0) q = reg m q := fun q hq => updz hz hq
  have slot : ∀ c (q : Fin 32), (q, c) ∈ [(ra, 0x2C), ((8 : Fin 32), 0x28), ((9 : Fin 32), 0x24),
      ((18 : Fin 32), 0x20), ((19 : Fin 32), 0x1C), ((20 : Fin 32), 0x18), ((21 : Fin 32), 0x14),
      ((22 : Fin 32), 0x10), ((23 : Fin 32), 0xC), ((24 : Fin 32), 8), ((25 : Fin 32), 4), ((26 : Fin 32), 0)] →
      memLoad32 Mf (sp0 + 0xFFFFFFD0 + BitVec.ofNat 32 c) = reg m q := by
    intro c q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · rw [Mf5 _ (by decide), eM5]
      simp only [saveMem]
      simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
      first
      | exact g1v _ (by decide)
      | exact r2 _ (by decide)
  have hwo : out.toNat + 36 ≤ 2 ^ 32 := env.hwrap.1
  have outw : wordsAt Mf out 8 = addBack (reg p8 (19 : Fin 32)) (reg p8 (20 : Fin 32)) (reg p8 (21 : Fin 32))
      (reg p8 (22 : Fin 32)) (reg p8 (24 : Fin 32)) (reg p8 (23 : Fin 32)) (reg p8 (25 : Fin 32))
      (reg p8 (26 : Fin 32)) (reg p8 a1) := by
    rw [eMf]
    show [memLoad32 _ (out + BitVec.ofNat 32 (4 * 0)), memLoad32 _ (out + BitVec.ofNat 32 (4 * 1)),
      memLoad32 _ (out + BitVec.ofNat 32 (4 * 2)), memLoad32 _ (out + BitVec.ofNat 32 (4 * 3)),
      memLoad32 _ (out + BitVec.ofNat 32 (4 * 4)), memLoad32 _ (out + BitVec.ofNat 32 (4 * 5)),
      memLoad32 _ (out + BitVec.ofNat 32 (4 * 6)), memLoad32 _ (out + BitVec.ofNat 32 (4 * 7))] = _
    rw [storeWords_load hwo _ 0 _ 0 (by decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide),
      storeWords_load hwo _ 0 _ 1 (by decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide),
      storeWords_load hwo _ 0 _ 2 (by decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide),
      storeWords_load hwo _ 0 _ 3 (by decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide),
      storeWords_load hwo _ 0 _ 4 (by decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide),
      storeWords_load hwo _ 0 _ 5 (by decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide),
      storeWords_load hwo _ 0 _ 6 (by decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide),
      storeWords_load hwo _ 0 _ 7 (by decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide)]
    rfl
  have outm : memLoad32 Mf (out + 32) = reg p8 a1 := by
    rw [eMf]
    exact storeWords_load hwo _ 0 _ 8 (by decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide) (by rw [List.length_append, addBack_length, List.length_singleton]; decide)
  -- the values
  have hbv := bchain_val (wordsAt m.mem lp 9) (wordsAt m.mem rp 9) 0 rfl (.inl rfl)
  rw [hbc] at hbv
  obtain ⟨hv, hmask0⟩ := hbv
  have hmask : reg p8 a1 = 0 ∨ reg p8 a1 = 0xFFFFFFFF := hmask0
  rw [limbVal9, wordsAt_length] at hv
  have hab := addBack_val (reg p8 (19 : Fin 32)) (reg p8 (20 : Fin 32)) (reg p8 (21 : Fin 32))
    (reg p8 (22 : Fin 32)) (reg p8 (24 : Fin 32)) (reg p8 (23 : Fin 32)) (reg p8 (25 : Fin 32))
    (reg p8 (26 : Fin 32)) (reg p8 a1) hmask
  rw [k19, k20, k21, k22, k24, k23, k25, k26] at hab outw
  obtain ⟨sf, sc⟩ := sub_fin_gen (limbVal [reg n8 a0, reg p1 a0, reg p2 a0, reg p3 a0, reg p4 a0, reg p5 a0,
      reg p6 a0, reg p7 a0]) (reg p8 a0).toNat (limbVal (wordsAt m.mem lp 9)) (limbVal (wordsAt m.mem rp 9))
      (maskBit (reg p8 a1))
    (limbVal_lt _) (maskBit_le1 _) (by rw [show maskBit (0 : Word) = 0 from rfl] at hv; omega) (reg p8 a0).isLt
  have hite : (if reg p8 a1 = 0 then 0 else p256) = (if maskBit (reg p8 a1) = 0 then 0 else p256) := by
    rcases hmask with h | h <;> rw [h] <;> rfl
  -- registers kept from entry
  have keepAll : ∀ q, siWr q = false → reg p8 q = reg m q := fun q hq => by
    obtain ⟨nra, nsp, _, n8', n9', na0, na1, na2, na3, na4, na5, n18, n19, n20, n21, n22, n23, n24, n25, n26⟩ :=
      siWr_ne q hq
    rw [fr8 q n26 na0 na1 na2 na3 na4 nra, fr7 q n25 na0 na1 na2 na3 na4 nra, fr6 q n23 na0 na1 na2 na3 na4 nra,
      fr5 q n24 na0 na1 na2 na3 na4 nra, fr4 q n22 na0 na1 na2 na3 na4 nra, fr3 q n21 na0 na1 na2 na3 na4 nra,
      fr2 q n20 na0 na1 na2 na3 na4 nra, fr1 q n19 na0 na1 na2 na3 na4 nra, fr0 q na0 na1 na2 na3 na4 nra,
      r7 q n9' n8' na2 na1 n18 na0, r2 q nsp]
  refine ⟨m15, .cons d1 (c2.trans (.cons d3 (.cons d4 (.cons d5 (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (c8.trans (cp1.trans (cp2.trans (cp3.trans (cp4.trans (cp5.trans (cp6.trans (cp7.trans (cp8.trans (c9.trans (c10.trans (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.single d15))))))))))))))))))))))))))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc15]
    simp only [restoreRegs]
    simp +decide only [upd, ↓reduceIte]
    rw [slot 0x2C ra (by simp), hra, add_lit_zero, hret]
  · rw [regs15]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [rsp]; rw [BitVec.add_assoc]; exact BitVec.add_zero _
  · intro q q0 q1 q2 q3 q4 q5 qt
    rw [regs15]
    have cat := (by decide : ∀ q : Fin 32, q = sp ∨ q = (24 : Fin 32) ∨ q = (25 : Fin 32) ∨ q = (26 : Fin 32) ∨
      q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨
      q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨ q = (23 : Fin 32) ∨ q = a0 ∨ q = a1 ∨ q = a2 ∨ q = a3 ∨ q = a4 ∨
      q = a5 ∨ q = t0 ∨ siWr q = false) q
    rcases cat with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; simp +decide only [upd, ↓reduceIte, aluEval]
      rw [rsp, hsp, BitVec.add_assoc]; exact BitVec.add_zero _
    · subst h; simp +decide only [upd, ↓reduceIte]; rw [rsp]; exact slot 8 _ (by simp)
    · subst h; simp +decide only [upd, ↓reduceIte]; rw [rsp]; exact slot 4 _ (by simp)
    · subst h; simp +decide only [upd, ↓reduceIte]; rw [rsp]; exact slot 0 _ (by simp)
    · subst h; simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]; exact slot 0x2C _ (by simp)
    · subst h; simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]; exact slot 0x28 _ (by simp)
    · subst h; simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]; exact slot 0x24 _ (by simp)
    · subst h; simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]; exact slot 0x20 _ (by simp)
    · subst h; simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]; exact slot 0x1C _ (by simp)
    · subst h; simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]; exact slot 0x18 _ (by simp)
    · subst h; simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]; exact slot 0x14 _ (by simp)
    · subst h; simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]; exact slot 0x10 _ (by simp)
    · subst h; simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]; exact slot 0xC _ (by simp)
    · exact absurd h q0
    · exact absurd h q1
    · exact absurd h q2
    · exact absurd h q3
    · exact absurd h q4
    · exact absurd h q5
    · exact absurd h qt
    · obtain ⟨nra, nsp, _, n8', n9', na0, na1, na2, na3, na4, na5, n18, n19, n20, n21, n22, n23, n24, n25, n26⟩ :=
        siWr_ne q h
      have q0' : q.val ≠ 0 ∨ q = 0 := by
        by_cases hq : q.val = 0
        · exact .inr (Fin.ext hq)
        · exact .inl hq
      rcases q0' with hq | hq
      · simp only [restoreRegs]
        simp [upd, hq, nra, nsp, n8', n9', n18, n19, n20, n21, n22, n23, n24, n25, n26]
        rw [gk q na0 na1 na2 na3 na4 na5 n8' n19 n20 n21 n22 n23 n24 n25 n26]
        exact keepAll q h
      · subst hq; simp [upd, hz]
  · rw [mem15, outw, hab, hite]; exact sf
  · rw [mem15, outm]
    rcases hmask with h | h
    · rw [h, ite_eq_right (fun hl => by have := sc.mpr hl; rw [h] at this; exact absurd this (by decide))]
    · rw [h, ite_eq_left (sc.mp (by rw [h]; rfl))]
  · intro x hS hO; rw [mem15]; exact IMf x hS hO

/-- **The compiled `sub_inner`** with the P-256 modulus as its second operand,
as `FieldElement::multiply` and `field_impl::add` call it: it stores
`subRes L`, which is `L - p` when `L` is at least `p` and `L` otherwise, and
the borrow mask, all ones exactly when `L < p`. -/
theorem subInner_correct (m : Machine) {P sp0 out lp rp retAddr : Word}
    (env : SIEnv m.mem P sp0 out lp rp) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = lp)
    (ha2 : reg m a2 = rp) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ t0 → reg m' q = reg m q) ∧
      limbVal (wordsAt m'.mem out 8) = subRes (limbVal (wordsAt m.mem lp 9)) ∧
      memLoad32 m'.mem (out + 32) = (if limbVal (wordsAt m.mem lp 9) < p256 then 0xFFFFFFFF else 0) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFCC) 0x34 x 1 → Sep out 36 x 1 → m'.mem x = m.mem x := by
  obtain ⟨m', c, pc, sp, regs, val, mask, frame⟩ := subInner_gen m env.toG hpc ha0 ha1 ha2 hra hret hsp
  rw [env.pval, pLimbs_val, subGen_p] at val
  rw [env.pval, pLimbs_val] at mask
  exact ⟨m', c, pc, sp, regs, val, mask, frame⟩

end C3.RV32
