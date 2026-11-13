import C3BootProofs.Proofs.Sha512Sched

/-!
# `compress512`: the 80 rounds

The round loop runs from 0x22C to 0x376. Before round `t` the working
variables are in registers, the round constants' pointer is in `s9`, and
`W[t]`'s slot is in `t5`. `s5_rounds_from` runs the loop to its exit.
-/

namespace C3.RV32

open C3.Image

abbrev s5K : Word := BitVec.ofNat 32 sha512KAddress

set_option maxRecDepth 100000 in
theorem sha512KData_length : sha512KData.length = 640 := rfl

theorem kbyte {M : Word → BitVec 8} (hk : CodeIn M s5K sha512KData) {c : Nat} (hc : c < 640) :
    M (s5K + BitVec.ofNat 32 c) = byteAt sha512KData c :=
  hk c (by rw [sha512KData_length]; exact hc)

set_option maxRecDepth 100000 in
/-- The round constants as the image stores them: each word's low half,
then its high half. -/
theorem s5K_words {M : Word → BitVec 8} (hk : CodeIn M s5K sha512KData) {t : Nat} (ht : t < 80) :
    memLoad32 M (s5K + BitVec.ofNat 32 (8 * t)) = lo64 Sha512.k[t]! ∧
      memLoad32 M (s5K + BitVec.ofNat 32 (8 * t) + 4) = hi64 Sha512.k[t]! := by
  have hl : ∀ t : Fin 80, (byteAt sha512KData (8 * t.val + 3) ++ byteAt sha512KData (8 * t.val + 2) ++
      byteAt sha512KData (8 * t.val + 1) ++ byteAt sha512KData (8 * t.val)) = lo64 Sha512.k[t.val]! := by
    decide +kernel
  have hh : ∀ t : Fin 80, (byteAt sha512KData (8 * t.val + 7) ++ byteAt sha512KData (8 * t.val + 6) ++
      byteAt sha512KData (8 * t.val + 5) ++ byteAt sha512KData (8 * t.val + 4)) = hi64 Sha512.k[t.val]! := by
    decide +kernel
  have b : ∀ c, c < 8 → M (s5K + BitVec.ofNat 32 (8 * t) + BitVec.ofNat 32 c) = byteAt sha512KData (8 * t + c) :=
    fun c hc => by rw [add_ofNat_assoc]; exact kbyte hk (by omega)
  have e : ∀ c, c < 8 → ∀ x : Word, x = s5K + BitVec.ofNat 32 (8 * t) + BitVec.ofNat 32 c →
      M x = byteAt sha512KData (8 * t + c) := fun c hc x hx => by rw [hx]; exact b c hc
  refine ⟨?_, ?_⟩
  · unfold memLoad32
    rw [e 3 (by omega) (s5K + BitVec.ofNat 32 (8 * t) + 3) rfl, e 2 (by omega) (s5K + BitVec.ofNat 32 (8 * t) + 2) rfl, e 1 (by omega) (s5K + BitVec.ofNat 32 (8 * t) + 1) rfl,
      e 0 (by omega) (s5K + BitVec.ofNat 32 (8 * t)) (add_ofNat_zero _).symm]
    exact hl ⟨t, ht⟩
  · unfold memLoad32
    rw [e 7 (by omega) (s5K + BitVec.ofNat 32 (8 * t) + 4 + 3) (by rw [BitVec.add_assoc]; rfl), e 6 (by omega) (s5K + BitVec.ofNat 32 (8 * t) + 4 + 2) (by rw [BitVec.add_assoc]; rfl),
      e 5 (by omega) (s5K + BitVec.ofNat 32 (8 * t) + 4 + 1) (by rw [BitVec.add_assoc]; rfl), e 4 (by omega) (s5K + BitVec.ofNat 32 (8 * t) + 4) rfl]
    exact hh ⟨t, ht⟩


theorem s5K_al (t : Nat) : (s5K + BitVec.ofNat 32 (8 * t)).toNat % 4 = 0 :=
  aligned_add (show s5K.toNat % 4 = 0 from rfl) (by omega)

/-- The round loop's head at 0x22C: `a` and `e` into the registers the round
reads. -/
def s5RHead : List BInstr :=
  [.alu .add (24 : Fin 32) x0 a0, .alu .add (31 : Fin 32) x0 (23 : Fin 32), .alu .add (22 : Fin 32) x0 a3,
   .alu .add (27 : Fin 32) x0 a2]

section
set_option maxRecDepth 100000
theorem s5RHead_end : blockEnd sha512CompressCode 0x22C s5RHead = some 0x234 := by decide
theorem s5Round_end : blockEnd sha512CompressCode 0x238 s5Round = some 0x374 := by decide
end

set_option maxRecDepth 100000 in
theorem s5Round_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h25 : (f 25).toNat % 4 = 0) (h30 : (f 30).toNat % 4 = 0) : BlockOk base len s5Round (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, s5Round, upd, ↓reduceIte, and_true, true_and]
  rw [show aluEval .add 0 (f 25) = f 25 from BitVec.zero_add _, show aluEval .add 0 (f 30) = f 30 from BitVec.zero_add _]
  exact ⟨aligned_add h25 (k := 0) (by decide), aligned_add h25 (k := 4) (by decide),
    aligned_add h30 (k := 0) (by decide), aligned_add h30 (k := 4) (by decide)⟩

/-- The registers the round loop leaves alone. -/
def s5RKeep (q : Fin 32) : Bool := q.val ∈ [2, 3, 4]

set_option maxRecDepth 100000 in
theorem s5RKeep_dst : ∀ q, s5RKeep q = true → q ∉ s5Round.filterMap BInstr.dst := by decide

/-- What holds at 0x22C before round `t`: the working variables after `t`
rounds in registers, `a` in `s7` and `a0` and `e` in `a2` and `a3`. -/
structure S5R (P F : Word) (w : Nat → Sha512.W64) (hv : Sha512.V8) (g : Fin 32 → Word) (t : Nat)
    (M : Word → BitVec 8) (m : Machine) : Prop where
  st : St M P m 0x22C (reg m)
  code : CodeIn M P sha512CompressCode
  kd : CodeIn M s5K sha512KData
  r29 : reg m 29 = BitVec.ofNat 32 (80 - t)
  r25 : reg m 25 = s5K + BitVec.ofNat 32 (8 * t)
  r30 : reg m 30 = wslot F t
  al : reg m 23 = lo64 (Sha512.vs w hv t).a
  ah : reg m a0 = hi64 (Sha512.vs w hv t).a
  bl : reg m 28 = lo64 (Sha512.vs w hv t).b
  bh : reg m 7 = hi64 (Sha512.vs w hv t).b
  cl : reg m 18 = lo64 (Sha512.vs w hv t).c
  ch : reg m 26 = hi64 (Sha512.vs w hv t).c
  dl : reg m 19 = lo64 (Sha512.vs w hv t).d
  dh : reg m 20 = hi64 (Sha512.vs w hv t).d
  el : reg m a2 = lo64 (Sha512.vs w hv t).e
  eh : reg m a3 = hi64 (Sha512.vs w hv t).e
  fl : reg m 6 = lo64 (Sha512.vs w hv t).f
  fh : reg m 5 = hi64 (Sha512.vs w hv t).f
  gl : reg m a7 = lo64 (Sha512.vs w hv t).g
  gh : reg m 21 = hi64 (Sha512.vs w hv t).g
  hl : reg m ra = lo64 (Sha512.vs w hv t).h
  hh : reg m a6 = hi64 (Sha512.vs w hv t).h
  win : ∀ s, s < 80 → WIn M F w s
  keep : ∀ q, s5RKeep q = true → reg m q = g q

theorem beq_pos {k : Nat} (h0 : 0 < k) (h1 : k < 2 ^ 32) : branchTaken .beq (BitVec.ofNat 32 k) 0 = false := by
  unfold branchTaken
  rw [beq_eq_false_iff_ne]
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1] at this
  exact absurd this (by show k ≠ 0; omega)

theorem wslot_succ (F : Word) (t : Nat) : wslot F t + 0x8 = wslot F (t + 1) := by
  unfold wslot; rw [show (0x8 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]; congr 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Round `t`, from 0x22C back to 0x22C. -/
theorem s5_round {P F : Word} {w : Nat → Sha512.W64} {hv : Sha512.V8} {g : Fin 32 → Word} {t : Nat}
    {M : Word → BitVec 8} {m : Machine} (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (I : S5R P F w hv g t M m) (ht : t < 80) :
    ∃ m', Steps m m' ∧ S5R P F w hv g (t + 1) M m' := by
  have z : reg m x0 = 0 := I.st.zero
  obtain ⟨m1, c1, u1⟩ := St.block s5RHead I.st I.code s5RHead_end (by simp [BlockOk, BInstr.ok, s5RHead])
  simp only [runBlock, BInstr.run, s5RHead] at u1
  have R1 : ∀ q, q.val ≠ 0 → q ≠ 24 → q ≠ 31 → q ≠ 22 → q ≠ 27 → reg m1 q = reg m q := fun q h0 h1 h2 h3 h4 => by
    rw [u1.regs]; simp only [upd_app, h0, h1, h2, h3, h4, ite_false]
  have x24 : reg m1 24 = hi64 (Sha512.vs w hv t).a := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, z]; rw [I.ah]; exact BitVec.zero_add _
  have x31 : reg m1 31 = lo64 (Sha512.vs w hv t).a := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, z]; rw [I.al]; exact BitVec.zero_add _
  have x22 : reg m1 22 = hi64 (Sha512.vs w hv t).e := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, z]; rw [I.eh]; exact BitVec.zero_add _
  have x27 : reg m1 27 = lo64 (Sha512.vs w hv t).e := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, z]; rw [I.el]; exact BitVec.zero_add _
  obtain ⟨m2, d2, u2⟩ := u1.self.notTaken I.code 0x238 s5_at_234 (by decide) (by
    rw [R1 29 (by decide) (by decide) (by decide) (by decide) (by decide), I.r29, u1.self.zero]
    exact beq_pos (by omega) (by omega))
  have k25 : reg m1 25 = s5K + BitVec.ofNat 32 (8 * t) := by
    rw [R1 25 (by decide) (by decide) (by decide) (by decide) (by decide), I.r25]
  have k30 : reg m1 30 = wslot F t := by
    rw [R1 30 (by decide) (by decide) (by decide) (by decide) (by decide), I.r30]
  have hK := s5K_words I.kd ht
  obtain ⟨Ea, Ea', Ee, Ee', Eg, Eg', Ef, Ef', Ee2, Ee2', Ec, Ec', Eb, Eb', Ea2, Ea2', E25, E30, E29⟩ :=
    s5Round_run (M := M) (f := reg m1) (v := Sha512.vs w hv t) (w := w) (t := t)
      (kp := reg m1 25) (wp := reg m1 30) x31 x24
      (by rw [R1 28 (by decide) (by decide) (by decide) (by decide) (by decide), I.bl])
      (by rw [R1 7 (by decide) (by decide) (by decide) (by decide) (by decide), I.bh])
      (by rw [R1 18 (by decide) (by decide) (by decide) (by decide) (by decide), I.cl])
      (by rw [R1 26 (by decide) (by decide) (by decide) (by decide) (by decide), I.ch])
      (by rw [R1 19 (by decide) (by decide) (by decide) (by decide) (by decide), I.dl])
      (by rw [R1 20 (by decide) (by decide) (by decide) (by decide) (by decide), I.dh])
      x27 x22
      (by rw [R1 6 (by decide) (by decide) (by decide) (by decide) (by decide), I.fl])
      (by rw [R1 5 (by decide) (by decide) (by decide) (by decide) (by decide), I.fh])
      (by rw [R1 a7 (by decide) (by decide) (by decide) (by decide) (by decide), I.gl])
      (by rw [R1 21 (by decide) (by decide) (by decide) (by decide) (by decide), I.gh])
      (by rw [R1 ra (by decide) (by decide) (by decide) (by decide) (by decide), I.hl])
      (by rw [R1 a6 (by decide) (by decide) (by decide) (by decide) (by decide), I.hh])
      rfl rfl
      (by rw [k25, add_lit_zero]; exact hK.1) (by rw [k25]; exact hK.2)
      (by rw [k30, add_lit_zero]; exact (I.win t ht).1) (by rw [k30]; exact (I.win t ht).2)
  obtain ⟨m3, c3, u3⟩ := St.block s5Round u2 I.code s5Round_end
    (s5Round_ok (by rw [k25]; exact s5K_al t) (by rw [k30]; exact aligned_add hF (by omega)))
  rw [show (runBlock s5Round (M, reg m1)).1 = M from rfl] at u3
  obtain ⟨m4, d4, u4⟩ := u3.jump I.code s5_at_374 (off' := 0x22C) (by decide)
    (pc_even (off' := 0x22C) hP u3.pc (by decide) (by decide))
  have K4 : ∀ q, s5RKeep q = true → (runBlock s5Round (M, reg m1)).2 q = reg m q := fun q hq => by
    rw [runBlock_reg _ M _ q u1.self.zero (s5RKeep_dst q hq)]
    exact R1 q (fun e => pkeep_ne hq (r := 0) rfl (Fin.ext e)) (pkeep_ne hq rfl) (pkeep_ne hq rfl)
      (pkeep_ne hq rfl) (pkeep_ne hq rfl)
  refine ⟨m4, c1.trans (.cons d2 (c3.trans (.cons d4 (.refl _)))), ⟨u4.self, I.code, I.kd, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, I.win, ?_⟩⟩
  · rw [u4.regs, E29, R1 29 (by decide) (by decide) (by decide) (by decide) (by decide), I.r29]
    exact (ofNat_sub1 (by omega) (by omega)).trans (by congr 1)
  · rw [u4.regs, E25, k25, show (0x8 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]; congr 2
  · rw [u4.regs, E30, k30, wslot_succ]
  · rw [u4.regs]; exact Ea
  · rw [u4.regs]; exact Ea'
  · rw [u4.regs]; exact Ea2
  · rw [u4.regs]; exact Ea2'
  · rw [u4.regs]; exact Eb
  · rw [u4.regs]; exact Eb'
  · rw [u4.regs]; exact Ec
  · rw [u4.regs]; exact Ec'
  · rw [u4.regs]; exact Ee
  · rw [u4.regs]; exact Ee'
  · rw [u4.regs]; exact Ee2
  · rw [u4.regs]; exact Ee2'
  · rw [u4.regs]; exact Ef
  · rw [u4.regs]; exact Ef'
  · rw [u4.regs]; exact Eg
  · rw [u4.regs]; exact Eg'
  · intro q hq; rw [u4.regs, K4 q hq, I.keep q hq]

/-- The rounds from round `t` to round 80. -/
theorem s5_rounds_from {P F : Word} {w : Nat → Sha512.W64} {hv : Sha512.V8} {g : Fin 32 → Word}
    (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0) :
    ∀ k t (M : Word → BitVec 8) (m : Machine), t + k = 80 → S5R P F w hv g t M m →
      ∃ m', Steps m m' ∧ S5R P F w hv g 80 M m'
  | 0, t, M, m, h, I => ⟨m, .refl _, by rw [Nat.add_zero] at h; subst h; exact I⟩
  | k + 1, t, M, m, h, I => by
    obtain ⟨m1, c1, I1⟩ := s5_round hP hF I (by omega)
    obtain ⟨m2, c2, I2⟩ := s5_rounds_from hP hF k (t + 1) M m1 (by omega) I1
    exact ⟨m2, c1.trans c2, I2⟩

set_option maxRecDepth 100000 in
/-- After round 80 the loop exits to 0x376, with `a` in `t6` and `s8` and `e`
in `s11` and `s6`. -/
theorem s5_rounds_exit {P F : Word} {w : Nat → Sha512.W64} {hv : Sha512.V8} {g : Fin 32 → Word}
    {M : Word → BitVec 8} {m : Machine} (I : S5R P F w hv g 80 M m) :
    ∃ m', Steps m m' ∧ St M P m' 0x376 (reg m') ∧
      reg m' 31 = lo64 (Sha512.vs w hv 80).a ∧ reg m' 24 = hi64 (Sha512.vs w hv 80).a ∧
      reg m' 28 = lo64 (Sha512.vs w hv 80).b ∧ reg m' 7 = hi64 (Sha512.vs w hv 80).b ∧
      reg m' 18 = lo64 (Sha512.vs w hv 80).c ∧ reg m' 26 = hi64 (Sha512.vs w hv 80).c ∧
      reg m' 19 = lo64 (Sha512.vs w hv 80).d ∧ reg m' 20 = hi64 (Sha512.vs w hv 80).d ∧
      reg m' 27 = lo64 (Sha512.vs w hv 80).e ∧ reg m' 22 = hi64 (Sha512.vs w hv 80).e ∧
      reg m' 6 = lo64 (Sha512.vs w hv 80).f ∧ reg m' 5 = hi64 (Sha512.vs w hv 80).f ∧
      reg m' a7 = lo64 (Sha512.vs w hv 80).g ∧ reg m' 21 = hi64 (Sha512.vs w hv 80).g ∧
      reg m' ra = lo64 (Sha512.vs w hv 80).h ∧ reg m' a6 = hi64 (Sha512.vs w hv 80).h ∧
      ∀ q, s5RKeep q = true → reg m' q = g q := by
  have z : reg m x0 = 0 := I.st.zero
  obtain ⟨m1, c1, u1⟩ := St.block s5RHead I.st I.code s5RHead_end (by simp [BlockOk, BInstr.ok, s5RHead])
  simp only [runBlock, BInstr.run, s5RHead] at u1
  have R1 : ∀ q, q.val ≠ 0 → q ≠ 24 → q ≠ 31 → q ≠ 22 → q ≠ 27 → reg m1 q = reg m q := fun q h0 h1 h2 h3 h4 => by
    rw [u1.regs]; simp only [upd_app, h0, h1, h2, h3, h4, ite_false]
  obtain ⟨m2, d2, u2⟩ := u1.self.taken I.code 0x376 s5_at_234 (by decide) (by
    rw [R1 29 (by decide) (by decide) (by decide) (by decide) (by decide), I.r29, u1.self.zero]; decide)
  refine ⟨m2, c1.trans (.cons d2 (.refl _)), u2.self, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [u2.regs, u1.regs]; simp +decide only [upd_app, ↓reduceIte, z]; rw [I.al]; exact BitVec.zero_add _
  · rw [u2.regs, u1.regs]; simp +decide only [upd_app, ↓reduceIte, z]; rw [I.ah]; exact BitVec.zero_add _
  · rw [u2.regs, R1 28 (by decide) (by decide) (by decide) (by decide) (by decide), I.bl]
  · rw [u2.regs, R1 7 (by decide) (by decide) (by decide) (by decide) (by decide), I.bh]
  · rw [u2.regs, R1 18 (by decide) (by decide) (by decide) (by decide) (by decide), I.cl]
  · rw [u2.regs, R1 26 (by decide) (by decide) (by decide) (by decide) (by decide), I.ch]
  · rw [u2.regs, R1 19 (by decide) (by decide) (by decide) (by decide) (by decide), I.dl]
  · rw [u2.regs, R1 20 (by decide) (by decide) (by decide) (by decide) (by decide), I.dh]
  · rw [u2.regs, u1.regs]; simp +decide only [upd_app, ↓reduceIte, z]; rw [I.el]; exact BitVec.zero_add _
  · rw [u2.regs, u1.regs]; simp +decide only [upd_app, ↓reduceIte, z]; rw [I.eh]; exact BitVec.zero_add _
  · rw [u2.regs, R1 6 (by decide) (by decide) (by decide) (by decide) (by decide), I.fl]
  · rw [u2.regs, R1 5 (by decide) (by decide) (by decide) (by decide) (by decide), I.fh]
  · rw [u2.regs, R1 a7 (by decide) (by decide) (by decide) (by decide) (by decide), I.gl]
  · rw [u2.regs, R1 21 (by decide) (by decide) (by decide) (by decide) (by decide), I.gh]
  · rw [u2.regs, R1 ra (by decide) (by decide) (by decide) (by decide) (by decide), I.hl]
  · rw [u2.regs, R1 a6 (by decide) (by decide) (by decide) (by decide) (by decide), I.hh]
  · intro q hq
    rw [u2.regs, R1 q (fun e => pkeep_ne hq (r := 0) rfl (Fin.ext e)) (pkeep_ne hq rfl) (pkeep_ne hq rfl)
      (pkeep_ne hq rfl) (pkeep_ne hq rfl), I.keep q hq]

end C3.RV32
