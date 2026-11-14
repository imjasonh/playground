import C3BootProofs.Proofs.Sha256LoopBlocks

/-!
# `compress256`, compact backend: the 64 rounds

The round loop runs from 0xD4 to 0x1EA. Before round `t` the working
variables are in registers, `W[t - 16]` to `W[t - 1]` (or `W[0]` to `W[15]`
while `t ≤ 16`) are in the 16-word window at `F + 0x2C`, and a round with
`t ≥ 16` first computes `W[t]` over `W[t - 16]`'s slot. `kc_rounds` runs
the loop from round 0 to its exit.
-/

namespace C3.RV32

open C3.Image

/-- The registers the round loop never writes. -/
def kcLoopKeep (q : Fin 32) : Bool :=
  q.val ∉ [0, 1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 22, 23, 25, 26, 28, 29, 30, 31]

/-- Where the round constants are. -/
abbrev kcK : Word := BitVec.ofNat 32 shaKAddress

/-- What the round loop needs and doesn't change: its code at an even `P`,
an aligned frame `F` apart from the code and the constants. -/
structure KCStatic (P F : Word) : Prop where
  hP : P.toNat % 2 = 0
  hF : F.toNat % 4 = 0
  sFC : Sep F 0xE0 P sha256CompressCode.length
  sFK : Sep F 0xE0 kcK 256

/-- What holds at 0xD4 before round `t`: `M1` and `g` are the memory and
registers when the loop starts. -/
structure KCR (P F : Word) (w : Nat → Word) (hv : Sha256.V8) (g : Fin 32 → Word)
    (M1 : Word → BitVec 8) (t : Nat) (M : Word → BitVec 8) (m : Machine) : Prop where
  st : St M P m 0xD4 (reg m)
  code : CodeIn M P sha256CompressCode
  kd : CodeIn M kcK shaKData
  r8 : reg m 8 = BitVec.ofNat 32 t
  r19 : reg m 19 = 0x10
  r20 : reg m 20 = F + BitVec.ofNat 32 0x2C
  r22 : reg m 22 = F + BitVec.ofNat 32 (0x2C + 4 * t)
  r7 : reg m 7 = kcK + BitVec.ofNat 32 (4 * t)
  va : reg m a2 = (Sha256.vs w hv t).a
  vb : reg m 29 = (Sha256.vs w hv t).b
  vc : reg m a6 = (Sha256.vs w hv t).c
  vd : reg m 25 = (Sha256.vs w hv t).d
  ve : reg m a0 = (Sha256.vs w hv t).e
  vf : reg m 5 = (Sha256.vs w hv t).f
  vg : reg m 17 = (Sha256.vs w hv t).g
  vh : reg m 26 = (Sha256.vs w hv t).h
  win : ∀ s, s < max t 16 → max t 16 ≤ s + 16 → memLoad32 M (kslot F s) = w s
  fr : ∀ x, Sep (F + BitVec.ofNat 32 0x2C) 0x40 x 1 → M x = M1 x
  keep : ∀ q, kcLoopKeep q = true → reg m q = g q

/-- What holds at 0x160 in round `t`, with `W[t]` in `a0`. -/
structure KCMid (P F : Word) (w : Nat → Word) (hv : Sha256.V8) (g : Fin 32 → Word)
    (M1 : Word → BitVec 8) (t : Nat) (M : Word → BitVec 8) (m : Machine) : Prop where
  st : St M P m 0x160 (reg m)
  code : CodeIn M P sha256CompressCode
  kd : CodeIn M kcK shaKData
  r28 : reg m 28 = BitVec.ofNat 32 (t + 1)
  r19 : reg m 19 = 0x10
  r20 : reg m 20 = F + BitVec.ofNat 32 0x2C
  r22 : reg m 22 = F + BitVec.ofNat 32 (0x2C + 4 * t)
  r7 : reg m 7 = kcK + BitVec.ofNat 32 (4 * t)
  wt : reg m a0 = w t
  va : reg m 30 = (Sha256.vs w hv t).a
  vb : reg m 29 = (Sha256.vs w hv t).b
  vc : reg m a6 = (Sha256.vs w hv t).c
  vd : reg m 25 = (Sha256.vs w hv t).d
  ve : reg m 6 = (Sha256.vs w hv t).e
  vf : reg m 5 = (Sha256.vs w hv t).f
  vg : reg m 17 = (Sha256.vs w hv t).g
  vh : reg m 26 = (Sha256.vs w hv t).h
  win : ∀ s, s < max (t + 1) 16 → max (t + 1) 16 ≤ s + 16 → memLoad32 M (kslot F s) = w s
  fr : ∀ x, Sep (F + BitVec.ofNat 32 0x2C) 0x40 x 1 → M x = M1 x
  keep : ∀ q, kcLoopKeep q = true → reg m q = g q

def kcHead : List BInstr :=
  [.aluImm .add (9 : Fin 32) (8 : Fin 32) 0xFFFFFFC0, .alu .add (30 : Fin 32) x0 a2, .alu .add (6 : Fin 32) x0 a0]

set_option maxRecDepth 20000 in
theorem kcHead_end : blockEnd sha256CompressCode 0xD4 kcHead = some 0xDC := by decide

theorem kslot_al {F : Word} (hF : F.toNat % 4 = 0) (n : Nat) : (kslot F n).toNat % 4 = 0 :=
  aligned_add hF (by omega)

theorem kslot_sep {F b : Word} {k : Nat} (h : Sep F 0xE0 b k) (n : Nat) : Sep (kslot F n) 4 b k :=
  h.sub (c := 0x2C + 4 * (n % 16)) (by omega)

theorem kslot_win {F x : Word} (h : Sep (F + BitVec.ofNat 32 0x2C) 0x40 x 1) (n : Nat) : Sep (kslot F n) 4 x 1 := by
  unfold kslot; rw [← add_ofNat_assoc]; exact h.sub (c := 4 * (n % 16)) (by omega)

theorem kslot_mod {F : Word} {a b : Nat} (h : a % 16 = b % 16) : kslot F a = kslot F b := by
  unfold kslot; rw [h]

theorem kslot_store_ne {M : Word → BitVec 8} {F v : Word} {s t : Nat} (h : s % 16 ≠ t % 16) :
    memLoad32 (memStore32 M (kslot F t) v) (kslot F s) = memLoad32 M (kslot F s) :=
  memLoad32_store32_sep (sep_offsets F (by omega) (by omega) (by omega))

theorem kcK_al (t : Nat) : (kcK + BitVec.ofNat 32 (4 * t) + 0).toNat % 4 = 0 := by
  rw [add_lit_zero]; exact aligned_add (show kcK.toNat % 4 = 0 from rfl) (by omega)

theorem beq_lt64 {t : Nat} (ht : t < 64) :
    branchTaken .beq (BitVec.ofNat 32 t + 0xFFFFFFC0) 0 = false := by
  unfold branchTaken
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0xFFFFFFC0 : Word).toNat = 0xFFFFFFC0 from rfl,
    show (0 : Word).toNat = 0 from rfl] at this
  omega

theorem bgeu16 {t : Nat} (ht : t < 64) :
    branchTaken .bgeu (BitVec.ofNat 32 t) 0x10 = decide (16 ≤ t) := by
  unfold branchTaken
  simp only [BitVec.ult, BitVec.toNat_ofNat, show (0x10 : Word).toNat = 16 from rfl]
  rw [Nat.mod_eq_of_lt (by omega)]
  by_cases h : 16 ≤ t
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_le h]

set_option maxRecDepth 20000 in
theorem kcLoopKeep_round : ∀ q, kcLoopKeep q = true → kcRoundKeep q = true := by decide

set_option maxRecDepth 20000 in
theorem kcLoopKeep_sched : ∀ q, kcLoopKeep q = true → kcSchedKeep q = true := by decide

theorem pc_even {P : Word} (hP : P.toNat % 2 = 0) {m : Machine} {o : Word} {off off' : Nat}
    (hpc : m.pc = P + BitVec.ofNat 32 off) (hn : BitVec.ofNat 32 off + o = BitVec.ofNat 32 off')
    (h2 : off' % 2 = 0) : (m.pc + o).getLsbD 0 = false := by
  rw [hpc, BitVec.add_assoc, hn]; exact even_bit0 (even_at P hP off' h2)

theorem upd_kp {p : Fin 32 → Bool} {f : Fin 32 → Word} {rd q : Fin 32} {v : Word} (hq : p q = true)
    (h0 : p 0 = false) (hr : p rd = false) : upd f rd v q = f q :=
  upd_ne (fun e => pkeep_ne hq h0 (Fin.ext e)) (pkeep_ne hq hr)

set_option maxRecDepth 20000 in
theorem kd_store {M : Word → BitVec 8} {a v : Word} (hk : CodeIn M kcK shaKData) (h : Sep a 4 kcK 256) :
    CodeIn (memStore32 M a v) kcK shaKData :=
  hk.store32 h

set_option maxHeartbeats 4000000 in
/-- Round `t` from 0xD4 to 0x160: past the exit test, with `W[t]` in `a0`
and in the window. -/
theorem kc_to_round {P F : Word} {w : Nat → Word} {hv : Sha256.V8} {g : Fin 32 → Word}
    {M1 M : Word → BitVec 8} {t : Nat} {m : Machine} (S : KCStatic P F) (hw : ShaSched w)
    (I : KCR P F w hv g M1 t M m) (ht : t < 64) :
    ∃ m' M', Steps m m' ∧ KCMid P F w hv g M1 t M' m' := by
  obtain ⟨m1, c1, u1⟩ := St.block kcHead I.st I.code kcHead_end (by simp [BlockOk, BInstr.ok, kcHead])
  simp only [runBlock, BInstr.run, kcHead] at u1
  have z1 : reg m1 0 = 0 := u1.self.zero
  have x9 : reg m1 9 = BitVec.ofNat 32 t + 0xFFFFFFC0 := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [I.r8]; rfl
  have k1 : ∀ q, q.val ≠ 0 → q ≠ 9 → q ≠ 30 → q ≠ 6 → reg m1 q = reg m q := fun q h0 h9 h30 h6 => by
    rw [u1.regs]; simp only [upd_app, h0, h9, h30, h6, ite_false]
  have x30 : reg m1 30 = (Sha256.vs w hv t).a := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [I.va]; exact BitVec.zero_add _
  have x6 : reg m1 6 = (Sha256.vs w hv t).e := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [I.ve]; exact BitVec.zero_add _
  have kk : ∀ q, kcLoopKeep q = true → reg m1 q = reg m q := fun q hq =>
    k1 q (fun e => pkeep_ne hq (r := 0) rfl (Fin.ext e)) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)
  obtain ⟨m2, d2, u2⟩ := u1.self.notTaken I.code 0xE0 kc_at_dc (by decide)
    (by rw [x9, z1]; exact beq_lt64 ht)
  obtain ⟨m3, d3, u3⟩ := u2.aluImm I.code kc_at_e0 (off' := 0xE4) (by decide)
  have r8 : reg m1 8 = BitVec.ofNat 32 t := by rw [k1 _ (by decide) (by decide) (by decide) (by decide), I.r8]
  have r19 : reg m1 19 = 0x10 := by rw [k1 _ (by decide) (by decide) (by decide) (by decide), I.r19]
  have r20 : reg m1 20 = F + BitVec.ofNat 32 0x2C := by
    rw [k1 _ (by decide) (by decide) (by decide) (by decide), I.r20]
  have r22 : reg m1 22 = F + BitVec.ofNat 32 (0x2C + 4 * t) := by
    rw [k1 _ (by decide) (by decide) (by decide) (by decide), I.r22]
  have r7 : reg m1 7 = kcK + BitVec.ofNat 32 (4 * t) := by
    rw [k1 _ (by decide) (by decide) (by decide) (by decide), I.r7]
  rw [r8, show aluEval .add (BitVec.ofNat 32 t) 1 = BitVec.ofNat 32 (t + 1) from ofNat_add_ofNat t 1] at u3
  have hb : branchTaken .bgeu (upd (reg m1) 28 (BitVec.ofNat 32 (t + 1)) 8)
      (upd (reg m1) 28 (BitVec.ofNat 32 (t + 1)) 19) = decide (16 ≤ t) := by
    simp +decide only [upd_app, ↓reduceIte]; rw [r8, r19, bgeu16 ht]
  -- the facts about the round's other registers, which both paths keep
  have vb : reg m1 29 = (Sha256.vs w hv t).b := by
    rw [k1 _ (by decide) (by decide) (by decide) (by decide), I.vb]
  have vc : reg m1 a6 = (Sha256.vs w hv t).c := by
    rw [k1 _ (by decide) (by decide) (by decide) (by decide), I.vc]
  have vd : reg m1 25 = (Sha256.vs w hv t).d := by
    rw [k1 _ (by decide) (by decide) (by decide) (by decide), I.vd]
  have vf : reg m1 5 = (Sha256.vs w hv t).f := by
    rw [k1 _ (by decide) (by decide) (by decide) (by decide), I.vf]
  have vg : reg m1 17 = (Sha256.vs w hv t).g := by
    rw [k1 _ (by decide) (by decide) (by decide) (by decide), I.vg]
  have vh : reg m1 26 = (Sha256.vs w hv t).h := by
    rw [k1 _ (by decide) (by decide) (by decide) (by decide), I.vh]
  by_cases h16 : 16 ≤ t
  · have hm : max t 16 = t := Nat.max_eq_left h16
    obtain ⟨m4, d4, u4⟩ := u3.taken I.code 0xEE kc_at_e4 (by decide) (by rw [hb]; exact decide_eq_true h16)
    have h8 : reg m4 8 = BitVec.ofNat 32 t := by rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact r8
    have h28 : reg m4 28 = BitVec.ofNat 32 (t + 1) := by rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]
    have h20 : reg m4 20 = F + BitVec.ofNat 32 0x2C := by
      rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact r20
    have w15 : memLoad32 M (kslot F (t + 1)) = w (t - 15) := by
      rw [kslot_mod (show (t + 1) % 16 = (t - 15) % 16 by omega)]
      exact I.win _ (by rw [hm]; omega) (by rw [hm]; omega)
    have w2 : memLoad32 M (kslot F (t + 14)) = w (t - 2) := by
      rw [kslot_mod (show (t + 14) % 16 = (t - 2) % 16 by omega)]
      exact I.win _ (by rw [hm]; omega) (by rw [hm]; omega)
    have w16 : memLoad32 M (kslot F t) = w (t - 16) := by
      rw [kslot_mod (show t % 16 = (t - 16) % 16 by omega)]
      exact I.win _ (by rw [hm]; omega) (by rw [hm]; omega)
    have w7 : memLoad32 M (kslot F (t + 9)) = w (t - 7) := by
      rw [kslot_mod (show (t + 9) % 16 = (t - 7) % 16 by omega)]
      exact I.win _ (by rw [hm]; omega) (by rw [hm]; omega)
    obtain ⟨E1, E2, E3⟩ := kcSched_run (M := M) (f := reg m4) u4.self.zero h8 h28 h20 w15 w2 w16 w7
      (hw t h16 ht)
    obtain ⟨m5, c5, u5⟩ := St.block kcSched u4.self I.code kcSched_end
      (kcSched_ok h8 h28 h20 (kslot_al S.hF) (kslot_sep S.sFC t))
    rw [E1] at u5
    have e5 : ∀ q, kcSchedKeep q = true → reg m5 q = upd (reg m1) 28 (BitVec.ofNat 32 (t + 1)) q :=
      fun q hq => by rw [u5.regs, E3 q hq, u4.regs]
    refine ⟨m5, memStore32 M (kslot F t) (w t), c1.trans (.cons d2 (.cons d3 (.cons d4 c5))),
      ⟨u5.self, I.code.store32 (kslot_sep S.sFC t), kd_store I.kd (kslot_sep S.sFK t), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [e5 _ rfl]; simp +decide only [upd_app, ↓reduceIte]
    · rw [e5 _ rfl]; simp +decide only [upd_app, ↓reduceIte]; exact r19
    · rw [e5 _ rfl]; simp +decide only [upd_app, ↓reduceIte]; exact r20
    · rw [e5 _ rfl]; simp +decide only [upd_app, ↓reduceIte]; exact r22
    · rw [e5 _ rfl]; simp +decide only [upd_app, ↓reduceIte]; exact r7
    · rw [u5.regs, E2]
    · rw [e5 _ rfl]; simp +decide only [upd_app, ↓reduceIte]; exact x30
    · rw [e5 _ rfl]; simp +decide only [upd_app, ↓reduceIte]; exact vb
    · rw [e5 _ rfl]; simp +decide only [upd_app, ↓reduceIte]; exact vc
    · rw [e5 _ rfl]; simp +decide only [upd_app, ↓reduceIte]; exact vd
    · rw [e5 _ rfl]; simp +decide only [upd_app, ↓reduceIte]; exact x6
    · rw [e5 _ rfl]; simp +decide only [upd_app, ↓reduceIte]; exact vf
    · rw [e5 _ rfl]; simp +decide only [upd_app, ↓reduceIte]; exact vg
    · rw [e5 _ rfl]; simp +decide only [upd_app, ↓reduceIte]; exact vh
    · intro s h1 h2
      rw [Nat.max_eq_left (by omega)] at h1 h2
      by_cases hs : s = t
      · subst hs; exact memLoad32_store32_same _ _ _
      · rw [kslot_store_ne (by omega)]; exact I.win s (by rw [hm]; omega) (by rw [hm]; omega)
    · intro x hx; rw [memStore32_get_sep (kslot_win hx t)]; exact I.fr x hx
    · intro q hq
      rw [e5 q (kcLoopKeep_sched q hq), upd_kp hq rfl rfl, kk q hq, I.keep q hq]
  · have hm : max t 16 = 16 := Nat.max_eq_right (by omega)
    obtain ⟨m4, d4, u4⟩ := u3.notTaken I.code 0xE8 kc_at_e4 (by decide) (by rw [hb]; exact decide_eq_false h16)
    have f22 : upd (reg m1) 28 (BitVec.ofNat 32 (t + 1)) 22 = F + BitVec.ofNat 32 (0x2C + 4 * t) := by
      simp +decide only [upd_app, ↓reduceIte]; exact r22
    obtain ⟨m5, d5, u5⟩ := u4.lw I.code kc_at_e8 (off' := 0xEC) (by decide)
      (by rw [f22, add_lit_zero]; exact aligned_add S.hF (by omega))
    have wt : memLoad32 M (upd (reg m1) 28 (BitVec.ofNat 32 (t + 1)) 22 + 0) = w t := by
      rw [f22, add_lit_zero]
      have := I.win t (by rw [hm]; omega) (by rw [hm]; omega)
      unfold kslot at this; rwa [Nat.mod_eq_of_lt (by omega)] at this
    rw [wt] at u5
    obtain ⟨m6, d6, u6⟩ := u5.jump I.code kc_at_ec (off' := 0x160) (by decide)
      (pc_even (off' := 0x160) S.hP u5.pc (by decide) (by decide))
    refine ⟨m6, M, c1.trans (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.refl _)))))),
      ⟨u6.self, I.code, I.kd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, I.fr, ?_⟩⟩
    all_goals try (rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte])
    · exact r19
    · exact r20
    · exact r22
    · exact r7
    · exact x30
    · exact vb
    · exact vc
    · exact vd
    · exact x6
    · exact vf
    · exact vg
    · exact vh
    · intro s h1 h2
      rw [Nat.max_eq_right (by omega)] at h1 h2
      exact I.win s (by rw [hm]; exact h1) (by rw [hm]; exact h2)
    · intro q hq
      rw [u6.regs, upd_kp hq rfl rfl, upd_kp hq rfl rfl, kk q hq, I.keep q hq]

set_option maxHeartbeats 4000000 in
/-- Round `t` from 0x160 back to 0xD4. -/
theorem kc_round_finish {P F : Word} {w : Nat → Word} {hv : Sha256.V8} {g : Fin 32 → Word}
    {M1 M : Word → BitVec 8} {t : Nat} {m : Machine} (S : KCStatic P F) (ht : t < 64)
    (I : KCMid P F w hv g M1 t M m) :
    ∃ m', Steps m m' ∧ KCR P F w hv g M1 (t + 1) M m' := by
  have hk : memLoad32 M (reg m 7 + 0) = Sha256.k[t]! := by
    rw [I.r7, add_lit_zero]; exact kcK_words I.kd t ht
  obtain ⟨E0, Ea, Ee, Eb, Ec, Ed, Ef, Eg, Eh, E8, E22, E7, Ek⟩ :=
    kcRound_run (M := M) (f := reg m) I.st.zero I.ve I.vf I.vg I.vh I.va I.vb I.vc I.vd I.wt hk
  obtain ⟨m1, c1, u1⟩ := St.block kcRound I.st I.code kcRound_end (kcRound_ok (by rw [I.r7]; exact kcK_al t))
  rw [E0] at u1
  obtain ⟨m2, d2, u2⟩ := u1.jump I.code kc_at_1e8 (off' := 0xD4) (by decide)
    (pc_even (off' := 0xD4) S.hP u1.pc (by decide) (by decide))
  refine ⟨m2, c1.trans (.cons d2 (.refl _)), ⟨u2.self, I.code, I.kd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, I.win, I.fr, ?_⟩⟩
  · rw [u2.regs, E8, I.r28]
  · rw [u2.regs, Ek _ rfl, I.r19]
  · rw [u2.regs, Ek _ rfl, I.r20]
  · rw [u2.regs, E22, I.r22, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc,
      show 0x2C + 4 * t + 4 = 0x2C + 4 * (t + 1) by omega]
  · rw [u2.regs, E7, I.r7, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc,
      show 4 * t + 4 = 4 * (t + 1) by omega]
  · rw [u2.regs, Ea]; rfl
  · rw [u2.regs, Eb]; rfl
  · rw [u2.regs, Ec]; rfl
  · rw [u2.regs, Ed]; rfl
  · rw [u2.regs, Ee]; rfl
  · rw [u2.regs, Ef]; rfl
  · rw [u2.regs, Eg]; rfl
  · rw [u2.regs, Eh]; rfl
  · intro q hq; rw [u2.regs, Ek q (kcLoopKeep_round q hq), I.keep q hq]

/-- The round loop from round `t` to its last round. -/
theorem kc_rounds_from {P F : Word} {w : Nat → Word} {hv : Sha256.V8} {g : Fin 32 → Word}
    {M1 : Word → BitVec 8} (S : KCStatic P F) (hw : ShaSched w) :
    ∀ k t (M : Word → BitVec 8) (m : Machine), t + k = 64 → KCR P F w hv g M1 t M m →
      ∃ m' M', Steps m m' ∧ KCR P F w hv g M1 64 M' m'
  | 0, t, M, m, h, I => ⟨m, M, .refl _, by rw [Nat.add_zero] at h; subst h; exact I⟩
  | k + 1, t, M, m, h, I => by
    obtain ⟨m1, M', c1, J⟩ := kc_to_round S hw I (by omega)
    obtain ⟨m2, c2, I2⟩ := kc_round_finish S (by omega) J
    obtain ⟨m3, M3, c3, I3⟩ := kc_rounds_from S hw k (t + 1) M' m2 (by omega) I2
    exact ⟨m3, M3, c1.trans (c2.trans c3), I3⟩

set_option maxHeartbeats 4000000 in
/-- After the last round the loop exits to 0x1EA with `a` in `t5` and `e`
in `t1`. -/
theorem kc_rounds_exit {P F : Word} {w : Nat → Word} {hv : Sha256.V8} {g : Fin 32 → Word}
    {M1 M : Word → BitVec 8} {m : Machine} (I : KCR P F w hv g M1 64 M m) :
    ∃ m', Steps m m' ∧ St M P m' 0x1EA (reg m') ∧
      reg m' 30 = (Sha256.vs w hv 64).a ∧ reg m' 29 = (Sha256.vs w hv 64).b ∧
      reg m' a6 = (Sha256.vs w hv 64).c ∧ reg m' 25 = (Sha256.vs w hv 64).d ∧
      reg m' 6 = (Sha256.vs w hv 64).e ∧ reg m' 5 = (Sha256.vs w hv 64).f ∧
      reg m' 17 = (Sha256.vs w hv 64).g ∧ reg m' 26 = (Sha256.vs w hv 64).h ∧
      ∀ q, kcLoopKeep q = true → reg m' q = g q := by
  obtain ⟨m1, c1, u1⟩ := St.block kcHead I.st I.code kcHead_end (by simp [BlockOk, BInstr.ok, kcHead])
  simp only [runBlock, BInstr.run, kcHead] at u1
  have x9 : reg m1 9 = BitVec.ofNat 32 64 + 0xFFFFFFC0 := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [I.r8]; rfl
  obtain ⟨m2, d2, u2⟩ := u1.self.taken I.code 0x1EA kc_at_dc (by decide)
    (by rw [x9, u1.self.zero]; decide)
  refine ⟨m2, c1.trans (.cons d2 (.refl _)), u2.self, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (rw [u2.regs, u1.regs]; simp +decide only [upd_app, ↓reduceIte])
  · rw [I.va]; exact BitVec.zero_add _
  · exact I.vb
  · exact I.vc
  · exact I.vd
  · rw [I.ve]; exact BitVec.zero_add _
  · exact I.vf
  · exact I.vg
  · exact I.vh
  · intro q hq
    rw [u2.regs, u1.regs, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl, I.keep q hq]

end C3.RV32
