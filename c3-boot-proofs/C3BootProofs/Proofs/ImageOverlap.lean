import C3BootProofs.Proofs.ImageSegLoop

/-!
# `image::parse`: the end check and the overlap loops

From the segment loop's exit at offset 0x2E8, `image::parse` checks that the
last segment ends at the image's end, then checks each segment against every
later one (`overlapW`). The outer loop runs at 0x322 over segment `j`; the
inner loop at 0x352 over a later segment `k`.
-/

namespace C3.RV32

open C3.Image

set_option maxRecDepth 20000

/-- What holds through the overlap loops: the frame, the full segment array,
the end pointer in `s11`, and 2 (`Segment::physical`'s error tag) in `s6`. -/
structure OBase (R G ptr len out ilen : Word) (M0 : Word → BitVec 8) (f0 : Fin 32 → Word)
    (sv cnt : BitVec 8) (entry : Word) (segs : List SegW)
    (Mx : Word → BitVec 8) (g : Fin 32 → Word) : Prop where
  inv : IInv R G ptr len out ilen M0 f0 Mx g
  arr : ArrInv Mx G segs
  hl : segs.length = cnt.toNat
  hc : cnt.toNat ≤ 16
  s2 : g s2 = sv.zeroExtend 32
  s11 : g s11 = G + BitVec.ofNat 32 (0x24 + 16 * cnt.toNat)
  s6 : g s6 = 2
  it : memLoad32 Mx (G + 0x14) = G + BitVec.ofNat 32 0x24
  ent : memLoad32 Mx (G + 8) = entry
  cntw : memLoad32 Mx (G + 0xC) = cnt.zeroExtend 32

/-- The outer overlap loop's invariant at offset 0x322, at segment `j`. -/
structure OInv (R G ptr len out ilen : Word) (M0 : Word → BitVec 8) (f0 : Fin 32 → Word)
    (sv cnt : BitVec 8) (entry : Word) (segs : List SegW) (j : Nat)
    (Mx : Word → BitVec 8) (g : Fin 32 → Word) : Prop where
  base : OBase R G ptr len out ilen M0 f0 sv cnt entry segs Mx g
  hj : j < cnt.toNat
  s5 : g s5 = G + BitVec.ofNat 32 (0x24 + 16 * j)
  s4 : g s4 = BitVec.ofNat 32 j

theorem cnt_le16 : ∀ c : BitVec 8, c.toNat ≤ 16 →
    branchTaken .bgeu (aluEval .add 0 16) (c.zeroExtend 32) = true := by decide

theorem cnt_lt17 : ∀ c : BitVec 8, c.toNat ≤ 16 → aluEval .sltu (c.zeroExtend 32) 0x11 = 1 := by decide

theorem cnt_sh4 : ∀ c : BitVec 8, c.toNat ≤ 16 → c.zeroExtend 32 <<< 4 = BitVec.ofNat 32 (16 * c.toNat) := by
  decide

theorem ones_and (x : Word) : aluEval .and (aluEval .sub 0 1) x = x := by
  show (0 - 1 : Word) &&& x = x
  rw [show (0 - 1 : Word) = BitVec.allOnes 32 by decide, BitVec.allOnes_and]

section Overlap

variable {P R G ptr len out ilen : Word} {M0 Mx : Word → BitVec 8} {f0 g : Fin 32 → Word}
  {sv cnt : BitVec 8} {entry : Word}

/-- From offset 0x2E8 after the segment loop: the last segment must end at
the image's end; then the overlap loop's setup. -/
theorem od_setup (env : IEnv P R G ptr len out) (code0 : ICode M0 P) {segs : List SegW} {pos prev : Word}
    (li : LInv R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Mx g) {m : Machine}
    (st : St Mx P m 0x2E8 g) (hl : segs.length = cnt.toNat) (hc1 : 1 ≤ cnt.toNat) :
    (prev ≠ ilen ∧ IErrDone R G out M0 f0 9 m) ∨
      (prev = ilen ∧ ∃ m' My g', Steps m m' ∧ St My P m' 0x322 g' ∧
        OInv R G ptr len out ilen M0 f0 sv cnt entry segs 0 My g') := by
  have hc := (li.inv.code env code0).parse
  have hz := li.inv.zero
  have sp0 := li.inv.sp
  by_cases hp : prev = ilen
  · refine .inr ⟨hp, ?_⟩
    obtain ⟨m1, d1, u1⟩ := st.notTaken hc 0x2EC ip_at_2e8 (by decide)
      (by rw [li.s5, li.inv.s1, hp]; simp [branchTaken])
    obtain ⟨m2, d2, u2⟩ := u1.aluImm hc ip_at_2ec (off' := 0x2EE) (by decide)
    obtain ⟨m3, d3, u3⟩ := u2.lw hc ip_at_2ee (off' := 0x2F0) (by decide)
      (by rw [updz hz (by decide), sp0]; exact aligned_add env.hG (k := 0xC) (by decide))
    rw [updz hz (by decide), sp0, li.cntw] at u3
    obtain ⟨m4, d4, u4⟩ := u3.taken hc 0x304 ip_at_2f0 (by decide)
      (by rw [upd_same (by decide), updz (by simp) (by decide), upd_a0, show g x0 = 0 from hz]
          exact cnt_le16 cnt li.hc)
    obtain ⟨m5, d5, u5⟩ := u4.aluImm hc ip_at_304 (off' := 0x306) (by decide)
    obtain ⟨m6, d6, u6⟩ := u5.lw hc ip_at_306 (off' := 0x308) (by decide)
      (by simp +decide only [upd, ↓reduceIte]; rw [sp0]; exact aligned_add env.hG (k := 0xC) (by decide))
    obtain ⟨m7, d7, u7⟩ := u6.aluImm hc ip_at_308 (off' := 0x30C) (by decide)
    obtain ⟨m8, d8, u8⟩ := u7.aluImm hc ip_at_30c (off' := 0x310) (by decide)
    obtain ⟨m9, d9, u9⟩ := u8.alu hc ip_at_310 (off' := 0x314) (by decide)
    obtain ⟨m10, d10, u10⟩ := u9.alu hc ip_at_314 (off' := 0x318) (by decide)
    have k10 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ s4 → r ≠ s5 → reg m10 r = g r := fun r h0 h1 h4 h5 => by
      rw [u10.regs, updz (by simp) h0, updz (by simp) h0, updz (by simp) h5, updz (by simp) h0,
        updz (by simp) h0, updz (by simp) h4, updz (by simp) h1, updz hz h0]
    have r10a0 : reg m10 a0 = G + BitVec.ofNat 32 0x24 := by
      rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
      rw [sp0, li.cntw, cnt_lt17 cnt li.hc, ones_and]; rfl
    have r10s5 : reg m10 s5 = G + BitVec.ofNat 32 0x24 := by
      rw [u10.regs]; simp +decide only [upd, ↓reduceIte]; rw [sp0]; rfl
    have r10s4 : reg m10 s4 = BitVec.ofNat 32 0 := by
      rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
    have inv10 : IInv R G ptr len out ilen M0 f0 Mx (reg m10) := li.inv.frameR
      (fun r hr => k10 r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide))
        (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide)))
      (by rw [k10 _ (by decide) (by decide) (by decide) (by decide), sp0])
      (by rw [k10 _ (by decide) (by decide) (by decide) (by decide), li.inv.s0])
      (by rw [k10 _ (by decide) (by decide) (by decide) (by decide), li.inv.s1])
      (by rw [k10 _ (by decide) (by decide) (by decide) (by decide), hz])
    obtain ⟨m11, d11, u11⟩ := u10.self.sw hc ip_at_318 (off' := 0x31A) (by decide)
      (by rw [inv10.sp]; exact aligned_add env.hG (k := 0x14) (by decide))
    rw [inv10.sp, r10a0] at u11
    have inv11 := inv10.st32 env 0x14 (G + BitVec.ofNat 32 0x24) (Or.inl (by omega))
    have hc11 := (inv11.code env code0).parse
    obtain ⟨m12, d12, u12⟩ := u11.alu hc11 ip_at_31a (off' := 0x31C) (by decide)
    obtain ⟨m13, d13, u13⟩ := u12.aluImm hc11 ip_at_31c (off' := 0x31E) (by decide)
    have k13 : ∀ r, r ≠ s6 → r ≠ s11 → reg m13 r = reg m10 r := fun r h6 h11 => by
      rw [u13.regs, updz (by simp) h6, updz inv10.zero h11]
    have r13s11 : reg m13 s11 = G + BitVec.ofNat 32 (0x24 + 16 * cnt.toNat) := by
      rw [u13.regs, updz (by simp) (by decide), upd_same (by decide),
        k10 s11 (by decide) (by decide) (by decide) (by decide), li.s11, r10s5, cnt_sh4 cnt li.hc]
      show _ + _ = _
      rw [BitVec.add_comm, add_ofNat_assoc]
    have r13s6 : reg m13 s6 = 2 := by
      rw [u13.regs, upd_same (by decide)]; show reg m10 x0 + 2 = 2; rw [inv10.zero]; rfl
    have inv13 : IInv R G ptr len out ilen M0 f0 _ (reg m13) := inv11.frameR
      (fun r hr => k13 r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide)))
      (by rw [k13 _ (by decide) (by decide), inv10.sp]) (by rw [k13 _ (by decide) (by decide), inv10.s0])
      (by rw [k13 _ (by decide) (by decide), inv10.s1]) (by rw [k13 _ (by decide) (by decide), inv10.zero])
    obtain ⟨m14, d14, u14⟩ := u13.self.notTaken (inv13.code env code0).parse 0x322 ip_at_31e (by decide)
      (by rw [k13 s5 (by decide) (by decide), r10s5, r13s11]
          exact Bool.eq_false_iff.mpr fun h => add_ofNat_ne G (c := 0x24) (d := 0x24 + 16 * cnt.toNat)
            (by omega) (by omega) (by omega) (beq_iff_eq.mp h))
    refine ⟨m14, _, _, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8
      (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.single d14))))))))))))), u14, ⟨⟨inv13, ?_, hl, li.hc,
      ?_, r13s11, r13s6, ?_, ?_, ?_⟩, by omega, ?_, ?_⟩⟩
    · exact li.arr.agree (ArrAgree.st32 Mx G 0x14 _ (Or.inl (by omega)) (by omega)) (by rw [hl]; exact li.hc)
    · rw [k13 _ (by decide) (by decide), k10 _ (by decide) (by decide) (by decide) (by decide), li.s2]
    · exact memLoad32_store32_same _ _ _
    · rw [memLoad32_store32_sep (show Sep (G + 20) 4 (G + 8) 4 from
        sep_offsets G (c := 0x14) (n := 4) (d := 8) (k := 4) (by omega) (by omega) (by omega))]; exact li.ent
    · rw [memLoad32_store32_sep (show Sep (G + 20) 4 (G + 0xC) 4 from
        sep_offsets G (c := 0x14) (n := 4) (d := 0xC) (k := 4) (by omega) (by omega) (by omega))]; exact li.cntw
    · rw [k13 _ (by decide) (by decide), r10s5]
    · rw [k13 _ (by decide) (by decide), r10s4]
  · refine .inl ⟨hp, ?_⟩
    obtain ⟨m1, d1, u1⟩ := st.taken hc 0x2F8 ip_at_2e8 (by decide)
      (by rw [li.s5, li.inv.s1]; exact bne_iff_ne.mpr hp)
    obtain ⟨m2, d2, u2⟩ := u1.aluImm hc ip_at_2f8 (off' := 0x2FA) (by decide)
    obtain ⟨m3, d3, u3⟩ := u2.jump hc ip_at_2fa (off' := 0x418) (by decide)
      (by rw [u2.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0x418 (by decide)))
    exact IErrDone.pre (.cons d1 (.cons d2 (.single d3)))
      (ip_err418 env code0 (li.inv.setR (16 : Fin 32)) u3 (by rw [upd_same (by decide), hz]; rfl))

/-! ## `Segment::physical`'s result at `G + 0x124` -/

theorem physMem_out (M : Word → BitVec 8) (o : Word) (k : BitVec 8) (addr x : Word)
    (h : Sep o 8 x 1) : physMem M o k addr x = M x := by
  have n0 : x ≠ o := fun e => h 0 (by omega) 0 (by omega) (by rw [add_ofNat_zero, add_ofNat_zero, e])
  have n1 : x ≠ o + 1 := fun e => h 1 (by omega) 0 (by omega) (by rw [add_ofNat_zero, e]; rfl)
  have s4 : Sep (o + 4) 4 x 1 := fun i hi j hj e => h (4 + i) (by omega) j hj (by
    rw [← e, ← add_ofNat_assoc]; rfl)
  unfold physMem
  rcases physResult k addr with _ | ⟨t, v⟩
  · dsimp only; rw [memStore8_ne n0, memStore8_ne n1]
  · dsimp only; split
    · rw [memStore8_ne n0, memStore32_get_sep s4]
    · rw [memStore32_get_sep s4, memStore8_ne n0]

theorem physMem_none {M : Word → BitVec 8} {o : Word} {k : BitVec 8} {addr : Word}
    (h : physResult k addr = none) : physMem M o k addr o = 2 ∧ physMem M o k addr (o + 1) = 9 := by
  have n10 : o + 1 ≠ o := by
    have := add_ofNat_ne o (c := 1) (d := 0) (by decide) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  unfold physMem; rw [h]; dsimp only
  exact ⟨memStore8_same _ _ _, by rw [memStore8_ne n10, memStore8_same]⟩

theorem physMem_some {M : Word → BitVec 8} {o : Word} {k : BitVec 8} {addr t v : Word}
    {t8 : BitVec 8} (h : physResult k addr = some (t8, v)) :
    physMem M o k addr o = t8 ∧ memLoad32 (physMem M o k addr) (o + 4) = v := by
  have s : Sep o 1 (o + 4) 4 := fun i hi j hj e => by
    have : i = 0 := by omega
    subst this
    have := add_ofNat_ne o (c := 0) (d := 4 + j) (by omega) (by omega) (by omega)
    rw [add_ofNat_zero] at e this; rw [← add_ofNat_assoc] at this; exact this (e.trans rfl)
  unfold physMem; rw [h]; dsimp only
  split
  · exact ⟨memStore8_same _ _ _, by rw [memLoad32_store8_sep s, memLoad32_store32_same]⟩
  · refine ⟨by rw [memStore32_get_sep s.symm, memStore8_same], ?_⟩
    exact memLoad32_store32_same _ _ _

theorem phys_sep (env : IEnv P R G ptr len out) {x : Word} (h : Sep (R + BitVec.ofNat 32 0x50) 0x10C x 1) :
    Sep (G + 0x124) 8 x 1 := by
  have := h.sub (c := 0x104) (l := 8) (by omega)
  rwa [add_ofNat_assoc, show G + 0x124 = G + BitVec.ofNat 32 0x124 from rfl, env.g_ofs] at *

theorem IInv.phys (env : IEnv P R G ptr len out) (inv : IInv R G ptr len out ilen M0 f0 Mx g)
    (k : BitVec 8) (addr : Word) :
    IInv R G ptr len out ilen M0 f0 (physMem Mx (G + 0x124) k addr) g :=
  inv.mem env fun x _ h2 => physMem_out _ _ _ _ x (phys_sep env h2)

/-- The frame's words below `G + 0x124` are as before `Segment::physical`. -/
theorem physMem_ld (M : Word → BitVec 8) (G : Word) (k : BitVec 8) (addr : Word) (c : Nat)
    (hc : c + 4 ≤ 0x124) :
    memLoad32 (physMem M (G + 0x124) k addr) (G + BitVec.ofNat 32 c) = memLoad32 M (G + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => physMem_out _ _ _ _ _ (fun i hi j' hj' e => by
    have : j' = 0 := by omega
    subst this
    rw [add_ofNat_zero, show G + 0x124 = G + BitVec.ofNat 32 0x124 from rfl, add_ofNat_assoc,
      add_ofNat_assoc] at e
    exact add_ofNat_ne G (c := 0x124 + i) (d := c + j) (by omega) (by omega) (by omega) e)

theorem ArrAgree.phys (M : Word → BitVec 8) (G : Word) (k : BitVec 8) (addr : Word) :
    ArrAgree (physMem M (G + 0x124) k addr) M G := fun k' hk =>
  physMem_out _ _ _ _ _ (fun i hi j hj e => by
    have : j = 0 := by omega
    subst this
    rw [add_ofNat_zero, show G + 0x124 = G + BitVec.ofNat 32 0x124 from rfl, add_ofNat_assoc] at e
    exact add_ofNat_ne G (c := 0x124 + i) (d := 0x24 + k') (by omega) (by omega) (by omega) e)

/-- A call to `Segment::physical` for the segment in slot `i`, whose
address is in `rb`, through the call. -/
theorem ov_phys (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} {off : Nat} (st : St Mx P m off g)
    {rb : Fin 32} {o : Word} {i : Nat} {s : SegW} (hi : i < 16)
    (hrb : g rb = G + BitVec.ofNat 32 (0x24 + 16 * i)) (hs : SlotOk Mx G i s) (hrb1 : rb ≠ a1)
    (i1 : fetchRel imageParseCode off = some (.load .lw a1 rb 0, 4))
    (i2 : fetchRel imageParseCode (off + 4) = some (.load .lbu a2 rb 0xC, 4))
    (i3 : fetchRel imageParseCode (off + 4 + 4) = some (.aluImm .add a0 sp 0x124, 2))
    (i4 : fetchRel imageParseCode (off + 4 + 4 + 2) = some (.auipc ra 0, 4))
    (i5 : fetchRel imageParseCode (off + 4 + 4 + 2 + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 (off + 4 + 4 + 2) + 0 + o = P + 0x470) (hoff : off % 2 = 0) :
    ∃ m' g', Steps m m' ∧ St (physMem Mx (G + 0x124) s.kind s.addr) P m' (off + 4 + 4 + 2 + 8) g' ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ ra → g' r = g r := by
  have hc := (inv.code env code0).parse
  have hz := inv.zero
  obtain ⟨m1, d1, u1⟩ := st.lw hc i1 (off' := off + 4) (ofNat_add_ofNat off 4)
    (by rw [hrb, add_lit_zero]; exact aligned_add env.hG (by omega))
  rw [hrb, add_lit_zero, hs.1] at u1
  obtain ⟨m2, d2, u2⟩ := u1.lbu hc i2 (off' := off + 4 + 4) (ofNat_add_ofNat _ 4)
  rw [updz hz (Ne.symm hrb1 |> fun h => fun e => h e.symm), hrb,
    show G + BitVec.ofNat 32 (0x24 + 16 * i) + 0xC = G + BitVec.ofNat 32 (0x30 + 16 * i) by
      rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, add_ofNat_assoc]; congr 2 <;> omega,
    hs.2.2.2] at u2
  obtain ⟨m3, d3, u3⟩ := u2.aluImm hc i3 (off' := off + 4 + 4 + 2) (ofNat_add_ofNat _ 2)
  have g3o : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 →
      upd (upd (upd g a1 s.addr) a2 (s.kind.zeroExtend 32)) a0
        (aluEval .add (upd (upd g a1 s.addr) a2 (s.kind.zeroExtend 32) sp) 0x124) r = g r :=
    fun r h0 h1 h2 => by rw [updz (by simp) h0, updz (by simp) h2, updz hz h1]
  obtain ⟨m4, c4, u4, mem4, fr4⟩ := ip_physical env u3 (inv.code env code0) i4 i5 hb
    (even_at P env.hP _ (by omega))
    (by rw [upd_a0, updz (by simp) (by decide), updz hz (by decide), inv.sp]; rfl)
    (by rw [updz (by simp) (by decide), updz (by simp) (by decide), upd_same (by decide)])
    (by rw [updz (by simp) (by decide), upd_same (by decide)])
  rw [mem4] at u4
  exact ⟨m4, _, .cons d1 (.cons d2 (.cons d3 c4)), u4,
    fun r h0 h1 h2 h3 h4 h7 => by rw [fr4 r h1 h2 h3 h4 h7, g3o r h0 h1 h2]⟩

end Overlap

end C3.RV32
