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
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h1 : ∀ i, i < 32 → (0 - 1 : Word).getLsbD i = true := by decide
  rw [BitVec.getLsbD_and, h1 i hi, Bool.true_and]

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

theorem physMem_some {M : Word → BitVec 8} {o : Word} {k : BitVec 8} {addr v : Word}
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
    {rb : Fin 32} {o : Word} {i : Nat} {s : SegW}
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

/-- The registers the overlap loops write. -/
abbrev ovClob : List (Fin 32) :=
  [a0, a1, a2, a3, a4, a5, (16 : Fin 32), ra, s3, s4, s5, s7, s8, s9, s10]

theorem ov_sub : ∀ r, r ∉ ipClob → r ∉ ovClob := by decide

theorem ov_ip : ∀ rd, rd ∈ ovClob → rd ∈ ipClob ∧ rd ≠ RV32.sp ∧ rd ≠ RV32.s0 ∧ rd ≠ RV32.s1 := by
  decide

theorem nv {r : Fin 32} (hr : r ∉ ovClob) (q : Fin 32) (hq : q ∈ ovClob := by decide) : r ≠ q :=
  fun e => hr (e ▸ hq)

theorem OBase.regs {segs : List SegW}
    (b : OBase R G ptr len out ilen M0 f0 sv cnt entry segs Mx g) {g' : Fin 32 → Word}
    (h : ∀ r, r ∉ ovClob → g' r = g r) : OBase R G ptr len out ilen M0 f0 sv cnt entry segs Mx g' :=
  { b with
    inv := b.inv.frameR (fun r hr => h r (ov_sub r hr))
      (by rw [h _ (by decide), b.inv.sp]) (by rw [h _ (by decide), b.inv.s0])
      (by rw [h _ (by decide), b.inv.s1]) (by rw [h _ (by decide), b.inv.zero])
    s2 := by rw [h _ (by decide), b.s2]
    s11 := by rw [h _ (by decide), b.s11]
    s6 := by rw [h _ (by decide), b.s6] }

theorem OBase.phys (env : IEnv P R G ptr len out) {segs : List SegW}
    (b : OBase R G ptr len out ilen M0 f0 sv cnt entry segs Mx g) (k : BitVec 8) (addr : Word) :
    OBase R G ptr len out ilen M0 f0 sv cnt entry segs (physMem Mx (G + 0x124) k addr) g :=
  { b with
    inv := b.inv.phys env k addr
    arr := b.arr.agree (ArrAgree.phys _ _ _ _) (by rw [b.hl]; exact b.hc)
    it := by rw [show G + 0x14 = G + BitVec.ofNat 32 0x14 from rfl, physMem_ld _ _ _ _ _ (by omega)]; exact b.it
    ent := by rw [show G + 8 = G + BitVec.ofNat 32 8 from rfl, physMem_ld _ _ _ _ _ (by omega)]; exact b.ent
    cntw := by
      rw [show G + 0xC = G + BitVec.ofNat 32 0xC from rfl, physMem_ld _ _ _ _ _ (by omega)]; exact b.cntw }

theorem phys_tag {k : BitVec 8} {addr v : Word} {t : BitVec 8} (h : physResult k addr = some (t, v)) :
    t.zeroExtend 32 ≠ (2 : Word) := by
  unfold physResult at h
  split at h
  · split at h <;> (cases h <;> decide)
  · split at h
    · split at h <;> (cases h <;> decide)
    · split at h
      · split at h <;> (cases h <;> decide)
      · cases h; decide

theorem zext8_inj {a b : BitVec 8} (h : a.zeroExtend 32 = b.zeroExtend 32) : a = b := by
  have := congrArg (BitVec.extractLsb' 0 8) h
  rwa [zext_lsb8, zext_lsb8] at this

theorem flag_ne (c : Bool) : ((if c then 1 else 0 : Word) != 0) = c := by cases c <;> rfl

theorem flag_and (c d : Bool) : (((if c then 1 else 0 : Word) &&& (if d then 1 else 0)) != 0) = (c && d) := by
  cases c <;> cases d <;> rfl

theorem SlotOk.agree {M' M : Word → BitVec 8} {G : Word} {j : Nat} {s : SegW} (h : SlotOk M G j s)
    (ha : ArrAgree M' M G) (hj : j < 16) : SlotOk M' G j s := by
  obtain ⟨e1, e2, e3, e4⟩ := h
  refine ⟨by rw [ha.load (by omega) (by omega), e1], by rw [ha.load (by omega) (by omega), e2],
    by rw [ha.load (by omega) (by omega), e3], ?_⟩
  rw [show 0x30 + 16 * j = 0x24 + (12 + 16 * j) by omega, ha _ (by omega),
    show 0x24 + (12 + 16 * j) = 0x30 + 16 * j by omega, e4]

/-- The inner overlap loop's registers, comparing segment `j`, placed at `xa`
in space `sa`. -/
def IHd (G : Word) (j : Nat) (sa : BitVec 8) (xa : Word) (g : Fin 32 → Word) : Prop :=
  g s5 = G + BitVec.ofNat 32 (0x24 + 16 * j) ∧ g s8 = G + BitVec.ofNat 32 (0x24 + 16 * (j + 1)) ∧
    g s4 = BitVec.ofNat 32 (j + 1) ∧ g s7 = sa.zeroExtend 32 ∧ g s9 = xa

theorem IHd.frame {G : Word} {j : Nat} {sa : BitVec 8} {xa : Word} {g g' : Fin 32 → Word}
    (h : IHd G j sa xa g) (k : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 →
      r ≠ (16 : Fin 32) → r ≠ ra → r ≠ s3 → r ≠ s10 → g' r = g r) : IHd G j sa xa g' := by
  obtain ⟨h5, h8, h4, h7, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)] <;> assumption

/-- One pass of the inner overlap loop, from offset 0x352: segment `bs` in
slot `k` against segment `a` in slot `j`, back to 0x34A with 0 in `a1`. -/
theorem ov_body (env : IEnv P R G ptr len out) (code0 : ICode M0 P) {segs : List SegW}
    {j k : Nat} {sa : BitVec 8} {xa : Word} {a bs : SegW}
    (b : OBase R G ptr len out ilen M0 f0 sv cnt entry segs Mx g) {m : Machine} (st : St Mx P m 0x352 g)
    (hjk : j < k) (hk : k < cnt.toNat) (hd : IHd G j sa xa g) (hs10 : g s10 = G + BitVec.ofNat 32 (0x24 + 16 * k))
    (ha : SlotOk Mx G j a) (hb : SlotOk Mx G k bs) :
    match pairW a sa xa bs with
    | .error e => IErrDone R G out M0 f0 e m
    | .ok () => ∃ m' My g', Steps m m' ∧ St My P m' 0x34A g' ∧
        OBase R G ptr len out ilen M0 f0 sv cnt entry segs My g' ∧ IHd G j sa xa g' ∧ g' a1 = 0 ∧
        g' s3 = G + BitVec.ofNat 32 (0x24 + 16 * (k + 1)) := by
  have hk16 : k < 16 := Nat.lt_of_lt_of_le hk b.hc
  have hc := (b.inv.code env code0).parse
  have hz := b.inv.zero
  obtain ⟨m1, d1, u1⟩ := st.aluImm hc ip_at_352 (off' := 0x356) (by decide)
  rw [hs10, show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl,
    show aluEval .add (G + BitVec.ofNat 32 (0x24 + 16 * k)) (BitVec.ofNat 32 0x10) =
      G + BitVec.ofNat 32 (0x24 + 16 * (k + 1)) by
        show _ + _ = _; rw [add_ofNat_assoc]; congr 2 <;> omega] at u1
  obtain ⟨m2, d2, u2⟩ := u1.notTaken hc 0x35A ip_at_356 (by decide)
    (by rw [updz hz (by decide), hs10, show upd g s3 (G + BitVec.ofNat 32 (0x24 + 16 * (k + 1))) x0 = 0 from rfl]
        exact Bool.eq_false_iff.mpr fun h => env.g_ne0 _ (by omega) (by omega) (beq_iff_eq.mp h))
  have b2 := b.regs (g' := upd g s3 (G + BitVec.ofNat 32 (0x24 + 16 * (k + 1)))) fun r hr => updz hz (nv hr s3)
  obtain ⟨m3, g3, c3, u3, fr3⟩ := ov_phys env code0 b2.inv u2 (by rw [updz hz (by decide), hs10]) hb
    (by decide) ip_at_35a ip_at_35e ip_at_362 ip_at_364 ip_at_368 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (by decide)
  have b3 := (b2.phys env bs.kind bs.addr).regs (g' := g3) fun r hr => fr3 r (nv hr a0) (nv hr a1) (nv hr a2)
    (nv hr a3) (nv hr a4) (nv hr ra)
  have hd3 : IHd G j sa xa g3 := hd.frame fun r h0 h1 h2 h3 h4 _ _ h7 hs3 _ => by
    rw [fr3 r h0 h1 h2 h3 h4 h7, updz hz hs3]
  have g3s3 : g3 s3 = G + BitVec.ofNat 32 (0x24 + 16 * (k + 1)) := by
    rw [fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), upd_same (by decide)]
  have g3s10 : g3 s10 = G + BitVec.ofNat 32 (0x24 + 16 * k) := by
    rw [fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), updz hz (by decide), hs10]
  have hc3 := (b3.inv.code env code0).parse
  obtain ⟨m4, d4, u4⟩ := u3.lbu hc3 ip_at_36c (off' := 0x370) (by decide)
  rw [b3.inv.sp] at u4
  have pre : Steps m m4 := .cons d1 (.cons d2 (c3.trans (.single d4)))
  have b4 := b3.regs (g' := upd g3 a0 ((physMem Mx (G + 0x124) bs.kind bs.addr (G + 0x124)).zeroExtend 32))
    fun r hr => updz b3.inv.zero (nv hr a0)
  have hd4 := hd3.frame (g' := upd g3 a0 ((physMem Mx (G + 0x124) bs.kind bs.addr (G + 0x124)).zeroExtend 32))
    fun r h0 _ _ _ _ _ _ _ _ _ => updz b3.inv.zero h0
  unfold pairW
  cases hph : physResult bs.kind bs.addr with
  | none =>
    obtain ⟨n0, n1⟩ := physMem_none (M := Mx) (o := G + 0x124) hph
    obtain ⟨m5, d5, u5⟩ := u4.taken hc3 0x414 ip_at_370 (by decide)
      (by rw [upd_a0, n0, updz b3.inv.zero (by decide), b3.s6]; rfl)
    obtain ⟨m6, d6, u6⟩ := u5.lbu hc3 ip_at_414 (off' := 0x418) (by decide)
    exact IErrDone.pre (pre.trans (.cons d5 (.single d6)))
      (ip_err418 env code0 (b4.inv.setR (16 : Fin 32)) u6
        (by rw [upd_same (by decide), updz b3.inv.zero (by decide), b3.inv.sp,
          show G + (0x125 : Word) = G + 0x124 + 1 by rw [BitVec.add_assoc]; rfl, n1]; rfl))
  | some r =>
    obtain ⟨sb, xb⟩ := r
    obtain ⟨n0, n1⟩ := physMem_some (M := Mx) (o := G + 0x124) hph
    rw [n0] at u4 b4 hd4
    obtain ⟨m5, d5, u5⟩ := u4.notTaken hc3 0x374 ip_at_370 (by decide)
      (by rw [upd_a0, updz b3.inv.zero (by decide), b3.s6]
          exact Bool.eq_false_iff.mpr fun h => phys_tag hph (beq_iff_eq.mp h))
    obtain ⟨m6, d6, u6⟩ := u5.aluImm hc3 ip_at_374 (off' := 0x376) (by decide)
    have b6 := b4.regs (g' := upd (upd g3 a0 (sb.zeroExtend 32)) a1
      (aluEval .add (upd g3 a0 (sb.zeroExtend 32) x0) 0)) fun r hr => updz (by simp) (nv hr a1)
    have hd6 := hd4.frame (g' := upd (upd g3 a0 (sb.zeroExtend 32)) a1
      (aluEval .add (upd g3 a0 (sb.zeroExtend 32) x0) 0)) fun r _ h1 _ _ _ _ _ _ _ _ => updz (by simp) h1
    have g6a1 : upd (upd g3 a0 (sb.zeroExtend 32)) a1 (aluEval .add (upd g3 a0 (sb.zeroExtend 32) x0) 0) a1 = 0 := by
      rw [upd_same (by decide)]; rfl
    have g6s3 : upd (upd g3 a0 (sb.zeroExtend 32)) a1 (aluEval .add (upd g3 a0 (sb.zeroExtend 32) x0) 0) s3 =
        G + BitVec.ofNat 32 (0x24 + 16 * (k + 1)) := by
      rw [updz (by simp) (by decide), updz b3.inv.zero (by decide), g3s3]
    have hc6 := (b6.inv.code env code0).parse
    have pre6 : Steps m m6 := pre.trans (.cons d5 (.single d6))
    by_cases hs : sa = sb
    · subst hs
      dsimp only; rw [ite_eq_left rfl]
      obtain ⟨m7, d7, u7⟩ := u6.notTaken hc6 0x37A ip_at_376 (by decide)
        (by rw [hd6.2.2.2.1, updz (by simp) (by decide), upd_a0]; simp [branchTaken])
      have hj16 : j < 16 := by omega
      have ha3 : SlotOk (physMem Mx (G + 0x124) bs.kind bs.addr) G j a := ha.agree (ArrAgree.phys _ _ _ _) hj16
      have hb3 : SlotOk (physMem Mx (G + 0x124) bs.kind bs.addr) G k bs := hb.agree (ArrAgree.phys _ _ _ _) hk16
      have u7' := u7.self
      have s7 : reg m7 s5 = G + BitVec.ofNat 32 (0x24 + 16 * j) := by rw [u7.regs]; exact hd6.1
      have s7_10 : reg m7 s10 = G + BitVec.ofNat 32 (0x24 + 16 * k) := by
        rw [u7.regs, updz (by simp) (by decide), updz b3.inv.zero (by decide), g3s10]
      have s7_9 : reg m7 s9 = xa := by rw [u7.regs]; exact hd6.2.2.2.2
      have b7 := b6.regs (g' := reg m7) fun r _ => u7.regs r
      have hd7 := hd6.frame (g' := reg m7) fun r _ _ _ _ _ _ _ _ _ _ => u7.regs r
      obtain ⟨m8, d8, u8⟩ := u7'.lw hc6 ip_at_37a (off' := 0x37E) (by decide)
        (by rw [s7]; exact aligned_add env.hG (k := 0x2C + 16 * j) (by omega) |> fun h => by
              rwa [show G + BitVec.ofNat 32 (0x2C + 16 * j) = G + BitVec.ofNat 32 (0x24 + 16 * j) + 8 by
                rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]; congr 2 <;> omega] at h)
      rw [s7, show G + BitVec.ofNat 32 (0x24 + 16 * j) + 8 = G + BitVec.ofNat 32 (0x2C + 16 * j) by
        rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]; congr 2 <;> omega, ha3.2.2.1] at u8
      obtain ⟨m9, d9, u9⟩ := u8.alu hc6 ip_at_37e (off' := 0x382) (by decide)
      obtain ⟨m10, d10, u10⟩ := u9.aluImm hc6 ip_at_382 (off' := 0x384) (by decide)
      have r10 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ (16 : Fin 32) → reg m10 r = reg m7 r := fun r h1 h2 h6 => by
        rw [u10.regs, updz (by simp) h6, updz (by simp) h1, updz b7.inv.zero h2]
      have r10a1 : reg m10 a1 = a.len + xa := by
        rw [u10.regs]; simp +decide only [upd, ↓reduceIte]; rw [s7_9]; rfl
      have r10a2 : reg m10 a2 = a.len := by
        rw [u10.regs, updz (by simp) (by decide), updz (by simp) (by decide), upd_same (by decide)]
      have r10a6 : reg m10 (16 : Fin 32) = 10 := by
        rw [u10.regs, upd_same (by decide)]; show _ + _ = _
        rw [updz (by simp) (show (0 : Fin 32) ≠ a1 by decide)]; simp [upd]
      have b10 := b7.regs (g' := reg m10) fun r hr => r10 r (nv hr a1) (nv hr a2) (nv hr (16 : Fin 32))
      have hd10 := hd7.frame (g' := reg m10) fun r _ h1 h2 _ _ _ h6 _ _ _ => r10 r h1 h2 h6
      have hc10 := (b10.inv.code env code0).parse
      have pre10 : Steps m m10 := pre6.trans (.cons d7 (.cons d8 (.cons d9 (.single d10))))
      unfold pairChk
      by_cases e1 : (a.len + xa).ult a.len = true
      · rw [ite_eq_left e1]
        obtain ⟨m11, d11, u11⟩ := u10.self.taken hc10 0x418 ip_at_384 (by decide)
          (by rw [r10a1, r10a2]; exact e1)
        exact IErrDone.pre (pre10.trans (.single d11)) (ip_err418 env code0 b10.inv u11 (by rw [r10a6]; rfl))
      rw [ite_eq_right e1]
      obtain ⟨m11, d11, u11⟩ := u10.self.notTaken hc10 0x388 ip_at_384 (by decide)
        (by rw [r10a1, r10a2]; exact Bool.eq_false_iff.mpr e1)
      obtain ⟨m12, d12, u12⟩ := u11.lw hc10 ip_at_388 (off' := 0x38C) (by decide)
        (by rw [b10.inv.sp]; exact aligned_add env.hG (k := 0x128) (by decide))
      rw [b10.inv.sp, show G + (0x128 : Word) = G + 0x124 + 4 by rw [BitVec.add_assoc]; rfl, n1] at u12
      obtain ⟨m13, d13, u13⟩ := u12.lw hc10 ip_at_38c (off' := 0x390) (by decide)
        (by rw [updz b10.inv.zero (by decide), r10 _ (by decide) (by decide) (by decide), s7_10]
            exact aligned_add env.hG (k := 0x2C + 16 * k) (by omega) |> fun h => by
              rwa [show G + BitVec.ofNat 32 (0x2C + 16 * k) = G + BitVec.ofNat 32 (0x24 + 16 * k) + 8 by
                rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]; congr 2 <;> omega] at h)
      rw [updz b10.inv.zero (by decide), r10 _ (by decide) (by decide) (by decide), s7_10,
        show G + BitVec.ofNat 32 (0x24 + 16 * k) + 8 = G + BitVec.ofNat 32 (0x2C + 16 * k) by
          rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]; congr 2 <;> omega,
        hb3.2.2.1] at u13
      obtain ⟨m14, d14, u14⟩ := u13.alu hc10 ip_at_390 (off' := 0x394) (by decide)
      obtain ⟨m15, d15, u15⟩ := u14.alu hc10 ip_at_394 (off' := 0x398) (by decide)
      have r15 : ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m15 r = reg m10 r := fun r h2 h3 h4 => by
        rw [u15.regs, updz (by simp) h4, updz (by simp) h3, updz (by simp) h4, updz b10.inv.zero h2]
      have r15a4 : reg m15 a4 = if (bs.len + xb).ult bs.len then 1 else 0 := by
        rw [u15.regs]; simp +decide only [upd, ↓reduceIte]; rfl
      have r15a3 : reg m15 a3 = bs.len + xb := by
        rw [u15.regs]; simp +decide only [upd, ↓reduceIte]; rfl
      have r15a2 : reg m15 a2 = xb := by rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
      have b15 := b10.regs (g' := reg m15) fun r hr => r15 r (nv hr a2) (nv hr a3) (nv hr a4)
      have hd15 := hd10.frame (g' := reg m15) fun r _ _ h2 h3 h4 _ _ _ _ _ => r15 r h2 h3 h4
      have hc15 := (b15.inv.code env code0).parse
      have a6_15 : reg m15 (16 : Fin 32) = 10 := by rw [r15 _ (by decide) (by decide) (by decide), r10a6]
      have pre15 : Steps m m15 := pre10.trans (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.single d15)))))
      by_cases e2 : (bs.len + xb).ult bs.len = true
      · rw [ite_eq_left e2]
        obtain ⟨m16, d16, u16⟩ := u15.self.taken hc15 0x418 ip_at_398 (by decide)
          (by rw [r15a4, b15.inv.zero, e2]; rfl)
        exact IErrDone.pre (pre15.trans (.single d16)) (ip_err418 env code0 b15.inv u16 (by rw [a6_15]; rfl))
      rw [ite_eq_right e2]
      obtain ⟨m16, d16, u16⟩ := u15.self.notTaken hc15 0x39A ip_at_398 (by decide)
        (by rw [r15a4, b15.inv.zero, Bool.eq_false_iff.mpr e2]; rfl)
      obtain ⟨m17, d17, u17⟩ := u16.alu hc15 ip_at_39a (off' := 0x39E) (by decide)
      obtain ⟨m18, d18, u18⟩ := u17.alu hc15 ip_at_39e (off' := 0x3A2) (by decide)
      obtain ⟨m19, d19, u19⟩ := u18.alu hc15 ip_at_3a2 (off' := 0x3A4) (by decide)
      obtain ⟨m20, d20, u20⟩ := u19.aluImm hc15 ip_at_3a4 (off' := 0x3A6) (by decide)
      have r20 : ∀ r, r ≠ a1 → r ≠ a3 → reg m20 r = reg m15 r := fun r h1 h3 => by
        rw [u20.regs, updz (by simp) h1, updz (by simp) h3, updz (by simp) h1, updz b15.inv.zero h3]
      have r20a3 : reg m20 a3 = (if xa.ult (bs.len + xb) then 1 else 0) &&& (if xb.ult (a.len + xa) then 1 else 0) := by
        have q9 : reg m15 s9 = xa := by
          rw [r15 _ (by decide) (by decide) (by decide), r10 _ (by decide) (by decide) (by decide), s7_9]
        have q1 : reg m15 a1 = a.len + xa := by rw [r15 _ (by decide) (by decide) (by decide), r10a1]
        rw [u20.regs]; simp +decide only [upd, ↓reduceIte]
        rw [q9, r15a3, r15a2, q1]; rfl
      have r20a1 : reg m20 a1 = 0 := by rw [u20.regs, upd_same (by decide)]; rfl
      have b20 := b15.regs (g' := reg m20) fun r hr => r20 r (nv hr a1) (nv hr a3)
      have hd20 := hd15.frame (g' := reg m20) fun r _ h1 _ h3 _ _ _ _ _ _ => r20 r h1 h3
      have hc20 := (b20.inv.code env code0).parse
      have pre20 : Steps m m20 := pre15.trans (.cons d16 (.cons d17 (.cons d18 (.cons d19 (.single d20)))))
      by_cases e3 : (xa.ult (bs.len + xb) && xb.ult (a.len + xa)) = true
      · rw [ite_eq_left e3]
        obtain ⟨m21, d21, u21⟩ := u20.self.taken hc20 0x418 ip_at_3a6 (by decide)
          (by rw [r20a3, b20.inv.zero]; exact (flag_and _ _).trans e3)
        exact IErrDone.pre (pre20.trans (.single d21)) (ip_err418 env code0 b20.inv u21
          (by rw [r20 _ (by decide) (by decide), a6_15]; rfl))
      rw [ite_eq_right e3]
      obtain ⟨m21, d21, u21⟩ := u20.self.notTaken hc20 0x3A8 ip_at_3a6 (by decide)
        (by rw [r20a3, b20.inv.zero]; exact (flag_and _ _).trans (Bool.eq_false_iff.mpr e3))
      obtain ⟨m22, d22, u22⟩ := u21.jump hc20 ip_at_3a8 (off' := 0x34A) (by decide)
        (by rw [u21.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0x34A (by decide)))
      refine ⟨m22, _, _, pre20.trans (.cons d21 (.single d22)), u22, b20, hd20, r20a1, ?_⟩
      rw [r20 _ (by decide) (by decide), r15 _ (by decide) (by decide) (by decide),
        r10 _ (by decide) (by decide) (by decide), u7.regs]
      exact g6s3
    · dsimp only; rw [ite_eq_right hs]
      obtain ⟨m7, d7, u7⟩ := u6.taken hc6 0x34A ip_at_376 (by decide)
        (by rw [hd6.2.2.2.1, updz (by simp) (by decide), upd_a0]
            exact bne_iff_ne.mpr fun h => hs (zext8_inj h))
      exact ⟨m7, _, _, pre6.trans (.single d7), u7, b6, hd6, g6a1, g6s3⟩

/-- **The inner overlap loop**, from offset 0x34A with 0 in `a1` and segment
`k` next: segment `j` against segments `k` on, to 0x3BA. -/
theorem ov_inner (env : IEnv P R G ptr len out) (code0 : ICode M0 P) {segs : List SegW} {j : Nat}
    {sa : BitVec 8} {xa : Word} (hj : j < segs.length) :
    ∀ n k {Mx : Word → BitVec 8} {g : Fin 32 → Word} {m : Machine}, k + n = cnt.toNat → j < k →
      OBase R G ptr len out ilen M0 f0 sv cnt entry segs Mx g → St Mx P m 0x34A g → IHd G j sa xa g →
      g a1 = 0 → g s3 = G + BitVec.ofNat 32 (0x24 + 16 * k) →
      match innerW segs[j] sa xa (segs.drop k) with
      | .error e => IErrDone R G out M0 f0 e m
      | .ok () => ∃ m' My g', Steps m m' ∧ St My P m' 0x3BA g' ∧
          OBase R G ptr len out ilen M0 f0 sv cnt entry segs My g' ∧ IHd G j sa xa g'
  | n, k, Mx, g, m, hn, hjk, b, st, hd, ha1, hs3 => by
    have hc := (b.inv.code env code0).parse
    have hz := b.inv.zero
    obtain ⟨m1, d1, u1⟩ := st.notTaken hc 0x34C ip_at_34a (by decide) (by rw [ha1, hz]; rfl)
    obtain ⟨m2, d2, u2⟩ := u1.alu hc ip_at_34c (off' := 0x34E) (by decide)
    rw [show aluEval .add (g x0) (g s3) = G + BitVec.ofNat 32 (0x24 + 16 * k) by
      show g 0 + _ = _; rw [hz, hs3]; exact BitVec.zero_add _] at u2
    have b2 := b.regs (g' := upd g s10 (G + BitVec.ofNat 32 (0x24 + 16 * k))) fun r hr => updz hz (nv hr s10)
    have hd2 := hd.frame (g' := upd g s10 (G + BitVec.ofNat 32 (0x24 + 16 * k)))
      fun r _ _ _ _ _ _ _ _ _ h10 => updz hz h10
    have pre : Steps m m2 := .cons d1 (.single d2)
    match n with
    | 0 =>
      obtain ⟨m3, d3, u3⟩ := u2.taken hc 0x3BA ip_at_34e (by decide)
        (by rw [updz hz (by decide), hs3, updz hz (by decide), b.s11, show k = cnt.toNat by omega]
            exact beq_iff_eq.mpr rfl)
      rw [List.drop_of_length_le (by rw [b.hl]; omega)]
      exact ⟨m3, _, _, pre.trans (.single d3), u3, b2, hd2⟩
    | n + 1 =>
      have hk : k < cnt.toNat := by omega
      obtain ⟨m3, d3, u3⟩ := u2.notTaken hc 0x352 ip_at_34e (by decide)
        (by rw [updz hz (by decide), hs3, updz hz (by decide), b.s11]
            exact Bool.eq_false_iff.mpr fun h => add_ofNat_ne G (c := 0x24 + 16 * k) (d := 0x24 + 16 * cnt.toNat)
              (by omega) (by have := b.hc; omega) (by omega) (beq_iff_eq.mp h))
      have hk' : k < segs.length := by rw [b.hl]; exact hk
      have body := ov_body env code0 b2 u3 hjk hk hd2 (upd_same (by decide)) (b2.arr.1 j hj) (b2.arr.1 k hk')
      rw [List.drop_eq_getElem_cons hk']
      show match Except.bind (pairW segs[j] sa xa segs[k]) (fun _ => innerW segs[j] sa xa (segs.drop (k + 1))) with
        | .error e => IErrDone R G out M0 f0 e m
        | .ok () => _
      revert body
      cases pairW segs[j] sa xa segs[k] with
      | error e => intro body; exact IErrDone.pre (pre.trans (.single d3)) body
      | ok u =>
        rintro ⟨m4, M4, g4, c4, u4, b4, hd4, h4a1, h4s3⟩
        have ih := ov_inner env code0 hj n (k + 1) (by omega) (by omega) b4 u4 hd4 h4a1 h4s3
        revert ih
        cases innerW segs[j] sa xa (segs.drop (k + 1)) with
        | error e => intro ih; exact IErrDone.pre ((pre.trans (.single d3)).trans c4) ih
        | ok u' =>
          rintro ⟨m5, M5, g5, c5, u5, b5, hd5⟩
          exact ⟨m5, M5, g5, ((pre.trans (.single d3)).trans c4).trans c5, u5, b5, hd5⟩

theorem ov_cnt : ∀ c, c ≤ 16 → BitVec.ofNat 32 (16 * c) >>> ((4 : Word).toNat % 32) = BitVec.ofNat 32 c := by
  decide

theorem ov_sh : ∀ c, c ≤ 16 → BitVec.ofNat 32 c <<< ((4 : Word).toNat % 32) = BitVec.ofNat 32 (16 * c) := by
  decide

theorem ov_lt : ∀ a, a ≤ 16 → ∀ b, b ≤ 16 → BitVec.ult (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = decide (a < b) := by
  decide

theorem ov_ne0 : ∀ a, a ≤ 16 → 1 ≤ a → BitVec.ofNat 32 a ≠ 0 := by decide

theorem ov_end (G : Word) (c : Nat) :
    aluEval .sub (G + BitVec.ofNat 32 (0x24 + 16 * c)) (G + BitVec.ofNat 32 0x24) = BitVec.ofNat 32 (16 * c) := by
  show _ - _ = _
  rw [show G + BitVec.ofNat 32 (0x24 + 16 * c) = BitVec.ofNat 32 (16 * c) + (G + BitVec.ofNat 32 0x24) by
    rw [BitVec.add_comm (BitVec.ofNat 32 (16 * c)), add_ofNat_assoc], BitVec.add_sub_cancel]

/-- **The outer overlap loop**, from offset 0x322 at segment `j`, to 0x3C0. -/
theorem ov_outer (env : IEnv P R G ptr len out) (code0 : ICode M0 P) {segs : List SegW} :
    ∀ n j {Mx : Word → BitVec 8} {g : Fin 32 → Word} {m : Machine}, j + n + 1 = cnt.toNat →
      OInv R G ptr len out ilen M0 f0 sv cnt entry segs j Mx g → St Mx P m 0x322 g →
      match overlapW (segs.drop j) with
      | .error e => IErrDone R G out M0 f0 e m
      | .ok () => ∃ m' My g', Steps m m' ∧ St My P m' 0x3C0 g' ∧
          OBase R G ptr len out ilen M0 f0 sv cnt entry segs My g'
  | n, j, Mx, g, m, hn, oi, st => by
    have b := oi.base
    have hj16 : j < 16 := Nat.lt_of_lt_of_le oi.hj b.hc
    have hjl : j < segs.length := by rw [b.hl]; exact oi.hj
    have hc := (b.inv.code env code0).parse
    obtain ⟨m1, g1, c1, u1, fr1⟩ := ov_phys env code0 b.inv st oi.s5 (b.arr.1 j hjl) (by decide)
      ip_at_322 ip_at_326 ip_at_32a ip_at_32c ip_at_330 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
      (by decide)
    have b1 := (b.phys env segs[j].kind segs[j].addr).regs (g' := g1) fun r hr =>
      fr1 r (nv hr a0) (nv hr a1) (nv hr a2) (nv hr a3) (nv hr a4) (nv hr ra)
    have k1 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ ra → g1 r = g r := fr1
    have hc1 := (b1.inv.code env code0).parse
    obtain ⟨m2, d2, u2⟩ := u1.lbu hc1 ip_at_334 (off' := 0x338) (by decide)
    rw [b1.inv.sp] at u2
    rw [List.drop_eq_getElem_cons hjl]
    unfold overlapW physW
    cases hph : physResult segs[j].kind segs[j].addr with
    | none =>
      obtain ⟨n0, n1⟩ := physMem_none (M := Mx) (o := G + 0x124) hph
      obtain ⟨m3, d3, u3⟩ := u2.taken hc1 0x414 ip_at_338 (by decide)
        (by rw [upd_same (by decide), n0, updz b1.inv.zero (by decide), b1.s6]; rfl)
      obtain ⟨m4, d4, u4⟩ := u3.lbu hc1 ip_at_414 (off' := 0x418) (by decide)
      exact IErrDone.pre (c1.trans (.cons d2 (.cons d3 (.single d4))))
        (ip_err418 env code0 ((b1.inv.setR s7).setR (16 : Fin 32)) u4
          (by rw [upd_same (by decide), updz b1.inv.zero (by decide), b1.inv.sp,
            show G + (0x125 : Word) = G + 0x124 + 1 by rw [BitVec.add_assoc]; rfl, n1]; rfl))
    | some r =>
      obtain ⟨sa, xa⟩ := r
      obtain ⟨n0, n1⟩ := physMem_some (M := Mx) (o := G + 0x124) hph
      rw [n0] at u2
      obtain ⟨m3, d3, u3⟩ := u2.notTaken hc1 0x33C ip_at_338 (by decide)
        (by rw [upd_same (by decide), updz b1.inv.zero (by decide), b1.s6]
            exact Bool.eq_false_iff.mpr fun h => phys_tag hph (beq_iff_eq.mp h))
      obtain ⟨m4, d4, u4⟩ := u3.lw hc1 ip_at_33c (off' := 0x340) (by decide)
        (by rw [updz b1.inv.zero (by decide), b1.inv.sp]; exact aligned_add env.hG (k := 0x128) (by decide))
      obtain ⟨m5, d5, u5⟩ := u4.aluImm hc1 ip_at_340 (off' := 0x344) (by decide)
      obtain ⟨m6, d6, u6⟩ := u5.aluImm hc1 ip_at_344 (off' := 0x346) (by decide)
      obtain ⟨m7, d7, u7⟩ := u6.lw hc1 ip_at_346 (off' := 0x348) (by decide)
        (by simp +decide only [upd, ↓reduceIte]; rw [b1.inv.sp]; exact aligned_add env.hG (k := 0x14) (by decide))
      obtain ⟨m8, d8, u8⟩ := u7.alu hc1 ip_at_348 (off' := 0x34A) (by decide)
      have hit : memLoad32 (physMem Mx (G + 0x124) segs[j].kind segs[j].addr) (G + 0x14) =
          G + BitVec.ofNat 32 0x24 := b1.it
      have r8 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ ra → r ≠ s3 → r ≠ s4 → r ≠ s7 →
          r ≠ s8 → r ≠ s9 → reg m8 r = g r := fun r h0 h1 h2 h3 h4 h7 hs3 hs4 hs7 hs8 hs9 => by
        rw [u8.regs, updz (by simp) h1, updz (by simp) hs3, updz (by simp) hs4, updz (by simp) hs8,
          updz (by simp) hs9, updz b1.inv.zero hs7, k1 r h0 h1 h2 h3 h4 h7]
      have r8s7 : reg m8 s7 = sa.zeroExtend 32 := by
        rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
      have r8s9 : reg m8 s9 = xa := by
        rw [u8.regs]; simp +decide only [upd, ↓reduceIte]; rw [b1.inv.sp]
        rw [show G + (0x128 : Word) = G + 0x124 + 4 by rw [BitVec.add_assoc]; rfl, n1]
      have r8s8 : reg m8 s8 = G + BitVec.ofNat 32 (0x24 + 16 * (j + 1)) := by
        rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
        rw [k1 s5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), oi.s5]
        show _ + BitVec.ofNat 32 0x10 = _; rw [add_ofNat_assoc]; congr 2 <;> omega
      have r8s4 : reg m8 s4 = BitVec.ofNat 32 (j + 1) := by
        rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
        rw [k1 s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), oi.s4]
        exact ofNat_add_ofNat j 1
      have r8a1 : reg m8 a1 = BitVec.ofNat 32 (j + 1) := by
        rw [u8.regs, upd_same (by decide)]; show _ + _ = _
        simp +decide only [upd, ↓reduceIte]
        rw [k1 s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), oi.s4,
          show aluEval .add (BitVec.ofNat 32 j) 1 = BitVec.ofNat 32 (j + 1) from ofNat_add_ofNat j 1]
        exact BitVec.zero_add _
      have r8s3 : reg m8 s3 = G + BitVec.ofNat 32 0x24 := by
        rw [u8.regs]; simp +decide only [upd, ↓reduceIte]; rw [b1.inv.sp]; exact hit
      have b8 := b1.regs (g' := reg m8) fun r hr => by
        rw [r8 r (nv hr a0) (nv hr a1) (nv hr a2) (nv hr a3) (nv hr a4) (nv hr ra) (nv hr s3) (nv hr s4)
          (nv hr s7) (nv hr s8) (nv hr s9), k1 r (nv hr a0) (nv hr a1) (nv hr a2) (nv hr a3) (nv hr a4) (nv hr ra)]
      have hd8 : IHd G j sa xa (reg m8) := ⟨by
        rw [r8 s5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), oi.s5], r8s8, r8s4, r8s7, r8s9⟩
      have hc8 := (b8.inv.code env code0).parse
      obtain ⟨m9, d9, u9⟩ := u8.self.taken hc8 0x3AA ip_at_34a (by decide)
        (by rw [r8a1, b8.inv.zero]; exact bne_iff_ne.mpr (ov_ne0 (j + 1) (by omega) (by omega)))
      obtain ⟨m10, d10, u10⟩ := u9.alu hc8 ip_at_3aa (off' := 0x3AE) (by decide)
      obtain ⟨m11, d11, u11⟩ := u10.aluImm hc8 ip_at_3ae (off' := 0x3B0) (by decide)
      obtain ⟨m12, d12, u12⟩ := u11.aluImm hc8 ip_at_3b0 (off' := 0x3B4) (by decide)
      obtain ⟨m13, d13, u13⟩ := u12.alu hc8 ip_at_3b4 (off' := 0x3B6) (by decide)
      have r13 : ∀ r, r ≠ a0 → r ≠ s10 → reg m13 r = reg m8 r := fun r h0 h10 => by
        rw [u13.regs, updz (by simp) h10, updz (by simp) h10, updz (by simp) h0, updz b8.inv.zero h0]
      have r13a0 : reg m13 a0 = BitVec.ofNat 32 cnt.toNat := by
        rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
        rw [b8.s11, r8s3, ov_end G _]; exact ov_cnt _ b.hc
      have r13s10 : reg m13 s10 = G + BitVec.ofNat 32 (0x24 + 16 * (j + 1)) := by
        rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
        rw [r8a1, r8s3]
        show BitVec.ofNat 32 (j + 1) <<< ((4 : Word).toNat % 32) + _ = _
        rw [ov_sh _ (by omega), BitVec.add_comm, add_ofNat_assoc]
      have b13 := b8.regs (g' := reg m13) fun r hr => r13 r (nv hr a0) (nv hr s10)
      have hd13 := hd8.frame (g' := reg m13) fun r h0 _ _ _ _ _ _ _ _ h10 => r13 r h0 h10
      have hc13 := (b13.inv.code env code0).parse
      have pre13 : Steps m m13 := c1.trans (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7
        (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.single d13))))))))))))
      -- After the inner loop: back to 0x322 or out to 0x3C0.
      have after : ∀ {m' : Machine} {My : Word → BitVec 8} {g' : Fin 32 → Word}, Steps m m' →
          St My P m' 0x3BA g' → OBase R G ptr len out ilen M0 f0 sv cnt entry segs My g' → IHd G j sa xa g' →
          match overlapW (segs.drop (j + 1)) with
          | .error e => IErrDone R G out M0 f0 e m
          | .ok () => ∃ m' My g', Steps m m' ∧ St My P m' 0x3C0 g' ∧
              OBase R G ptr len out ilen M0 f0 sv cnt entry segs My g' := by
        intro m' My g' c' st' b' hd'
        have hc' := (b'.inv.code env code0).parse
        obtain ⟨m14, d14, u14⟩ := st'.alu hc' ip_at_3ba (off' := 0x3BC) (by decide)
        have b14 := b'.regs (g' := upd g' s5 (aluEval .add (g' x0) (g' s8))) fun r hr => updz b'.inv.zero (nv hr s5)
        have s14 : upd g' s5 (aluEval .add (g' x0) (g' s8)) s5 = G + BitVec.ofNat 32 (0x24 + 16 * (j + 1)) := by
          rw [upd_same (by decide)]; show g' 0 + _ = _; rw [b'.inv.zero, hd'.2.1]; exact BitVec.zero_add _
        match n with
        | 0 =>
          obtain ⟨m15, d15, u15⟩ := u14.notTaken hc' 0x3C0 ip_at_3bc (by decide)
            (by rw [updz b'.inv.zero (by decide), hd'.2.1, updz b'.inv.zero (by decide), b'.s11,
                  show j + 1 = cnt.toNat by omega]; exact bne_self_eq_false _)
          rw [List.drop_of_length_le (by rw [b.hl]; omega)]
          exact ⟨m15, _, _, c'.trans (.cons d14 (.single d15)), u15, b14⟩
        | n + 1 =>
          obtain ⟨m15, d15, u15⟩ := u14.taken hc' 0x322 ip_at_3bc (by decide)
            (by rw [updz b'.inv.zero (by decide), hd'.2.1, updz b'.inv.zero (by decide), b'.s11]
                exact bne_iff_ne.mpr fun h => add_ofNat_ne G (c := 0x24 + 16 * (j + 1))
                  (d := 0x24 + 16 * cnt.toNat) (by omega) (by have := b.hc; omega) (by omega) h)
          have ih := ov_outer env code0 n (j + 1) (by omega)
            ⟨b14, by omega, s14, by rw [updz b'.inv.zero (by decide)]; exact hd'.2.2.1⟩ u15
          revert ih
          cases overlapW (segs.drop (j + 1)) with
          | error e => intro ih; exact IErrDone.pre (c'.trans (.cons d14 (.single d15))) ih
          | ok u => rintro ⟨m16, M16, g16, c16, u16, b16⟩
                    exact ⟨m16, M16, g16, (c'.trans (.cons d14 (.single d15))).trans c16, u16, b16⟩
      show match Except.bind (innerW segs[j] sa xa (segs.drop (j + 1))) (fun _ => overlapW (segs.drop (j + 1))) with
        | .error e => IErrDone R G out M0 f0 e m
        | .ok () => _
      by_cases hlt : j + 1 < cnt.toNat
      · obtain ⟨m14, d14, u14⟩ := u13.self.taken hc13 0x352 ip_at_3b6 (by decide)
          (by rw [r13 a1 (by decide) (by decide), r8a1, r13a0]; show BitVec.ult _ _ = _
              rw [ov_lt _ (by omega) _ b.hc]; exact decide_eq_true hlt)
        have hk' : j + 1 < segs.length := by rw [b.hl]; exact hlt
        have body := ov_body env code0 b13 u14 (Nat.lt_succ_self j) hlt hd13 r13s10
          (b13.arr.1 j hjl) (b13.arr.1 (j + 1) hk')
        rw [List.drop_eq_getElem_cons hk']
        show match Except.bind (Except.bind (pairW segs[j] sa xa segs[j + 1])
            (fun _ => innerW segs[j] sa xa (segs.drop (j + 1 + 1)))) (fun _ => overlapW (segs[j + 1] :: segs.drop (j + 1 + 1))) with
          | .error e => IErrDone R G out M0 f0 e m
          | .ok () => _
        rw [← List.drop_eq_getElem_cons hk']
        revert body
        cases pairW segs[j] sa xa segs[j + 1] with
        | error e => intro body; exact IErrDone.pre (pre13.trans (.single d14)) body
        | ok u =>
          rintro ⟨m15, M15, g15, c15, u15, b15, hd15, h15a1, h15s3⟩
          have inner := ov_inner env code0 hjl (cnt.toNat - (j + 2)) (j + 1 + 1) (by omega) (by omega)
            b15 u15 hd15 h15a1 h15s3
          revert inner
          cases innerW segs[j] sa xa (segs.drop (j + 1 + 1)) with
          | error e => intro inner; exact IErrDone.pre ((pre13.trans (.single d14)).trans c15) inner
          | ok u' =>
            rintro ⟨m16, M16, g16, c16, u16, b16, hd16⟩
            exact after (((pre13.trans (.single d14)).trans c15).trans c16) u16 b16 hd16
      · obtain ⟨m14, d14, u14⟩ := u13.self.notTaken hc13 0x3BA ip_at_3b6 (by decide)
          (by rw [r13 a1 (by decide) (by decide), r8a1, r13a0]; show BitVec.ult _ _ = _
              rw [ov_lt _ (by omega) _ b.hc]; exact decide_eq_false hlt)
        have a14 := after (pre13.trans (.single d14)) u14 b13 hd13
        have hd0 : segs.drop (j + 1) = [] := List.drop_of_length_le (by rw [b.hl]; omega)
        rw [hd0] at a14 ⊢
        exact a14

end Overlap

end C3.RV32
