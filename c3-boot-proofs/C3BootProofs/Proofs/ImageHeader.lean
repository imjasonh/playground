import C3BootProofs.Proofs.ImageMain

/-!
# `image::parse`: the fixed header

From entry to offset 0x15A, `image::parse` reads the header's fixed fields.
`ip_header` proves that it returns the error `hdrW` gives, or reaches 0x15A
with `IInv`, the reader past the header, and the security version, segment
count, and entry point in `s2`, `s3`, and `s4` (the last two also in the
frame's words at `G + 0xC` and `G + 8`).
-/

namespace C3.RV32

open C3.ImageV0

set_option maxRecDepth 20000

section Hdr

variable {P R G ptr len out ilen : Word} {M0 Mx : Word → BitVec 8} {f0 g : Fin 32 → Word}

theorem IInv.code (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) : ICode Mx P :=
  code0.of_agree (inv.win env) fun k hk => inv.outside _ (env.hST.subR (c := k) (l := 1) (by omega))

/-- `IInv` holds after a call that keeps every register but `a0` through
`a5`, `t0`, and `ra`. -/
theorem IInv.regsT (inv : IInv R G ptr len out ilen M0 f0 Mx g) {g' : Fin 32 → Word}
    (h : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ ra → g' r = g r) :
    IInv R G ptr len out ilen M0 f0 Mx g' := by
  have k : ∀ r, r ∉ ipClob → g' r = g r := fun r hr => by
    apply h r <;> (intro e; subst e; exact hr (by decide))
  refine ⟨inv.outside, inv.slots, inv.rdp, inv.rdl, ?_, ?_, ?_, fun r hr => by rw [k r hr, inv.keep r hr], ?_⟩
  · rw [h _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      inv.sp]
  · rw [h _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      inv.s0]
  · rw [h _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      inv.s1]
  · rw [h _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      inv.zero]

theorem IInv.regs (inv : IInv R G ptr len out ilen M0 f0 Mx g) {g' : Fin 32 → Word}
    (h : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → g' r = g r) :
    IInv R G ptr len out ilen M0 f0 Mx g' :=
  inv.regsT fun r h0 h1 h2 h3 h4 h5 _ h7 => h r h0 h1 h2 h3 h4 h5 h7

end Hdr

/-- From `m`, `image::parse` reaches offset 0x15A past the header. -/
def HdrOk (P R G ptr len out ilen : Word) (M0 : Word → BitVec 8) (f0 : Fin 32 → Word)
    (sv cnt : BitVec 8) (entry pos : Word) (m : Machine) : Prop :=
  ∃ m' Mx g, Steps m m' ∧ St Mx P m' 0x15A g ∧ IInv R G ptr len out ilen M0 f0 Mx g ∧
    memLoad32 Mx (G + 0x18 + 8) = pos ∧ g s2 = sv.zeroExtend 32 ∧ g s3 = cnt.zeroExtend 32 ∧
    g s4 = entry ∧ memLoad32 Mx (G + 8) = entry ∧ memLoad32 Mx (G + 0xC) = cnt.zeroExtend 32

/-- What the machine at `m` does with the header, given what `hdrW` decides. -/
def HPost (P R G ptr len out ilen : Word) (M0 : Word → BitVec 8) (f0 : Fin 32 → Word) (m : Machine) :
    Except (BitVec 8) (BitVec 8 × BitVec 8 × Word × Word) → Prop
  | .error e => IErrDone R G out M0 f0 e m
  | .ok (sv, cnt, entry, pos) => HdrOk P R G ptr len out ilen M0 f0 sv cnt entry pos m

section Hdr

variable {P R G ptr len out ilen : Word} {M0 Mx : Word → BitVec 8} {f0 g : Fin 32 → Word}

theorem IErrDone.pre {m m' : Machine} {e : BitVec 8} (c : Steps m m') (h : IErrDone R G out M0 f0 e m') :
    IErrDone R G out M0 f0 e m :=
  let ⟨n, c', rest⟩ := h; ⟨n, c.trans c', rest⟩

theorem HPost.pre {m m' : Machine} (c : Steps m m') :
    ∀ r, HPost P R G ptr len out ilen M0 f0 m' r → HPost P R G ptr len out ilen M0 f0 m r
  | .error _, h => IErrDone.pre c h
  | .ok _, ⟨n, Mx, g, c', rest⟩ => ⟨n, Mx, g, c.trans c', rest⟩

theorem upd_a0 (g : Fin 32 → Word) (v : Word) : upd g a0 v a0 = v := by simp +decide [upd]

theorem zext_lsb8 (b : BitVec 8) : (b.zeroExtend 32).extractLsb' 0 8 = b := by revert b; decide

/-- A range of the stack region is apart from `image::parse`'s code. -/
theorem IEnv.stack_parse (env : IEnv P R G ptr len out) (c n : Nat) (hn : c + n ≤ 0x190) :
    Sep (R + BitVec.ofNat 32 c) n P imageParseCode.length := by
  have := env.stack_code c n hn 0x2AE imageParseCode.length (by decide)
  rwa [← ip_wP P] at this

/-- Offset 0x146: `Reader::u32` failed, with the error byte at `G + 0x25`. -/
theorem ip_e146 (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0x146 g)
    {e : BitVec 8} (h : Mx (G + 0x25) = e) : IErrDone R G out M0 f0 e m := by
  have hc := (inv.code env code0).parse
  obtain ⟨m1, d1, u1⟩ := s.lbu hc ip_at_146 (off' := 0x14A) (by decide)
  have inv1 := inv.setReg (rd := a0) (v := (Mx (g sp + 0x25)).zeroExtend 32)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.jump hc ip_at_14a (off' := 0xB6) (by decide)
    (by rw [u1.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0xB6 (by decide)))
  refine IErrDone.pre (.cons d1 (.single d2)) (ip_errB6 env code0 inv1 u2 ?_)
  rw [upd_a0, inv.sp, h, zext_lsb8]

/-- Offset 0x14C: the image-length check, then the header's last stores. -/
theorem ip_len2 (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0x14C g)
    {pos ln entry : Word} {sv cnt : BitVec 8} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos)
    (hln : memLoad32 Mx (G + 0x28) = ln) (h2 : g s2 = sv.zeroExtend 32) (h3 : g s3 = cnt.zeroExtend 32)
    (h4 : g s4 = entry) :
    (ln = ilen ∧ HdrOk P R G ptr len out ilen M0 f0 sv cnt entry pos m) ∨
      (ln ≠ ilen ∧ IErrDone R G out M0 f0 7 m) := by
  have hc := (inv.code env code0).parse
  obtain ⟨m1, d1, u1⟩ := s.lw hc ip_at_14c (off' := 0x14E) (by decide)
    (by rw [inv.sp]; exact aligned_add env.hG (k := 0x28) (by decide))
  rw [inv.sp, hln] at u1
  have inv1 := inv.setReg (rd := a0) (v := ln) (by decide) (by decide) (by decide) (by decide)
  have e1 : upd g a0 ln s1 = ilen := by rw [show upd g a0 ln s1 = g s1 by simp +decide [upd], inv.s1]
  by_cases hl : ln = ilen
  · refine .inl ⟨hl, ?_⟩
    obtain ⟨m2, d2, u2⟩ := u1.notTaken hc 0x152 ip_at_14e (by decide)
      (by rw [upd_a0, e1, hl]; simp [branchTaken])
    have hs : ∀ r, r ≠ a0 → upd g a0 ln r = g r := fun r hr => by
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd, inv.zero]
      · simp [upd, h0, hr]
    obtain ⟨m3, d3, u3⟩ := u2.sw hc ip_at_152 (off' := 0x154) (by decide)
      (by rw [hs sp (by decide), inv.sp]; exact aligned_add env.hG (k := 8) (by decide))
    rw [hs sp (by decide), hs s4 (by decide), inv.sp, h4] at u3
    have c3 : CodeIn (memStore32 Mx (G + 8) entry) P imageParseCode :=
      hc.store32 (by rw [show G + 8 = R + BitVec.ofNat 32 0x38 from env.g_ofs 8]
                     exact env.stack_parse 0x38 4 (by omega))
    obtain ⟨m4, d4, u4⟩ := u3.aluImm c3 ip_at_154 (off' := 0x158) (by decide)
    rw [hs s3 (by decide), h3, zext_and_ff] at u4
    have hs4 : ∀ r, r ≠ a0 → upd (upd g a0 ln) a0 (cnt.zeroExtend 32) r = g r := fun r hr => by
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd, inv.zero]
      · simp [upd, h0, hr]
    obtain ⟨m5, d5, u5⟩ := u4.sw c3 ip_at_158 (off' := 0x15A) (by decide)
      (by rw [hs4 sp (by decide), inv.sp]; exact aligned_add env.hG (k := 0xC) (by decide))
    rw [hs4 sp (by decide), inv.sp, upd_a0] at u5
    have inv4 := inv1.setReg (rd := a0) (v := cnt.zeroExtend 32) (by decide) (by decide) (by decide)
      (by decide)
    have eP : G + 0x18 + 8 = G + BitVec.ofNat 32 0x20 := by rw [BitVec.add_assoc]; rfl
    have s8 : ∀ x, Sep R 0x48 x 1 → ∀ c, 0x38 ≤ c → c + 4 ≤ 0x48 → Sep (R + BitVec.ofNat 32 c) 4 x 1 :=
      fun x h c h1 h2 => h.sub (c := c) (l := 4) (by omega)
    refine ⟨m5, _, _, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5)))), u5,
      inv4.mem env fun x h _ => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have a1 : Sep (G + 0xC) 4 x 1 := by
        rw [show G + 0xC = R + BitVec.ofNat 32 0x3C from env.g_ofs 0xC]
        exact s8 x h 0x3C (by omega) (by omega)
      have a2 : Sep (G + 8) 4 x 1 := by
        rw [show G + 8 = R + BitVec.ofNat 32 0x38 from env.g_ofs 8]
        exact s8 x h 0x38 (by omega) (by omega)
      rw [memStore32_get_sep a1, memStore32_get_sep a2]
    · rw [eP, memLoad32_store32_sep (show Sep (G + 0xC) 4 (G + BitVec.ofNat 32 0x20) 4 from
          sep_offsets G (c := 0xC) (n := 4) (d := 0x20) (k := 4) (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 8) 4 (G + BitVec.ofNat 32 0x20) 4 from
          sep_offsets G (c := 8) (n := 4) (d := 0x20) (k := 4) (by omega) (by omega) (by omega)), ← eP, hpos]
    · rw [hs4 s2 (by decide), h2]
    · rw [hs4 s3 (by decide), h3]
    · rw [hs4 s4 (by decide), h4]
    · rw [memLoad32_store32_sep (show Sep (G + 0xC) 4 (G + 8) 4 from
          sep_offsets G (c := 0xC) (n := 4) (d := 8) (k := 4) (by omega) (by omega) (by omega)), memLoad32_store32_same]
    · exact memLoad32_store32_same _ _ _
  · refine .inr ⟨hl, ?_⟩
    obtain ⟨m2, d2, u2⟩ := u1.taken hc 0x2E4 ip_at_14e (by decide)
      (by rw [upd_a0, e1]; exact bne_iff_ne.mpr hl)
    obtain ⟨m3, d3, u3⟩ := u2.aluImm hc ip_at_2e4 (off' := 0x2E6) (by decide)
    have inv3 := inv1.setReg (rd := a0) (v := aluEval .add (upd g a0 ln x0) 7)
      (by decide) (by decide) (by decide) (by decide)
    obtain ⟨m4, d4, u4⟩ := u3.jump hc ip_at_2e6 (off' := 0xB6) (by decide)
      (by rw [u3.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0xB6 (by decide)))
    refine IErrDone.pre (.cons d2 (.cons d3 (.single d4))) (ip_errB6 env code0 inv3 u4 ?_)
      |> IErrDone.pre (.single d1)
    rw [upd_a0]; simp [upd, aluEval]

theorem ofs (a b c : Nat) (h : a + b = c) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 c := by
  rw [ofNat_add_ofNat, h]

/-- A call to `Reader::u32` with its result at `G + 0x24`, through the load of
its tag byte. -/
theorem ip_rd32 (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} {off : Nat} (s : St Mx P m off g)
    {pos o : Word} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos)
    (i1 : fetchRel imageParseCode off = some (.aluImm .add a0 sp 0x24, 2))
    (i2 : fetchRel imageParseCode (off + 2) = some (.aluImm .add a1 sp 0x18, 2))
    (i3 : fetchRel imageParseCode (off + 4) = some (.auipc ra 0, 4))
    (i4 : fetchRel imageParseCode (off + 4 + 4) = some (.jalr ra ra o, 4))
    (i5 : fetchRel imageParseCode (off + 4 + 8) = some (.load .lbu a0 sp 0x24, 4))
    (hb : P + BitVec.ofNat 32 (off + 4) + 0 + o = P + 0x420) (hoff : off % 2 = 0) :
    ∃ m' My g', Steps m m' ∧ St My P m' (off + 4 + 8 + 4) g' ∧ IInv R G ptr len out ilen M0 f0 My g' ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → g' r = g r) ∧
      match bytesResult ptr len pos 4 with
      | none => g' a0 = 1 ∧ My (G + 0x25) = 0
      | some (p, e) => g' a0 = 0 ∧ memLoad32 My (G + 0x28) = memLoad32 M0 p ∧
          memLoad32 My (G + 0x18 + 8) = e := by
  have hc := (inv.code env code0).parse
  have hz := inv.zero
  obtain ⟨m1, d1, u1⟩ := s.aluImm hc i1 (off' := off + 2) (ofNat_add_ofNat off 2)
  obtain ⟨m2, d2, u2⟩ := u1.aluImm hc i2 (off' := off + 4) (ofNat_add_ofNat (off + 2) 2)
  have v1 : upd g a0 (aluEval .add (g sp) 0x24) sp = G := by rw [updz hz (by decide), inv.sp]
  rw [v1] at u2
  have f2o : ∀ r, r ≠ a0 → r ≠ a1 →
      upd (upd g a0 (aluEval .add (g sp) 0x24)) a1 (aluEval .add G 0x18) r = g r := fun r h0 h1 => by
    rw [updz (by simp) h1, updz hz h0]
  obtain ⟨m3, c3, u3, sp3, fr3, mem3⟩ := ip_u32 env 0x24 (by omega) (by omega) (by omega) u2
    (inv.code env code0) i3 i4 hb (even_at P env.hP (off + 4 + 8) (by omega))
    (by rw [f2o sp (by decide) (by decide), inv.sp])
    (by rw [updz (by simp) (by decide), upd_a0]; show g sp + _ = _; rw [inv.sp]; rfl)
    (by simp +decide [upd]; rfl) inv.rdp inv.rdl
  obtain ⟨invM, res⟩ := IInv.u32 env inv hpos (c := 0x24) (by omega) (by omega) mem3
  have inv3 : IInv R G ptr len out ilen M0 f0 m3.mem (reg m3) :=
    invM.regs fun r h0 h1 h2 h3 h4 h5 h7 => by rw [fr3 r h0 h1 h2 h3 h4 h5 h7, f2o r h0 h1]
  obtain ⟨m4, d4, u4⟩ := u3.lbu (inv3.code env code0).parse i5 (off' := off + 4 + 8 + 4)
    (ofNat_add_ofNat _ 4)
  rw [sp3] at u4
  refine ⟨m4, _, _, (Steps.cons d1 (.cons d2 c3)).trans (.single d4), u4,
    inv3.setReg (by decide) (by decide) (by decide) (by decide),
    fun r h0 h1 h2 h3 h4 h5 h7 => by rw [updz (by rw [← u3.regs]; rfl) h0, fr3 r h0 h1 h2 h3 h4 h5 h7,
      f2o r h0 h1], ?_⟩
  revert res
  rcases bytesResult ptr len pos 4 with _ | ⟨p, e⟩
  · rintro ⟨r1, r2⟩
    refine ⟨?_, ?_⟩
    · rw [upd_a0, show m3.mem (G + 0x24) = 1 from r1]; rfl
    · rwa [show G + BitVec.ofNat 32 0x24 + 1 = G + 0x25 by rw [BitVec.add_assoc]; rfl] at r2
  · rintro ⟨r1, r2, r3⟩
    refine ⟨?_, ?_, r3⟩
    · rw [upd_a0, show m3.mem (G + 0x24) = 0 from r1]; rfl
    · rwa [show G + BitVec.ofNat 32 0x24 + 4 = G + 0x28 by rw [BitVec.add_assoc]; rfl] at r2

/-- From offset 0x134: the image length. -/
theorem ip_hdrLn (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0x134 g)
    {pos entry : Word} {sv cnt : BitVec 8} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos)
    (h2 : g s2 = sv.zeroExtend 32) (h3 : g s3 = cnt.zeroExtend 32) (h4 : g s4 = entry) :
    HPost P R G ptr len out ilen M0 f0 m (hdrLn M0 ptr len ilen sv cnt entry pos) := by
  obtain ⟨m1, My, g1, c1, u1, inv1, fr1, res⟩ := ip_rd32 env code0 inv s hpos ip_at_134 ip_at_136
    ip_at_138 ip_at_13c ip_at_140 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
  have hc := (inv1.code env code0).parse
  unfold hdrLn rdU32 rdB
  revert res
  rcases bytesResult ptr len pos 4 with _ | ⟨p, e⟩
  · rintro ⟨r1, r2⟩
    obtain ⟨m2, d2, u2⟩ := u1.notTaken hc 0x146 ip_at_144 (by decide) (by rw [r1, inv1.zero]; decide)
    exact IErrDone.pre (c1.trans (.single d2)) (ip_e146 env code0 inv1 u2 r2)
  · rintro ⟨r1, r2, r3⟩
    obtain ⟨m2, d2, u2⟩ := u1.taken hc 0x14C ip_at_144 (by decide) (by rw [r1, inv1.zero]; decide)
    have k : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → g1 r = g r := fr1
    rcases ip_len2 env code0 inv1 u2 r3 r2 (by rw [k s2 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), h2])
      (by rw [k s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h3])
      (by rw [k s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h4])
      with ⟨hl, ok⟩ | ⟨hl, err⟩
    · show HPost P R G ptr len out ilen M0 f0 m
        (if (memLoad32 M0 p != ilen) = true then .error 7 else .ok (sv, cnt, entry, e))
      rw [show (memLoad32 M0 p != ilen) = false by simp [hl]]
      exact HPost.pre (c1.trans (.single d2)) _ ok
    · show HPost P R G ptr len out ilen M0 f0 m
        (if (memLoad32 M0 p != ilen) = true then .error 7 else .ok (sv, cnt, entry, e))
      rw [show (memLoad32 M0 p != ilen) = true by simp [hl]]
      exact IErrDone.pre (c1.trans (.single d2)) err

/-- From offset 0x120: the entry point, then the image length. -/
theorem ip_hdrLen (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0x120 g)
    {pos : Word} {sv cnt : BitVec 8} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos)
    (h2 : g s2 = sv.zeroExtend 32) (h3 : g s3 = cnt.zeroExtend 32) :
    HPost P R G ptr len out ilen M0 f0 m (hdrLen M0 ptr len ilen sv cnt pos) := by
  obtain ⟨m1, My, g1, c1, u1, inv1, fr1, res⟩ := ip_rd32 env code0 inv s hpos ip_at_120 ip_at_122
    ip_at_124 ip_at_128 ip_at_12c (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
  have hc := (inv1.code env code0).parse
  have k : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → g1 r = g r := fr1
  unfold hdrLen rdU32 rdB
  revert res
  rcases bytesResult ptr len pos 4 with _ | ⟨p, e⟩
  · rintro ⟨r1, r2⟩
    obtain ⟨m2, d2, u2⟩ := u1.taken hc 0x146 ip_at_130 (by decide) (by rw [r1, inv1.zero]; decide)
    exact IErrDone.pre (c1.trans (.single d2)) (ip_e146 env code0 inv1 u2 r2)
  · rintro ⟨r1, r2, r3⟩
    obtain ⟨m2, d2, u2⟩ := u1.notTaken hc 0x132 ip_at_130 (by decide) (by rw [r1, inv1.zero]; decide)
    obtain ⟨m3, d3, u3⟩ := u2.lw hc ip_at_132 (off' := 0x134) (by decide)
      (by rw [inv1.sp]; exact aligned_add env.hG (k := 0x28) (by decide))
    rw [inv1.sp, r2] at u3
    have inv3 := inv1.setReg (rd := s4) (v := memLoad32 M0 p) (by decide) (by decide) (by decide)
      (by decide)
    have z1 := inv1.zero
    show HPost P R G ptr len out ilen M0 f0 m (hdrLn M0 ptr len ilen sv cnt (memLoad32 M0 p) e)
    exact HPost.pre (c1.trans (.cons d2 (.single d3))) _ (ip_hdrLn env code0 inv3 u3 r3
      (by rw [updz z1 (by decide), k s2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h2])
      (by rw [updz z1 (by decide), k s3 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h3])
      (by simp +decide [upd]))

/-- From offset 0x10A: the two reserved bytes, then the rest. -/
theorem ip_cntRes (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0x10A g)
    {pos : Word} {sv cnt : BitVec 8} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos)
    (h2 : g s2 = sv.zeroExtend 32) (h3 : g s3 = cnt.zeroExtend 32) :
    HPost P R G ptr len out ilen M0 f0 m
      (Except.bind (rdRes M0 ptr len 2 pos) fun pos => hdrLen M0 ptr len ilen sv cnt pos) := by
  have hc := (inv.code env code0).parse
  have hz := inv.zero
  obtain ⟨m1, d1, u1⟩ := s.aluImm hc ip_at_10a (off' := 0x10C) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.aluImm hc ip_at_10c (off' := 0x10E) (by decide)
  have f2o : ∀ r, r ≠ a0 → r ≠ a1 → upd (upd g a0 (aluEval .add (g sp) 0x18)) a1
      (aluEval .add (upd g a0 (aluEval .add (g sp) 0x18) x0) 2) r = g r := fun r h0 h1 => by
    rw [updz (by simp) h1, updz hz h0]
  obtain ⟨m3, c3, u3, sp3, a03, fr3, mem3⟩ := ip_reserved env u2 (inv.code env code0) (n := 2)
    ip_at_10e ip_at_112 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (even_at P env.hP 0x116 (by decide)) (by rw [f2o sp (by decide) (by decide), inv.sp])
    (by rw [updz (by simp) (by decide), upd_a0]; show g sp + _ = _; rw [inv.sp])
    (by rw [upd_same (by decide)]; show upd g a0 _ 0 + 2 = 2; rw [upd_zero]; rfl)
    (by decide) inv.rdp inv.rdl
  obtain ⟨invM, adv⟩ := IInv.adv env inv hpos (My := m3.mem) (n := 2) (c := 32) (N := 16) (by omega)
    fun x hx => by rw [mem3 x hx, reservedMem_pos]
  have inv3 : IInv R G ptr len out ilen M0 f0 m3.mem (reg m3) :=
    invM.regs fun r h0 h1 h2 h3 h4 h5 h7 => by rw [fr3 r h0 h1 h2 h3 h4 h5 h7, f2o r h0 h1]
  have k3 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m3 r = g r :=
    fun r h0 h1 h2 h3 h4 h5 h7 => by rw [fr3 r h0 h1 h2 h3 h4 h5 h7, f2o r h0 h1]
  rw [resR env inv hpos] at a03
  obtain ⟨m4, g4, c4, k4, br⟩ := check_br u3 (inv3.code env code0).parse ip_at_116 ip_at_11a ip_at_11e
    (T := 0xB6) (by decide)
  have inv4 : IInv R G ptr len out ilen M0 f0 m3.mem g4 :=
    inv3.regs fun r _ h1 _ _ _ _ _ => k4 r h1
  have g4a : g4 a0 = reg m3 a0 := k4 a0 (by decide)
  have pre : Steps m m3 := (Steps.cons d1 (.cons d2 c3))
  unfold rdRes rdB
  revert a03
  rcases hb : bytesResult ptr len pos 2 with _ | ⟨p, e⟩ <;> intro a03
  · dsimp only at a03
    rcases br with ⟨h, -⟩ | ⟨-, u4⟩
    · rw [a03] at h; exact absurd h (by decide)
    · exact IErrDone.pre (pre.trans c4) (ip_errB6 env code0 inv4 u4 (by rw [g4a, a03]; rfl))
  · dsimp only at a03
    show HPost P R G ptr len out ilen M0 f0 m (Except.bind
      (if allZero M0 p (2 : Word).toNat = true then .ok e else .error 4)
      fun pos => hdrLen M0 ptr len ilen sv cnt pos)
    by_cases hz2 : allZero M0 p (2 : Word).toNat = true
    · rw [ite_eq_left hz2]
      rw [ite_eq_left hz2] at a03
      rcases br with ⟨-, u4⟩ | ⟨h, -⟩
      · exact HPost.pre (pre.trans c4) _ (ip_hdrLen env code0 inv4 u4 (adv p e hb)
          (by rw [k4 s2 (by decide), k3 s2 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide), h2])
          (by rw [k4 s3 (by decide), k3 s3 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide), h3]))
      · rw [a03] at h; exact absurd rfl h
    · rw [ite_eq_right hz2]
      rw [ite_eq_right hz2] at a03
      rcases br with ⟨h, -⟩ | ⟨-, u4⟩
      · rw [a03] at h; exact absurd h (by decide)
      · exact IErrDone.pre (pre.trans c4) (ip_errB6 env code0 inv4 u4 (by rw [g4a, a03]; rfl))

theorem cnt_chk (b : BitVec 8) :
    branchTaken .bgeu (aluEval .add 0 0xEF) (aluEval .and (aluEval .add (b.zeroExtend 32) 0xFFFFFFEF) 0xFF) =
      decide (b.toNat = 0 ∨ 16 < b.toNat) := by
  revert b; decide

/-- From offset 0xE2: the segment count, then the rest. -/
theorem ip_hdrCnt (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0xE2 g)
    {pos : Word} {sv : BitVec 8} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos)
    (h2 : g s2 = sv.zeroExtend 32) :
    HPost P R G ptr len out ilen M0 f0 m (hdrCnt M0 ptr len ilen sv pos) := by
  have hc := (inv.code env code0).parse
  have hz := inv.zero
  obtain ⟨m1, d1, u1⟩ := s.aluImm hc ip_at_e2 (off' := 0xE4) (by decide)
  obtain ⟨m2, c2, u2, sp2, a02, a12, fr2, mem2⟩ := ip_u8 env u1 (inv.code env code0) ip_at_e4
    ip_at_e8 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xEC (by decide))
    (by rw [updz hz (by decide), inv.sp]) (by rw [upd_a0]; show g sp + _ = _; rw [inv.sp])
    inv.rdp inv.rdl
  obtain ⟨invM, adv⟩ := IInv.adv env inv hpos (My := m2.mem) (n := 1) (c := 32) (N := 16) (by omega)
    fun x hx => by rw [mem2 x hx, reservedMem_pos]
  have k2 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m2 r = g r :=
    fun r h0 h1 h2 h3 h4 h5 h7 => by rw [fr2 r h0 h1 h2 h3 h4 h5 h7, updz hz h0]
  have inv2 : IInv R G ptr len out ilen M0 f0 m2.mem (reg m2) := invM.regs k2
  have hc2 := (inv2.code env code0).parse
  have z2 := inv2.zero
  rw [u8R env inv hpos] at a02 a12
  obtain ⟨m3, d3, u3⟩ := u2.aluImm hc2 ip_at_ec (off' := 0xEE) (by decide)
  obtain ⟨m4, d4, u4⟩ := u3.alu hc2 ip_at_ee (off' := 0xF0) (by decide)
  have inv4 := (inv2.setReg (rd := a0) (v := aluEval .and (reg m2 a0) 1) (by decide) (by decide)
    (by decide) (by decide)).setReg (rd := s3)
    (v := aluEval .add (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1) x0)
      (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1) a1)) (by decide) (by decide) (by decide) (by decide)
  have hc4 := (inv4.code env code0).parse
  have v3 : aluEval .add (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1) x0)
      (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1) a1) = reg m2 a1 := by
    rw [updz z2 (by decide)]; show (0 : Word) + _ = _; exact BitVec.zero_add _
  rw [v3] at u4 inv4
  have g4a0 : upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1)) s3 (reg m2 a1) a0 =
      aluEval .and (reg m2 a0) 1 := by rw [updz (by simp) (by decide), upd_a0]
  have g4s3 : upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1)) s3 (reg m2 a1) s3 = reg m2 a1 :=
    upd_same (by decide)
  have g4o : ∀ r, r ≠ a0 → r ≠ s3 →
      upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1)) s3 (reg m2 a1) r = reg m2 r :=
    fun r h0 h3 => by rw [updz (by simp) h3, updz z2 h0]
  have pre : Steps m m4 := .cons d1 (c2.trans (.cons d3 (.single d4)))
  unfold hdrCnt rdU8 rdB
  revert a02 a12
  rcases hb : bytesResult ptr len pos 1 with _ | ⟨p, e⟩ <;> intro a02 a12 <;> dsimp only at a02 a12
  · obtain ⟨m5, d5, u5⟩ := u4.notTaken hc4 0xF2 ip_at_f0 (by decide)
      (by rw [g4a0, a02, upd_zero]; decide)
    exact IErrDone.pre (pre.trans (.single d5)) (ip_errF2 env code0 inv4 u5 (by rw [g4s3, a12]; rfl))
  · obtain ⟨m5, d5, u5⟩ := u4.taken hc4 0xFA ip_at_f0 (by decide)
      (by rw [g4a0, a02, upd_zero]; decide)
    show HPost P R G ptr len out ilen M0 f0 m
      (if (M0 p).toNat = 0 ∨ 16 < (M0 p).toNat then .error 5
       else Except.bind (rdRes M0 ptr len 2 e) fun pos => hdrLen M0 ptr len ilen sv (M0 p) pos)
    obtain ⟨m6, d6, u6⟩ := u5.aluImm hc4 ip_at_fa (off' := 0xFE) (by decide)
    obtain ⟨m7, d7, u7⟩ := u6.aluImm hc4 ip_at_fe (off' := 0x102) (by decide)
    obtain ⟨m8, d8, u8⟩ := u7.aluImm hc4 ip_at_102 (off' := 0x106) (by decide)
    have gs : ∀ v w x : Word, ∀ r, r ≠ a0 → r ≠ a1 → r ≠ s3 →
        upd (upd (upd (upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1)) s3 (reg m2 a1)) a0 v) a0 w)
          a1 x r = reg m2 r := fun v w x r h0 h1 h3 => by
      rw [updz (by simp) h1, updz (by simp) h0, updz (by simp) h0, g4o r h0 h3]
    have q : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ s3 →
        reg m2 r = g r := fun r h0 h1 h2 h3 h4 h5 h7 _ => k2 r h0 h1 h2 h3 h4 h5 h7
    by_cases hcnt : (M0 p).toNat = 0 ∨ 16 < (M0 p).toNat
    · rw [ite_eq_left hcnt]
      obtain ⟨m9, d9, u9⟩ := u8.taken hc4 0xB4 ip_at_106 (by decide) (by
        simp only [upd_a0, show ∀ (f : Fin 32 → Word) v, upd f a1 v a1 = v from fun f v => upd_same (by decide)]
        rw [updz (by simp) (show (a0 : Fin 32) ≠ a1 by decide), upd_a0,
          show ∀ (f : Fin 32 → Word) v, upd f a0 v x0 = 0 from fun _ _ => rfl, g4s3, a12, cnt_chk]
        simpa using hcnt)
      obtain ⟨m10, d10, u10⟩ := u9.aluImm hc4 ip_at_b4 (off' := 0xB6) (by decide)
      exact IErrDone.pre (pre.trans (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.single d10)))))))
        (ip_errB6 env code0 (inv4.regs fun r h0 h1 _ _ _ _ _ => by
            rw [updz (by simp) h0, updz (by simp) h1, updz (by simp) h0, updz (by simp) h0]) u10
          (by rw [upd_a0]; simp [upd, aluEval]))
    · rw [ite_eq_right hcnt]
      obtain ⟨m9, d9, u9⟩ := u8.notTaken hc4 0x10A ip_at_106 (by decide) (by
        simp only [upd_a0, show ∀ (f : Fin 32 → Word) v, upd f a1 v a1 = v from fun f v => upd_same (by decide)]
        rw [updz (by simp) (show (a0 : Fin 32) ≠ a1 by decide), upd_a0,
          show ∀ (f : Fin 32 → Word) v, upd f a0 v x0 = 0 from fun _ _ => rfl, g4s3, a12, cnt_chk]
        simpa using hcnt)
      exact HPost.pre (pre.trans (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.single d9)))))) _
        (ip_cntRes env code0 (inv4.regs fun r h0 h1 _ _ _ _ _ => by
            rw [updz (by simp) h1, updz (by simp) h0, updz (by simp) h0]) u9 (adv p e hb)
          (by rw [gs _ _ _ s2 (by decide) (by decide) (by decide), q s2 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide), h2])
          (by rw [updz (by simp) (show (s3 : Fin 32) ≠ a1 by decide),
            updz (by simp) (show (s3 : Fin 32) ≠ a0 by decide),
            updz (by simp) (show (s3 : Fin 32) ≠ a0 by decide), g4s3, a12]))

theorem sv_chk (b : BitVec 8) :
    branchTaken .bgeu (aluEval .add 0 0x10) (b.zeroExtend 32) = decide (b.toNat ≤ 16) := by
  revert b; decide

/-- From offset 0x8A: the security version, then the rest. -/
theorem ip_hdrSv (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0x8A g)
    {pos : Word} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos) :
    HPost P R G ptr len out ilen M0 f0 m (hdrSv M0 ptr len ilen pos) := by
  have hc := (inv.code env code0).parse
  have hz := inv.zero
  obtain ⟨m1, d1, u1⟩ := s.aluImm hc ip_at_8a (off' := 0x8C) (by decide)
  obtain ⟨m2, c2, u2, sp2, a02, a12, fr2, mem2⟩ := ip_u8 env u1 (inv.code env code0) ip_at_8c
    ip_at_90 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x94 (by decide))
    (by rw [updz hz (by decide), inv.sp]) (by rw [upd_a0]; show g sp + _ = _; rw [inv.sp])
    inv.rdp inv.rdl
  obtain ⟨invM, adv⟩ := IInv.adv env inv hpos (My := m2.mem) (n := 1) (c := 32) (N := 16) (by omega)
    fun x hx => by rw [mem2 x hx, reservedMem_pos]
  have k2 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m2 r = g r :=
    fun r h0 h1 h2 h3 h4 h5 h7 => by rw [fr2 r h0 h1 h2 h3 h4 h5 h7, updz hz h0]
  have inv2 : IInv R G ptr len out ilen M0 f0 m2.mem (reg m2) := invM.regs k2
  have hc2 := (inv2.code env code0).parse
  have z2 := inv2.zero
  rw [u8R env inv hpos] at a02 a12
  obtain ⟨m3, d3, u3⟩ := u2.aluImm hc2 ip_at_94 (off' := 0x96) (by decide)
  obtain ⟨m4, d4, u4⟩ := u3.alu hc2 ip_at_96 (off' := 0x98) (by decide)
  have v3 : aluEval .add (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1) x0)
      (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1) a1) = reg m2 a1 := by
    rw [updz z2 (by decide)]; show (0 : Word) + _ = _; exact BitVec.zero_add _
  rw [v3] at u4
  have inv4 : IInv R G ptr len out ilen M0 f0 m2.mem
      (upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1)) s2 (reg m2 a1)) :=
    (inv2.setReg (by decide) (by decide) (by decide) (by decide)).setReg (by decide) (by decide)
      (by decide) (by decide)
  have hc4 := (inv4.code env code0).parse
  have g4a0 : upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1)) s2 (reg m2 a1) a0 =
      aluEval .and (reg m2 a0) 1 := by rw [updz (by simp) (by decide), upd_a0]
  have g4s2 : upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1)) s2 (reg m2 a1) s2 = reg m2 a1 :=
    upd_same (by decide)
  have pre : Steps m m4 := .cons d1 (c2.trans (.cons d3 (.single d4)))
  unfold hdrSv rdU8 rdB
  revert a02 a12
  rcases hb : bytesResult ptr len pos 1 with _ | ⟨p, e⟩ <;> intro a02 a12 <;> dsimp only at a02 a12
  · obtain ⟨m5, d5, u5⟩ := u4.notTaken hc4 0x9A ip_at_98 (by decide)
      (by rw [g4a0, a02, upd_zero]; decide)
    exact IErrDone.pre (pre.trans (.single d5)) (ip_err9A env code0 inv4 u5 (by rw [g4s2, a12]; rfl))
  · obtain ⟨m5, d5, u5⟩ := u4.taken hc4 0xAA ip_at_98 (by decide)
      (by rw [g4a0, a02, upd_zero]; decide)
    show HPost P R G ptr len out ilen M0 f0 m
      (if 16 < (M0 p).toNat then .error 5 else hdrCnt M0 ptr len ilen (M0 p) e)
    obtain ⟨m6, d6, u6⟩ := u5.aluImm hc4 ip_at_aa (off' := 0xAE) (by decide)
    rw [show aluEval .and (upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1)) s2 (reg m2 a1) s2) 0xFF =
      (M0 p).zeroExtend 32 by rw [g4s2, a12, zext_and_ff]] at u6
    obtain ⟨m7, d7, u7⟩ := u6.aluImm hc4 ip_at_ae (off' := 0xB0) (by decide)
    have br : branchTaken .bgeu
        (upd (upd (upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1)) s2 (reg m2 a1)) a0
          ((M0 p).zeroExtend 32)) a1 (aluEval .add (upd (upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1))
            s2 (reg m2 a1)) a0 ((M0 p).zeroExtend 32) x0) 0x10) a1)
        (upd (upd (upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1)) s2 (reg m2 a1)) a0
          ((M0 p).zeroExtend 32)) a1 (aluEval .add (upd (upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1))
            s2 (reg m2 a1)) a0 ((M0 p).zeroExtend 32) x0) 0x10) a0) = decide ((M0 p).toNat ≤ 16) := by
      rw [upd_same (by decide), updz (by simp) (show (a0 : Fin 32) ≠ a1 by decide), upd_a0,
        show ∀ (f : Fin 32 → Word) v, upd f a0 v x0 = 0 from fun _ _ => rfl, sv_chk]
    by_cases hsv : 16 < (M0 p).toNat
    · rw [ite_eq_left hsv]
      obtain ⟨m8, d8, u8⟩ := u7.notTaken hc4 0xB4 ip_at_b0 (by decide)
        (by rw [br]; simpa using hsv)
      obtain ⟨m9, d9, u9⟩ := u8.aluImm hc4 ip_at_b4 (off' := 0xB6) (by decide)
      exact IErrDone.pre (pre.trans (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.single d9))))))
        (ip_errB6 env code0 (inv4.regs fun r h0 h1 _ _ _ _ _ => by
            rw [updz (by simp) h0, updz (by simp) h1, updz (by simp) h0]) u9
          (by rw [upd_a0]; simp [upd, aluEval]))
    · rw [ite_eq_right hsv]
      obtain ⟨m8, d8, u8⟩ := u7.taken hc4 0xE2 ip_at_b0 (by decide)
        (by rw [br]; simpa using hsv)
      exact HPost.pre (pre.trans (.cons d5 (.cons d6 (.cons d7 (.single d8))))) _
        (ip_hdrCnt env code0 (inv4.regs fun r h0 h1 _ _ _ _ _ => by
            rw [updz (by simp) h1, updz (by simp) h0]) u8 (adv p e hb)
          (by rw [updz (by simp) (show (s2 : Fin 32) ≠ a1 by decide),
            updz (by simp) (show (s2 : Fin 32) ≠ a0 by decide), g4s2, a12]))

theorem u16_lo (x y : BitVec 8) :
    aluEval .and (x.zeroExtend 32 <<< 24 ||| y.zeroExtend 32 <<< 16 : Word) 1 = 0 := by
  show (_ ||| _) &&& 1 = 0
  have h24 : ∀ b : BitVec 8, (b.zeroExtend 32 <<< 24 : Word) &&& 1 = 0 := by decide
  have h16 : ∀ b : BitVec 8, (b.zeroExtend 32 <<< 16 : Word) &&& 1 = 0 := by decide
  rw [BitVec.and_or_distrib_right, h24, h16]; rfl

/-- From offset 0x6E: the chip id, then the rest. -/
theorem ip_hdrChip (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0x6E g)
    {pos : Word} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos) :
    HPost P R G ptr len out ilen M0 f0 m (hdrChip M0 ptr len ilen pos) := by
  have hc := (inv.code env code0).parse
  have hz := inv.zero
  obtain ⟨m1, d1, u1⟩ := s.aluImm hc ip_at_6e (off' := 0x70) (by decide)
  obtain ⟨m2, c2, u2, sp2, a02, fr2, mem2⟩ := ip_u16 env u1 (inv.code env code0) ip_at_70
    ip_at_74 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x78 (by decide))
    (by rw [updz hz (by decide), inv.sp]) (by rw [upd_a0]; show g sp + _ = _; rw [inv.sp])
    inv.rdp inv.rdl
  obtain ⟨invM, adv⟩ := IInv.adv env inv hpos (My := m2.mem) (n := 2) (c := 32) (N := 16) (by omega)
    fun x hx => by rw [mem2 x hx, u16Mem_pos]
  have k2 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m2 r = g r :=
    fun r h0 h1 h2 h3 h4 h5 h7 => by rw [fr2 r h0 h1 h2 h3 h4 h5 h7, updz hz h0]
  have inv2 : IInv R G ptr len out ilen M0 f0 m2.mem (reg m2) := invM.regs k2
  have hc2 := (inv2.code env code0).parse
  have z2 := inv2.zero
  rw [u16R env inv hpos] at a02
  obtain ⟨m3, d3, u3⟩ := u2.aluImm hc2 ip_at_78 (off' := 0x7C) (by decide)
  have inv3 : IInv R G ptr len out ilen M0 f0 m2.mem (upd (reg m2) a1 (aluEval .and (reg m2 a0) 1)) :=
    inv2.setReg (by decide) (by decide) (by decide) (by decide)
  have g3a1 : upd (reg m2) a1 (aluEval .and (reg m2 a0) 1) a1 = aluEval .and (reg m2 a0) 1 :=
    upd_same (by decide)
  have g3a0 : upd (reg m2) a1 (aluEval .and (reg m2 a0) 1) a0 = reg m2 a0 := updz z2 (by decide)
  have pre : Steps m m3 := .cons d1 (c2.trans (.single d3))
  unfold hdrChip rdU16 rdB
  revert a02
  rcases hb : bytesResult ptr len pos 2 with _ | ⟨p, e⟩ <;> intro a02 <;> dsimp only at a02
  · obtain ⟨m4, d4, u4⟩ := u3.notTaken hc2 0x7E ip_at_7c (by decide)
      (by rw [g3a1, a02, upd_zero]; decide)
    obtain ⟨m5, d5, u5⟩ := u4.aluImm hc2 ip_at_7e (off' := 0x80) (by decide)
    obtain ⟨m6, d6, u6⟩ := u5.jump hc2 ip_at_80 (off' := 0xB6) (by decide)
      (by rw [u5.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0xB6 (by decide)))
    exact IErrDone.pre (pre.trans (.cons d4 (.cons d5 (.single d6))))
      (ip_errB6 env code0 (inv3.setReg (by decide) (by decide) (by decide) (by decide)) u6
        (by rw [upd_a0, g3a0, a02]; rfl))
  · obtain ⟨m4, d4, u4⟩ := u3.taken hc2 0x82 ip_at_7c (by decide)
      (by rw [g3a1, a02, u16_lo, upd_zero]; decide)
    obtain ⟨m5, d5, u5⟩ := u4.aluImm hc2 ip_at_82 (off' := 0x84) (by decide)
    rw [show aluEval .srl (upd (reg m2) a1 (aluEval .and (reg m2 a0) 1) a0) 0x10 =
      aluEval .srl ((M0 (p + 1)).zeroExtend 32 <<< 24 ||| (M0 p).zeroExtend 32 <<< 16) 0x10 by
        rw [g3a0, a02]] at u5
    obtain ⟨m6, d6, u6⟩ := u5.aluImm hc2 ip_at_84 (off' := 0x86) (by decide)
    have inv6 := (inv3.setReg (rd := a0)
      (v := aluEval .srl ((M0 (p + 1)).zeroExtend 32 <<< 24 ||| (M0 p).zeroExtend 32 <<< 16) 0x10)
      (by decide) (by decide) (by decide) (by decide)).setReg
      (rd := a1) (v := aluEval .add (upd (upd (reg m2) a1 (aluEval .and (reg m2 a0) 1)) a0
        (aluEval .srl ((M0 (p + 1)).zeroExtend 32 <<< 24 ||| (M0 p).zeroExtend 32 <<< 16) 0x10) x0) 5)
      (by decide) (by decide) (by decide) (by decide)
    have hc6 := (inv6.code env code0).parse
    have v0 : upd (upd (upd (reg m2) a1 (aluEval .and (reg m2 a0) 1)) a0
        (aluEval .srl ((M0 (p + 1)).zeroExtend 32 <<< 24 ||| (M0 p).zeroExtend 32 <<< 16) 0x10)) a1
        (aluEval .add (upd (upd (reg m2) a1 (aluEval .and (reg m2 a0) 1)) a0
          (aluEval .srl ((M0 (p + 1)).zeroExtend 32 <<< 24 ||| (M0 p).zeroExtend 32 <<< 16) 0x10) x0) 5) a0 =
        ((M0 (p + 1)).zeroExtend 32 <<< 24 ||| (M0 p).zeroExtend 32 <<< 16 : Word) >>> 16 := by
      rw [updz (by simp) (by decide), upd_a0]; rfl
    have v1 : upd (upd (upd (reg m2) a1 (aluEval .and (reg m2 a0) 1)) a0
        (aluEval .srl ((M0 (p + 1)).zeroExtend 32 <<< 24 ||| (M0 p).zeroExtend 32 <<< 16) 0x10)) a1
        (aluEval .add (upd (upd (reg m2) a1 (aluEval .and (reg m2 a0) 1)) a0
          (aluEval .srl ((M0 (p + 1)).zeroExtend 32 <<< 24 ||| (M0 p).zeroExtend 32 <<< 16) 0x10) x0) 5) a1 =
        5 := by rw [upd_same (by decide)]; rfl
    show HPost P R G ptr len out ilen M0 f0 m
      (if (((M0 (p + 1)).zeroExtend 32 <<< 24 ||| (M0 p).zeroExtend 32 <<< 16 : Word) >>> 16 != 5) = true
       then .error 8 else hdrSv M0 ptr len ilen e)
    by_cases hch : (((M0 (p + 1)).zeroExtend 32 <<< 24 ||| (M0 p).zeroExtend 32 <<< 16 : Word) >>> 16 != 5) = true
    · rw [ite_eq_left hch]
      obtain ⟨m7, d7, u7⟩ := u6.taken hc6 0xA6 ip_at_86 (by decide) (by rw [v0, v1]; exact hch)
      obtain ⟨m8, d8, u8⟩ := u7.aluImm hc6 ip_at_a6 (off' := 0xA8) (by decide)
      obtain ⟨m9, d9, u9⟩ := u8.jump hc6 ip_at_a8 (off' := 0xB6) (by decide)
        (by rw [u8.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0xB6 (by decide)))
      exact IErrDone.pre (pre.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.single d9)))))))
        (ip_errB6 env code0 (inv6.setReg (rd := a0) (by decide) (by decide) (by decide) (by decide)) u9
          (by rw [upd_a0]; simp [upd, aluEval]))
    · rw [ite_eq_right hch]
      obtain ⟨m7, d7, u7⟩ := u6.notTaken hc6 0x8A ip_at_86 (by decide)
        (by rw [v0, v1]; exact Bool.eq_false_iff.mpr hch)
      exact HPost.pre (pre.trans (.cons d4 (.cons d5 (.cons d6 (.single d7))))) _
        (ip_hdrSv env code0 inv6 u7 (adv p e hb))

/-- From offset 0x5A: the format version, then the rest. -/
theorem ip_hdrVer (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0x5A g)
    {pos : Word} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos) :
    HPost P R G ptr len out ilen M0 f0 m
      (Except.bind (rdVer1 M0 ptr len pos) fun pos => hdrChip M0 ptr len ilen pos) := by
  have hc := (inv.code env code0).parse
  have hz := inv.zero
  obtain ⟨m1, d1, u1⟩ := s.aluImm hc ip_at_5a (off' := 0x5C) (by decide)
  obtain ⟨m2, c2, u2, sp2, a02, fr2, mem2⟩ := ip_version env u1 (inv.code env code0) ip_at_5c
    ip_at_60 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x64 (by decide))
    (by rw [updz hz (by decide), inv.sp]) (by rw [upd_a0]; show g sp + _ = _; rw [inv.sp])
    inv.rdp inv.rdl
  obtain ⟨invM, adv⟩ := IInv.adv env inv hpos (My := m2.mem) (n := 2) (c := 16) (N := 32) (by omega)
    fun x hx => by rw [mem2 x hx, u16Mem_pos]
  have k2 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m2 r = g r :=
    fun r h0 h1 h2 h3 h4 h5 h7 => by rw [fr2 r h0 h1 h2 h3 h4 h5 h7, updz hz h0]
  have inv2 : IInv R G ptr len out ilen M0 f0 m2.mem (reg m2) := invM.regs k2
  rw [verR env inv hpos] at a02
  obtain ⟨m3, g3, c3, k3, br⟩ := check_br u2 (inv2.code env code0).parse ip_at_64 ip_at_68 ip_at_6c
    (T := 0xB6) (by decide)
  have inv3 : IInv R G ptr len out ilen M0 f0 m2.mem g3 := inv2.regs fun r _ h1 _ _ _ _ _ => k3 r h1
  have g3a : g3 a0 = reg m2 a0 := k3 a0 (by decide)
  have pre : Steps m m2 := .cons d1 c2
  unfold rdVer1 rdU16 rdB
  revert a02
  rcases hb : bytesResult ptr len pos 2 with _ | ⟨p, e⟩ <;> intro a02 <;> dsimp only at a02
  · rcases br with ⟨h, -⟩ | ⟨-, u3⟩
    · rw [a02] at h; exact absurd h (by decide)
    · exact IErrDone.pre (pre.trans c3) (ip_errB6 env code0 inv3 u3 (by rw [g3a, a02]; rfl))
  · show HPost P R G ptr len out ilen M0 f0 m (Except.bind
      (if (((M0 (p + 1)).zeroExtend 32 <<< 24 ||| (M0 p).zeroExtend 32 <<< 16 : Word) >>> 16 == 1) = true
       then .ok e else .error 3) fun pos => hdrChip M0 ptr len ilen pos)
    by_cases hv : (((M0 (p + 1)).zeroExtend 32 <<< 24 ||| (M0 p).zeroExtend 32 <<< 16 : Word) >>> 16 == 1) = true
    · rw [ite_eq_left hv]
      rw [ite_eq_left hv] at a02
      rcases br with ⟨-, u3⟩ | ⟨h, -⟩
      · exact HPost.pre (pre.trans c3) _ (ip_hdrChip env code0 inv3 u3 (adv p e hb))
      · rw [a02] at h; exact absurd rfl h
    · rw [ite_eq_right hv]
      rw [ite_eq_right hv] at a02
      rcases br with ⟨h, -⟩ | ⟨-, u3⟩
      · rw [a02] at h; exact absurd h (by decide)
      · exact IErrDone.pre (pre.trans c3) (ip_errB6 env code0 inv3 u3 (by rw [g3a, a02]; rfl))

/-! ## The prologue -/

/-- Offsets 0 through 0x46: allocate the frame, save `ra` and `s0` through
`s11`, keep the result address and image length, set up the reader, and
load the magic number. -/
def ipProBlock : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFEA0, .aluImm .add a4 sp 0x100, .sw a4 ra 0x5C, .sw a4 s0 0x58,
   .sw a4 s1 0x54, .sw a4 s2 0x50, .sw a4 s3 0x4C, .sw a4 s4 0x48, .sw a4 s5 0x44, .sw a4 s6 0x40,
   .sw a4 s7 0x3C, .sw a4 s8 0x38, .sw a4 s9 0x34, .sw a4 s10 0x30, .sw a4 s11 0x2C,
   .alu .add s1 x0 a3, .alu .add s0 x0 a0, .sw sp a1 0x18, .sw sp a2 0x1C, .sw sp x0 0x20,
   .lui a1 0x4D493000, .aluImm .add a1 a1 0x343, .aluImm .add a0 sp 0x18]

theorem ipPro_end : blockEnd imageParseCode 0 ipProBlock = some 0x48 := by decide

theorem st_out (env : IEnv P R G ptr len out) {x : Word} (hx : Sep R 0x190 x 1) (M : Word → BitVec 8)
    (c : Nat) (v : Word) (hc : c + 4 ≤ 0x160) : memStore32 M (G + BitVec.ofNat 32 c) v x = M x :=
  memStore32_get_sep (by rw [env.g_ofs]; exact hx.sub (c := 0x30 + c) (l := 4) (by omega))

theorem ld_st (M : Word → BitVec 8) (G : Word) (c d : Nat) (v : Word) (hc : c + 4 ≤ 0x160)
    (hd : d + 4 ≤ 0x160) (hc4 : c % 4 = 0) (hd4 : d % 4 = 0) :
    memLoad32 (memStore32 M (G + BitVec.ofNat 32 c) v) (G + BitVec.ofNat 32 d) =
      if c = d then v else memLoad32 M (G + BitVec.ofNat 32 d) := by
  by_cases h : c = d
  · subst h; rw [ite_eq_left rfl]; exact memLoad32_store32_same _ _ _
  · rw [ite_eq_right h]; exact memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega))

theorem gsepP (env : IEnv P R G ptr len out) (c : Nat) (hc : c + 4 ≤ 0x160) :
    Sep (G + BitVec.ofNat 32 c) 4 P imageParseCode.length := by
  rw [env.g_ofs]; exact env.stack_parse (0x30 + c) 4 (by omega)

/-- **The prologue**: from entry to offset 0x48, with `IInv` and the reader
at position 0. -/
theorem ip_prologue (m : Machine) (env : IEnv P R G ptr len out) (code : ICode m.mem P)
    (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ptr) (ha2 : reg m a2 = len)
    (ha3 : reg m a3 = ilen) (hsp : reg m sp = G + 0x160) :
    ∃ m1 M1 g1, Steps m m1 ∧ St M1 P m1 0x48 g1 ∧ IInv R G ptr len out ilen m.mem (reg m) M1 g1 ∧
      memLoad32 M1 (G + 0x18 + 8) = 0 ∧ g1 a0 = G + 0x18 ∧ g1 a1 = 0x4D493343 := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hG := env.hG
  have ok : BlockOk P imageParseCode.length ipProBlock (m.mem, reg m) := by
    simp only [BlockOk, BInstr.ok, BInstr.run, ipProBlock]
    simp +decide only [upd, hsp, aluEval, BitVec.add_assoc, BitVec.reduceAdd, ↓reduceIte, BitVec.add_zero]
    repeat' apply And.intro
    all_goals first
      | trivial
      | (show Sep _ _ _ _; exact gsepP env _ (by decide))
      | exact aligned_add hG (by decide)
  obtain ⟨m1, c1, u1⟩ := St.block ipProBlock s0 code.parse ipPro_end ok
  obtain ⟨M1, hM1⟩ : ∃ M1, (runBlock ipProBlock (m.mem, reg m)).1 = M1 := ⟨_, rfl⟩
  obtain ⟨g1, hg1⟩ : ∃ g1, (runBlock ipProBlock (m.mem, reg m)).2 = g1 := ⟨_, rfl⟩
  rw [hM1, hg1] at u1
  have eM := hM1
  simp only [runBlock, BInstr.run, ipProBlock] at eM
  simp +decide only [upd, hsp, aluEval, BitVec.add_assoc, BitVec.reduceAdd, ↓reduceIte,
    BitVec.add_zero, BitVec.ofNat_eq_ofNat] at eM
  have rk : ∀ r, r ≠ sp → r ≠ a4 → r ≠ s1 → r ≠ RV32.s0 → r ≠ a1 → r ≠ a0 → g1 r = reg m r :=
    fun r h1 h2 h3 h4 h5 h6 => by
      rw [← hg1]; simp only [runBlock, BInstr.run, ipProBlock]
      rw [updz (by simp) h6, updz (by simp) h5, updz (by simp) h5, updz (by simp) h4, updz (by simp) h3,
        updz (by simp) h2, updz hz h1]
  have ld : ∀ d, d + 4 ≤ 0x160 → d % 4 = 0 → memLoad32 M1 (G + BitVec.ofNat 32 d) =
      if 0x20 = d then 0 else if 0x1C = d then reg m a2 else if 0x18 = d then reg m a1 else
      if 0x12C = d then reg m s11 else if 0x130 = d then reg m s10 else if 0x134 = d then reg m s9 else
      if 0x138 = d then reg m s8 else if 0x13C = d then reg m s7 else if 0x140 = d then reg m s6 else
      if 0x144 = d then reg m s5 else if 0x148 = d then reg m s4 else if 0x14C = d then reg m s3 else
      if 0x150 = d then reg m s2 else if 0x154 = d then reg m s1 else if 0x158 = d then reg m RV32.s0 else
      if 0x15C = d then reg m ra else memLoad32 m.mem (G + BitVec.ofNat 32 d) := fun d hd h4 => by
    rw [← eM]
    repeat rw [ld_st _ _ _ _ _ _ hd _ h4]
    all_goals first | rfl | decide
  refine ⟨m1, M1, g1, c1, u1, ⟨fun x hx => ?_, fun p hp => ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [← eM]; simp (disch := decide) only [st_out env hx]
  · simp only [ipSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [ld _ (by decide) (by decide)] <;> rfl
  · rw [show G + 0x18 = G + BitVec.ofNat 32 0x18 from rfl, ld _ (by decide) (by decide)]; exact ha1
  · rw [show G + 0x18 + 4 = G + BitVec.ofNat 32 0x1C by rw [BitVec.add_assoc]; rfl,
      ld _ (by decide) (by decide)]; exact ha2
  · rw [← hg1]; simp +decide only [runBlock, BInstr.run, ipProBlock, upd, hsp, aluEval, BitVec.add_assoc,
      BitVec.reduceAdd, ↓reduceIte, BitVec.add_zero]
  · rw [← hg1]; simp +decide only [runBlock, BInstr.run, ipProBlock, upd, ↓reduceIte]
    show (0 : Word) + _ = _; exact (BitVec.zero_add _).trans ha0
  · rw [← hg1]; simp +decide only [runBlock, BInstr.run, ipProBlock, upd, ↓reduceIte]
    show (0 : Word) + _ = _; exact (BitVec.zero_add _).trans ha3
  · exact rk r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide))
      (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide))
  · rw [← hg1]; simp only [runBlock, BInstr.run, ipProBlock, upd_zero]
  · rw [show G + 0x18 + 8 = G + BitVec.ofNat 32 0x20 by rw [BitVec.add_assoc]; rfl,
      ld _ (by decide) (by decide)]; rfl
  · rw [← hg1]; simp +decide only [runBlock, BInstr.run, ipProBlock, upd, hsp, aluEval, BitVec.add_assoc,
      BitVec.reduceAdd, ↓reduceIte, BitVec.add_zero]
  · rw [← hg1]; simp +decide only [runBlock, BInstr.run, ipProBlock, upd, ↓reduceIte]

/-- **`image::parse`'s header.** From entry, `image::parse` returns the error
`hdrW` gives, or reaches offset 0x15A past the header. -/
theorem ip_header (m : Machine) (env : IEnv P R G ptr len out) (code : ICode m.mem P)
    (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ptr) (ha2 : reg m a2 = len)
    (ha3 : reg m a3 = ilen) (hsp : reg m sp = G + 0x160) :
    HPost P R G ptr len out ilen m.mem (reg m) m (hdrW m.mem ptr len ilen) := by
  obtain ⟨m1, M1, g1, c1, u1, inv1, hpos, h1a0, h1a1⟩ :=
    ip_prologue (ilen := ilen) m env code hpc ha0 ha1 ha2 ha3 hsp
  obtain ⟨m2, c2, u2, sp2, a02, fr2, mem2⟩ := ip_magic env u1 (inv1.code env code) ip_at_48 ip_at_4c
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x50 (by decide)) inv1.sp
    h1a0 h1a1 inv1.rdp inv1.rdl
  obtain ⟨invM, adv⟩ := IInv.adv env inv1 hpos (My := m2.mem) (n := 4) (c := 0) (N := 48) (by omega)
    fun x hx => by rw [mem2 x (by rwa [add_ofNat_zero] at hx), magicMem_pos]
  have inv2 : IInv R G ptr len out ilen m.mem (reg m) m2.mem (reg m2) := invM.regsT fr2
  rw [magicR env inv1 hpos] at a02
  obtain ⟨m3, g3, c3, k3, br⟩ := check_br u2 (inv2.code env code).parse ip_at_50 ip_at_54 ip_at_58
    (T := 0xB6) (by decide)
  have inv3 : IInv R G ptr len out ilen m.mem (reg m) m2.mem g3 :=
    inv2.regs fun r _ h1 _ _ _ _ _ => k3 r h1
  have g3a : g3 a0 = reg m2 a0 := k3 a0 (by decide)
  have pre : Steps m m2 := c1.trans c2
  unfold hdrW rdMagic rdB
  revert a02
  rcases hb : bytesResult ptr len 0 4 with _ | ⟨p, e⟩ <;> intro a02 <;> dsimp only at a02
  · rcases br with ⟨h, -⟩ | ⟨-, u3⟩
    · rw [a02] at h; exact absurd h (by decide)
    · exact IErrDone.pre (pre.trans c3) (ip_errB6 env code inv3 u3 (by rw [g3a, a02]; rfl))
  · show HPost P R G ptr len out ilen m.mem (reg m) m (Except.bind
      (if (memLoad32 m.mem p == 0x4D493343) = true then .ok e else .error 2)
      fun pos => Except.bind (rdVer1 m.mem ptr len pos) fun pos => hdrChip m.mem ptr len ilen pos)
    by_cases hk : (memLoad32 m.mem p == 0x4D493343) = true
    · rw [ite_eq_left hk]
      rw [ite_eq_left hk] at a02
      rcases br with ⟨-, u3⟩ | ⟨h, -⟩
      · exact HPost.pre (pre.trans c3) _ (ip_hdrVer env code inv3 u3 (adv p e hb))
      · rw [a02] at h; exact absurd rfl h
    · rw [ite_eq_right hk]
      rw [ite_eq_right hk] at a02
      rcases br with ⟨h, -⟩ | ⟨-, u3⟩
      · rw [a02] at h; exact absurd h (by decide)
      · exact IErrDone.pre (pre.trans c3) (ip_errB6 env code inv3 u3 (by rw [g3a, a02]; rfl))

end Hdr

end C3.RV32
