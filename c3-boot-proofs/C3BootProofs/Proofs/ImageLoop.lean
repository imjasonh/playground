import C3BootProofs.Proofs.ImageSegs

/-!
# `image::parse`: one pass of the segment loop

`lp_read` runs `read_segment` from offset 0x198 and `lp_check` the checks
from offset 0x2CA; `lp_iter` puts them together into one pass from 0x188
back to 0x188.
-/

namespace C3.RV32

open C3.ImageV0

set_option maxRecDepth 20000

theorem posMem_fr (M : Word → BitVec 8) (self n x : Word) (h : Sep (self + 8) 4 x 1) :
    posMem M self n x = M x := by
  unfold posMem
  rcases bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) n with _ | ⟨_, e⟩
  · rfl
  · exact memStore32_get_sep h

theorem u32Mem_fr (M : Word → BitVec 8) (o self x : Word) (h1 : Sep (self + 8) 4 x 1) (h2 : Sep o 8 x 1) :
    u32Mem M o self x = M x := by
  have n0 : x ≠ o := fun e => h2 0 (by omega) 0 (by omega) (by rw [add_ofNat_zero, add_ofNat_zero, e])
  have n1 : x ≠ o + 1 := fun e => h2 1 (by omega) 0 (by omega) (by rw [add_ofNat_zero, e]; rfl)
  have s4 : Sep (o + 4) 4 x 1 := fun i hi j hj e => h2 (4 + i) (by omega) j hj (by
    rw [← e, ← add_ofNat_assoc]; rfl)
  unfold u32Mem
  rcases bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 with _ | ⟨p, e⟩
  · dsimp only; rw [memStore8_ne n0, memStore8_ne n1]
  · dsimp only; rw [memStore8_ne n0, memStore32_get_sep s4, memStore32_get_sep h1]

theorem lo8_and (w : Word) : (w &&& 0xFF).extractLsb' 0 8 = w.extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hff : ∀ i, i < 8 → (0xFF : Word).getLsbD (0 + i) = true := by decide
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hff i hi, Bool.and_true]

theorem or_ff_and (v : Word) : (v ||| 0xFF) &&& 0xFF = 0xFF := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  rw [BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases v.getLsbD i <;> cases (0xFF : Word).getLsbD i <;> rfl

/-- `My` and `Mx` agree on the frame's entry point, segment count, and mask
words and on the segment array. -/
def ByteFr (My Mx : Word → BitVec 8) (G : Word) : Prop :=
  ∀ k, (8 ≤ k ∧ k < 0x10) ∨ (0x14 ≤ k ∧ k < 0x18) ∨ (0x24 ≤ k ∧ k < 0x124) →
    My (G + BitVec.ofNat 32 k) = Mx (G + BitVec.ofNat 32 k)

theorem ByteFr.refl (M : Word → BitVec 8) (G : Word) : ByteFr M M G := fun _ _ => rfl

theorem ByteFr.trans {M'' M' M : Word → BitVec 8} {G : Word} (h1 : ByteFr M'' M' G) (h2 : ByteFr M' M G) :
    ByteFr M'' M G := fun k hk => (h1 k hk).trans (h2 k hk)

theorem ByteFr.word {My Mx : Word → BitVec 8} {G : Word} (h : ByteFr My Mx G) (c : Nat)
    (hc : (8 ≤ c ∧ c + 4 ≤ 0x10) ∨ (0x14 ≤ c ∧ c + 4 ≤ 0x18) ∨ (0x24 ≤ c ∧ c + 4 ≤ 0x124)) :
    memLoad32 My (G + BitVec.ofNat 32 c) = memLoad32 Mx (G + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h _ (Or.inl ⟨by omega, by omega⟩)
    · exact h _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
    · exact h _ (Or.inr (Or.inr ⟨by omega, by omega⟩))

theorem ByteFr.arr {My Mx : Word → BitVec 8} {G : Word} (h : ByteFr My Mx G) : ArrAgree My Mx G :=
  fun k hk => h _ (Or.inr (Or.inr ⟨by omega, by omega⟩))

/-- A word stored in the frame's scratch words at 0, 4, or 0x10. -/
theorem ByteFr.st32 (M : Word → BitVec 8) (G : Word) (c : Nat) (v : Word)
    (hc : c + 4 ≤ 8 ∨ (0x10 ≤ c ∧ c + 4 ≤ 0x14)) : ByteFr (memStore32 M (G + BitVec.ofNat 32 c) v) M G :=
  fun k hk => memStore32_get_sep (sep_offsets G (by omega) (by omega) (by omega))

/-- What a call from the loop keeps: the frame below the reader's position,
and the segment array. -/
def CallFr (My Mx : Word → BitVec 8) (G : Word) : Prop :=
  ∀ k, k < 0x20 ∨ (0x24 ≤ k ∧ k < 0x124) → My (G + BitVec.ofNat 32 k) = Mx (G + BitVec.ofNat 32 k)

theorem CallFr.byteFr {My Mx : Word → BitVec 8} {G : Word} (h : CallFr My Mx G) : ByteFr My Mx G :=
  fun k hk => by
    rcases hk with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, h2⟩
    · exact h k (Or.inl (by omega))
    · exact h k (Or.inl (by omega))
    · exact h k (Or.inr ⟨h1, h2⟩)

theorem CallFr.word {My Mx : Word → BitVec 8} {G : Word} (h : CallFr My Mx G) (c : Nat)
    (hc : c + 4 ≤ 0x20 ∨ (0x24 ≤ c ∧ c + 4 ≤ 0x124)) :
    memLoad32 My (G + BitVec.ofNat 32 c) = memLoad32 Mx (G + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]
    rcases hc with h1 | ⟨h1, h2⟩
    · exact h _ (Or.inl (by omega))
    · exact h _ (Or.inr ⟨by omega, by omega⟩)

section Loop

variable {P R G ptr len out ilen : Word} {M0 Mx : Word → BitVec 8} {f0 g : Fin 32 → Word}

/-- A frame byte a call keeps is outside the callees' stacks, the reader's
position, and the result slot at `G + 0x124`. -/
theorem fr_sep (env : IEnv P R G ptr len out) {k : Nat} (hk : k < 0x20 ∨ (0x24 ≤ k ∧ k < 0x124)) :
    Sep R 48 (G + BitVec.ofNat 32 k) 1 ∧ Sep (R + BitVec.ofNat 32 32) 16 (G + BitVec.ofNat 32 k) 1 ∧
      Sep (G + 0x18 + 8) 4 (G + BitVec.ofNat 32 k) 1 ∧ Sep (G + BitVec.ofNat 32 0x124) 8 (G + BitVec.ofNat 32 k) 1 := by
  have eP : G + 0x18 + 8 = G + BitVec.ofNat 32 0x20 := by rw [BitVec.add_assoc]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [env.g_ofs]
    have := env.stack_stack 0 48 (0x30 + k) 1 (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  · rw [env.g_ofs]; exact env.stack_stack 32 16 (0x30 + k) 1 (by omega) (by omega) (by omega)
  · rw [eP]; exact sep_offsets G (by omega) (by omega) (by omega)
  · exact sep_offsets G (by omega) (by omega) (by omega)

/-- Offset 0x212: `read_segment` failed, with the error in the low byte of `a1`. -/
theorem lp_e212 (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0x212 g)
    {e : BitVec 8} (he : (g a1).extractLsb' 0 8 = e) : IErrDone R G out M0 f0 e m := by
  have hc := (inv.code env code0).parse
  have hz := inv.zero
  obtain ⟨m1, d1, u1⟩ := s.aluImm hc ip_at_212 (off' := 0x216) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.aluImm hc ip_at_216 (off' := 0x21A) (by decide)
  obtain ⟨m3, d3, u3⟩ := u2.aluImm hc ip_at_21a (off' := 0x21E) (by decide)
  obtain ⟨m4, d4, u4⟩ := u3.aluImm hc ip_at_21e (off' := 0x222) (by decide)
  have v3 : ∀ (f : Fin 32 → Word) (v : Word), aluEval .and (aluEval .or v 0xFF) 0xFF = 0xFF :=
    fun _ v => or_ff_and v
  obtain ⟨m5, d5, u5⟩ := u4.taken hc 0x2FC ip_at_222 (by decide) (by
    simp +decide only [upd, ↓reduceIte]; rw [v3 g]; rfl)
  obtain ⟨m6, d6, u6⟩ := u5.alu hc ip_at_2fc (off' := 0x2FE) (by decide)
  obtain ⟨m7, d7, u7⟩ := u6.jump hc ip_at_2fe (off' := 0x418) (by decide)
    (by rw [u6.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0x418 (by decide)))
  refine IErrDone.pre (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.single d7)))))))
    (ip_err418 env code0 (inv.frameR (fun r hr => ?_) ?_ ?_ ?_ rfl) u7 ?_)
  · have n : ∀ q : Fin 32, q ∈ ipClob → r ≠ q := fun q hq e => hr (e ▸ hq)
    rw [updz (by simp) (n (16 : Fin 32) (by decide)), updz (by simp) (n a0 (by decide)),
      updz (by simp) (n a2 (by decide)), updz (by simp) (n s10 (by decide)), updz hz (n s7 (by decide))]
  · simp +decide only [upd, ↓reduceIte]; exact inv.sp
  · simp +decide only [upd, ↓reduceIte]; exact inv.s0
  · simp +decide only [upd, ↓reduceIte]; exact inv.s1
  · simp +decide only [upd, ↓reduceIte]
    rw [show aluEval .add 0 (aluEval .and (g a1) 0xFF) = g a1 &&& 0xFF from BitVec.zero_add _, lo8_and, he]

/-- A call to `Reader::u32` from the loop, with its result at `G + 0x124`,
through the load of its tag byte. -/
theorem lp_rd32 (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} {off : Nat} (s : St Mx P m off g)
    {pos o : Word} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos)
    (i1 : fetchRel imageParseCode off = some (.aluImm .add a0 sp 0x124, 2))
    (i2 : fetchRel imageParseCode (off + 2) = some (.aluImm .add a1 sp 0x18, 2))
    (i3 : fetchRel imageParseCode (off + 4) = some (.auipc ra 0, 4))
    (i4 : fetchRel imageParseCode (off + 4 + 4) = some (.jalr ra ra o, 4))
    (i5 : fetchRel imageParseCode (off + 4 + 8) = some (.load .lbu a0 sp 0x124, 4))
    (hb : P + BitVec.ofNat 32 (off + 4) + 0 + o = P + 0x420) (hoff : off % 2 = 0) :
    ∃ m' My g', Steps m m' ∧ St My P m' (off + 4 + 8 + 4) g' ∧ IInv R G ptr len out ilen M0 f0 My g' ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → g' r = g r) ∧
      CallFr My Mx G ∧
      match bytesResult ptr len pos 4 with
      | none => g' a0 = 1 ∧ My (G + 0x125) = 0
      | some (p, e) => g' a0 = 0 ∧ memLoad32 My (G + 0x128) = memLoad32 M0 p ∧
          memLoad32 My (G + 0x18 + 8) = e := by
  have hc := (inv.code env code0).parse
  have hz := inv.zero
  obtain ⟨m1, d1, u1⟩ := s.aluImm hc i1 (off' := off + 2) (ofNat_add_ofNat off 2)
  obtain ⟨m2, d2, u2⟩ := u1.aluImm hc i2 (off' := off + 4) (ofNat_add_ofNat (off + 2) 2)
  have v1 : upd g a0 (aluEval .add (g sp) 0x124) sp = G := by rw [updz hz (by decide), inv.sp]
  rw [v1] at u2
  have f2o : ∀ r, r ≠ a0 → r ≠ a1 →
      upd (upd g a0 (aluEval .add (g sp) 0x124)) a1 (aluEval .add G 0x18) r = g r := fun r h0 h1 => by
    rw [updz (by simp) h1, updz hz h0]
  obtain ⟨m3, c3, u3, sp3, fr3, mem3⟩ := ip_u32 env 0x124 (by omega) (by omega) (by omega) u2
    (inv.code env code0) i3 i4 hb (even_at P env.hP (off + 4 + 8) (by omega))
    (by rw [f2o sp (by decide) (by decide), inv.sp])
    (by rw [updz (by simp) (by decide), upd_a0]; show g sp + _ = _; rw [inv.sp]; rfl)
    (by simp +decide [upd]; rfl) inv.rdp inv.rdl
  obtain ⟨invM, res⟩ := IInv.u32 env inv hpos (c := 0x124) (by omega) (by omega) mem3
  have inv3 : IInv R G ptr len out ilen M0 f0 m3.mem (reg m3) :=
    invM.regs fun r h0 h1 h2 h3 h4 h5 h7 => by rw [fr3 r h0 h1 h2 h3 h4 h5 h7, f2o r h0 h1]
  obtain ⟨m4, d4, u4⟩ := u3.lbu (inv3.code env code0).parse i5 (off' := off + 4 + 8 + 4)
    (ofNat_add_ofNat _ 4)
  rw [sp3] at u4
  have cf : CallFr m3.mem Mx G := fun k hk => by
    obtain ⟨h1, -, h3, h4⟩ := fr_sep env hk
    rw [mem3 _ h1, u32Mem_fr _ _ _ _ h3 h4]
  refine ⟨m4, _, _, (Steps.cons d1 (.cons d2 c3)).trans (.single d4), u4,
    inv3.setReg (by decide) (by decide) (by decide) (by decide),
    fun r h0 h1 h2 h3 h4 h5 h7 => by rw [updz (by rw [← u3.regs]; rfl) h0, fr3 r h0 h1 h2 h3 h4 h5 h7,
      f2o r h0 h1], cf, ?_⟩
  revert res
  rcases bytesResult ptr len pos 4 with _ | ⟨p, e⟩
  · rintro ⟨r1, r2⟩
    refine ⟨?_, ?_⟩
    · rw [upd_a0, show m3.mem (G + 0x124) = 1 from r1]; rfl
    · rwa [show G + BitVec.ofNat 32 0x124 + 1 = G + 0x125 by rw [BitVec.add_assoc]; rfl] at r2
  · rintro ⟨r1, r2, r3⟩
    refine ⟨?_, ?_, r3⟩
    · rw [upd_a0, show m3.mem (G + 0x124) = 0 from r1]; rfl
    · rwa [show G + BitVec.ofNat 32 0x124 + 4 = G + 0x128 by rw [BitVec.add_assoc]; rfl] at r2

/-- Offset 0x20E: `Reader::u32` failed, with the error byte at `G + 0x125`. -/
theorem lp_e20e (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0x20E g)
    {e : BitVec 8} (h : Mx (G + 0x125) = e) : IErrDone R G out M0 f0 e m := by
  have hc := (inv.code env code0).parse
  obtain ⟨m1, d1, u1⟩ := s.lbu hc ip_at_20e (off' := 0x212) (by decide)
  have inv1 := inv.setReg (rd := a1) (v := (Mx (g sp + 0x125)).zeroExtend 32)
    (by decide) (by decide) (by decide) (by decide)
  refine IErrDone.pre (.single d1) (lp_e212 env code0 inv1 u1 ?_)
  rw [upd_same (by decide), inv.sp, h, zext_lsb8]

end Loop

/-- At offset 0x2CA after `read_segment` read `s`: what the checks need,
against the memory `Ms` and registers `gs` at the start of the pass. -/
def RdSt (R G ptr len out ilen : Word) (M0 : Word → BitVec 8) (f0 : Fin 32 → Word)
    (Ms : Word → BitVec 8) (gs : Fin 32 → Word) (s : SegW) (pos : Word)
    (My : Word → BitVec 8) (g : Fin 32 → Word) : Prop :=
  IInv R G ptr len out ilen M0 f0 My g ∧ memLoad32 My (G + 0x18 + 8) = pos ∧ ByteFr My Ms G ∧
    memLoad32 My (G + 4) = s.off ∧ memLoad32 My (G + 0x128) = s.len ∧
    g s7 = s.addr ∧ g s6 = s.kind.zeroExtend 32 ∧
    ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ s6 → r ≠ s7 → g r = gs r

def RdPost (P R G ptr len out ilen : Word) (M0 : Word → BitVec 8) (f0 : Fin 32 → Word)
    (Ms : Word → BitVec 8) (gs : Fin 32 → Word) (m : Machine) :
    Except (BitVec 8) (SegW × Word) → Prop
  | .error e => IErrDone R G out M0 f0 e m
  | .ok (s, pos) => ∃ m' My g, Steps m m' ∧ St My P m' 0x2CA g ∧
      RdSt R G ptr len out ilen M0 f0 Ms gs s pos My g

section Loop

variable {P R G ptr len out ilen : Word} {M0 Mx Ms : Word → BitVec 8} {f0 g gs : Fin 32 → Word}

theorem RdPost.pre {m m' : Machine} (c : Steps m m') :
    ∀ r, RdPost P R G ptr len out ilen M0 f0 Ms gs m' r → RdPost P R G ptr len out ilen M0 f0 Ms gs m r
  | .error _, h => IErrDone.pre c h
  | .ok _, ⟨n, My, g, c', rest⟩ => ⟨n, My, g, c.trans c', rest⟩

/-- From offset 0x1FC: the segment's length. -/
theorem lp_rdL (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0x1FC g)
    {pos a o : Word} {k : BitVec 8} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos) (hfr : ByteFr Mx Ms G)
    (ho : memLoad32 Mx (G + 4) = o) (h7 : g s7 = a) (h6 : g s6 = k.zeroExtend 32)
    (hk : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ s6 → r ≠ s7 →
      g r = gs r) :
    RdPost P R G ptr len out ilen M0 f0 Ms gs m (segL M0 ptr len pos k a o) := by
  obtain ⟨m1, My, g1, c1, u1, inv1, fr1, cf, res⟩ := lp_rd32 env code0 inv s hpos ip_at_1fc ip_at_1fe
    ip_at_200 ip_at_204 ip_at_208 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
  have hc := (inv1.code env code0).parse
  unfold segL rdU32 rdB
  revert res
  rcases bytesResult ptr len pos 4 with _ | ⟨p, e⟩
  · rintro ⟨r1, r2⟩
    obtain ⟨m2, d2, u2⟩ := u1.notTaken hc 0x20E ip_at_20c (by decide) (by rw [r1, inv1.zero]; decide)
    exact IErrDone.pre (c1.trans (.single d2)) (lp_e20e env code0 inv1 u2 r2)
  · rintro ⟨r1, r2, r3⟩
    obtain ⟨m2, d2, u2⟩ := u1.taken hc 0x2CA ip_at_20c (by decide) (by rw [r1, inv1.zero]; decide)
    refine ⟨m2, My, g1, c1.trans (.single d2), u2, inv1, r3, cf.byteFr.trans hfr, ?_, r2, ?_, ?_, ?_⟩
    · rw [show G + 4 = G + BitVec.ofNat 32 4 from rfl, cf.word 4 (Or.inl (by omega))]; exact ho
    · rw [fr1 s7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h7]
    · rw [fr1 s6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h6]
    · intro r h0 h1 h2 h3 h4 h5 h7' h6' h7''
      rw [fr1 r h0 h1 h2 h3 h4 h5 h7', hk r h0 h1 h2 h3 h4 h5 h7' h6' h7'']

/-- From offset 0x1E4: the segment's offset, kept at `G + 4`. -/
theorem lp_rdO (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0x1E4 g)
    {pos a : Word} {k : BitVec 8} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos) (hfr : ByteFr Mx Ms G)
    (h7 : g s7 = a) (h6 : g s6 = k.zeroExtend 32)
    (hk : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ s6 → r ≠ s7 →
      g r = gs r) :
    RdPost P R G ptr len out ilen M0 f0 Ms gs m (segO M0 ptr len pos k a) := by
  obtain ⟨m1, My, g1, c1, u1, inv1, fr1, cf, res⟩ := lp_rd32 env code0 inv s hpos ip_at_1e4 ip_at_1e6
    ip_at_1e8 ip_at_1ec ip_at_1f0 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
  have hc := (inv1.code env code0).parse
  have k1 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → g1 r = g r := fr1
  unfold segO rdU32 rdB
  revert res
  rcases hb : bytesResult ptr len pos 4 with _ | ⟨p, e⟩
  · rintro ⟨r1, r2⟩
    obtain ⟨m2, d2, u2⟩ := u1.taken hc 0x20E ip_at_1f4 (by decide) (by rw [r1, inv1.zero]; decide)
    exact IErrDone.pre (c1.trans (.single d2)) (lp_e20e env code0 inv1 u2 r2)
  · rintro ⟨r1, r2, r3⟩
    obtain ⟨m2, d2, u2⟩ := u1.notTaken hc 0x1F6 ip_at_1f4 (by decide) (by rw [r1, inv1.zero]; decide)
    obtain ⟨m3, d3, u3⟩ := u2.lw hc ip_at_1f6 (off' := 0x1FA) (by decide)
      (by rw [inv1.sp]; exact aligned_add env.hG (k := 0x128) (by decide))
    rw [inv1.sp, r2] at u3
    obtain ⟨m4, d4, u4⟩ := u3.sw hc ip_at_1fa (off' := 0x1FC) (by decide)
      (by rw [updz inv1.zero (by decide), inv1.sp]; exact aligned_add env.hG (k := 4) (by decide))
    rw [updz inv1.zero (by decide), inv1.sp, upd_a0] at u4
    have inv4 := (inv1.setReg (rd := a0) (v := memLoad32 M0 p) (by decide) (by decide) (by decide)
      (by decide)).st32 env 4 (memLoad32 M0 p) (Or.inl (by omega))
    show RdPost P R G ptr len out ilen M0 f0 Ms gs m (segL M0 ptr len e k a (memLoad32 M0 p))
    have z1 := inv1.zero
    exact RdPost.pre (c1.trans (.cons d2 (.cons d3 (.single d4)))) _ (lp_rdL env code0 inv4 u4
      (by rw [show G + 0x18 + 8 = G + BitVec.ofNat 32 0x20 by rw [BitVec.add_assoc]; rfl,
          memLoad32_store32_sep (show Sep (G + BitVec.ofNat 32 4) 4 (G + BitVec.ofNat 32 0x20) 4 from
            sep_offsets G (c := 4) (n := 4) (d := 0x20) (k := 4) (by omega) (by omega) (by omega)),
          show G + BitVec.ofNat 32 0x20 = G + 0x18 + 8 by rw [BitVec.add_assoc]; rfl, r3])
      ((ByteFr.st32 My G 4 _ (Or.inl (by omega))).trans (cf.byteFr.trans hfr))
      (memLoad32_store32_same _ _ _)
      (by rw [updz z1 (by decide), k1 s7 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h7])
      (by rw [updz z1 (by decide), k1 s6 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h6])
      (fun r h0 h1 h2 h3 h4 h5 h7' h6' h7'' => by
        rw [updz z1 h0, k1 r h0 h1 h2 h3 h4 h5 h7', hk r h0 h1 h2 h3 h4 h5 h7' h6' h7'']))

/-- From offset 0x1CE: the segment's address, kept in `s7`. -/
theorem lp_rdA (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0x1CE g)
    {pos : Word} {k : BitVec 8} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos) (hfr : ByteFr Mx Ms G)
    (h6 : g s6 = k.zeroExtend 32)
    (hk : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ s6 → r ≠ s7 →
      g r = gs r) :
    RdPost P R G ptr len out ilen M0 f0 Ms gs m (segA M0 ptr len pos k) := by
  obtain ⟨m1, My, g1, c1, u1, inv1, fr1, cf, res⟩ := lp_rd32 env code0 inv s hpos ip_at_1ce ip_at_1d0
    ip_at_1d2 ip_at_1d6 ip_at_1da (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
  have hc := (inv1.code env code0).parse
  have k1 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → g1 r = g r := fr1
  unfold segA rdU32 rdB
  revert res
  rcases hb : bytesResult ptr len pos 4 with _ | ⟨p, e⟩
  · rintro ⟨r1, r2⟩
    obtain ⟨m2, d2, u2⟩ := u1.taken hc 0x20E ip_at_1de (by decide) (by rw [r1, inv1.zero]; decide)
    exact IErrDone.pre (c1.trans (.single d2)) (lp_e20e env code0 inv1 u2 r2)
  · rintro ⟨r1, r2, r3⟩
    obtain ⟨m2, d2, u2⟩ := u1.notTaken hc 0x1E0 ip_at_1de (by decide) (by rw [r1, inv1.zero]; decide)
    obtain ⟨m3, d3, u3⟩ := u2.lw hc ip_at_1e0 (off' := 0x1E4) (by decide)
      (by rw [inv1.sp]; exact aligned_add env.hG (k := 0x128) (by decide))
    rw [inv1.sp, r2] at u3
    have inv3 := inv1.setReg (rd := s7) (v := memLoad32 M0 p) (by decide) (by decide) (by decide)
      (by decide)
    show RdPost P R G ptr len out ilen M0 f0 Ms gs m (segO M0 ptr len e k (memLoad32 M0 p))
    have z1 := inv1.zero
    exact RdPost.pre (c1.trans (.cons d2 (.single d3))) _ (lp_rdO env code0 inv3 u3 r3
      (cf.byteFr.trans hfr) (upd_same (by decide))
      (by rw [updz z1 (by decide), k1 s6 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h6])
      (fun r h0 h1 h2 h3 h4 h5 h7' h6' h7'' => by
        rw [updz z1 h7'', k1 r h0 h1 h2 h3 h4 h5 h7', hk r h0 h1 h2 h3 h4 h5 h7' h6' h7'']))

theorem IInv.setR (inv : IInv R G ptr len out ilen M0 f0 Mx g) (rd : Fin 32) {v : Word}
    (h : rd ∈ ipClob ∧ rd ≠ RV32.sp ∧ rd ≠ RV32.s0 ∧ rd ≠ RV32.s1 := by decide) :
    IInv R G ptr len out ilen M0 f0 Mx (upd g rd v) :=
  inv.setReg h.1 h.2.1 h.2.2.1 h.2.2.2

theorem kind_dec (b : BitVec 8) :
    aluEval .and (aluEval .add (b.zeroExtend 32) 0xFFFFFFFF) 0xFF = (b - 1).zeroExtend 32 := by
  revert b; decide

theorem kind_chk (k : BitVec 8) :
    branchTaken .bgeu (aluEval .add 0 3) (k.zeroExtend 32) = !((3 : BitVec 8).ult k) := by
  revert k; decide

/-- A call from the loop that only moves the reader keeps `CallFr`. -/
theorem callFr_pos (env : IEnv P R G ptr len out) {My : Word → BitVec 8} {n : Word}
    (h : ∀ x, Sep (R + BitVec.ofNat 32 32) 16 x 1 → My x = posMem Mx (G + 0x18) n x) : CallFr My Mx G :=
  fun k hk => by
    obtain ⟨-, h2, h3, -⟩ := fr_sep env hk
    rw [h _ h2, posMem_fr _ _ _ _ h3]

/-- **`read_segment`**, from offset 0x198. -/
theorem lp_read (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0x198 g)
    {pos : Word} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos) :
    RdPost P R G ptr len out ilen M0 f0 Mx g m (readSegW M0 ptr len pos) := by
  have hc := (inv.code env code0).parse
  have hz := inv.zero
  obtain ⟨m1, d1, u1⟩ := s.aluImm hc ip_at_198 (off' := 0x19A) (by decide)
  obtain ⟨m2, c2, u2, sp2, a02, a12, fr2, mem2⟩ := ip_u8 env u1 (inv.code env code0) ip_at_19a
    ip_at_19e (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x1A2 (by decide))
    (by rw [updz hz (by decide), inv.sp]) (by rw [upd_a0]; show g sp + _ = _; rw [inv.sp])
    inv.rdp inv.rdl
  obtain ⟨invM, adv⟩ := IInv.adv env inv hpos (My := m2.mem) (n := 1) (c := 32) (N := 16) (by omega)
    fun x hx => by rw [mem2 x hx, reservedMem_pos]
  have cf2 : CallFr m2.mem Mx G := callFr_pos env fun x hx => by rw [mem2 x hx, reservedMem_pos]
  have k2 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m2 r = g r :=
    fun r h0 h1 h2 h3 h4 h5 h7 => by rw [fr2 r h0 h1 h2 h3 h4 h5 h7, updz hz h0]
  have inv2 : IInv R G ptr len out ilen M0 f0 m2.mem (reg m2) := invM.regs k2
  have hc2 := (inv2.code env code0).parse
  have z2 := inv2.zero
  rw [u8R env inv hpos] at a02 a12
  obtain ⟨m3, d3, u3⟩ := u2.aluImm hc2 ip_at_1a2 (off' := 0x1A4) (by decide)
  have inv3 : IInv R G ptr len out ilen M0 f0 m2.mem (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1)) :=
    inv2.setReg (by decide) (by decide) (by decide) (by decide)
  have pre : Steps m m3 := .cons d1 (c2.trans (.single d3))
  unfold readSegW rdU8 rdB
  revert a02 a12
  rcases hb : bytesResult ptr len pos 1 with _ | ⟨p, e⟩ <;> intro a02 a12 <;> dsimp only at a02 a12
  · obtain ⟨m4, d4, u4⟩ := u3.taken hc2 0x212 ip_at_1a4 (by decide)
      (by rw [upd_a0, a02, upd_zero]; decide)
    exact IErrDone.pre (pre.trans (.single d4)) (lp_e212 env code0 inv3 u4
      (by rw [updz z2 (by decide), a12]; rfl))
  · obtain ⟨m4, d4, u4⟩ := u3.notTaken hc2 0x1A6 ip_at_1a4 (by decide)
      (by rw [upd_a0, a02, upd_zero]; decide)
    obtain ⟨m5, d5, u5⟩ := u4.aluImm hc2 ip_at_1a6 (off' := 0x1A8) (by decide)
    obtain ⟨m6, d6, u6⟩ := u5.aluImm hc2 ip_at_1a8 (off' := 0x1AC) (by decide)
    rw [show aluEval .and (upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1)) a1
        (aluEval .add (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1) a1) 0xFFFFFFFF) a1) 0xFF =
        (M0 p - 1).zeroExtend 32 by
      rw [upd_same (by decide), updz z2 (by decide), a12, kind_dec]] at u6
    obtain ⟨m7, d7, u7⟩ := u6.aluImm hc2 ip_at_1ac (off' := 0x1AE) (by decide)
    show RdPost P R G ptr len out ilen M0 f0 Mx g m
      (if (3 : BitVec 8).ult (M0 p - 1) = true then .error 9
       else Except.bind (rdRes M0 ptr len 3 e) fun pos => segA M0 ptr len pos (M0 p - 1))
    have br : ∀ v w : Word, branchTaken .bgeu
        (upd (upd (upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1)) a1 v) s6 ((M0 p - 1).zeroExtend 32))
          a0 (aluEval .add (upd (upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1)) a1 v) s6
            ((M0 p - 1).zeroExtend 32) x0) 3) a0)
        (upd (upd (upd (upd (reg m2) a0 (aluEval .and (reg m2 a0) 1)) a1 v) s6 ((M0 p - 1).zeroExtend 32))
          a0 w s6) = !((3 : BitVec 8).ult (M0 p - 1)) := fun v w => by
      rw [upd_a0, updz (by simp) (show (s6 : Fin 32) ≠ a0 by decide), upd_same (by decide),
        show ∀ (f : Fin 32 → Word) v, upd f s6 v x0 = 0 from fun _ _ => rfl, kind_chk]
    by_cases hk : (3 : BitVec 8).ult (M0 p - 1) = true
    · rw [ite_eq_left hk]
      obtain ⟨m8, d8, u8⟩ := u7.notTaken hc2 0x1B2 ip_at_1ae (by decide)
        (by rw [br, hk]; rfl)
      obtain ⟨m9, d9, u9⟩ := u8.aluImm hc2 ip_at_1b2 (off' := 0x1B4) (by decide)
      obtain ⟨m10, d10, u10⟩ := u9.jump hc2 ip_at_1b4 (off' := 0x212) (by decide)
        (by rw [u9.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0x212 (by decide)))
      exact IErrDone.pre (pre.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
        (.single d10))))))))
        (lp_e212 env code0 (((((inv2.setR a0).setR a1).setR s6).setR a0).setR a1) u10
          (by rw [upd_same (by decide)]; simp [upd, aluEval]))
    · rw [ite_eq_right hk]
      obtain ⟨m8, d8, u8⟩ := u7.taken hc2 0x1B6 ip_at_1ae (by decide)
        (by rw [br, Bool.eq_false_iff.mpr hk]; rfl)
      obtain ⟨m9, d9, u9⟩ := u8.aluImm hc2 ip_at_1b6 (off' := 0x1B8) (by decide)
      obtain ⟨m10, d10, u10⟩ := u9.aluImm hc2 ip_at_1b8 (off' := 0x1BA) (by decide)
      have inv10 : IInv R G ptr len out ilen M0 f0 m2.mem (reg m10) := inv2.frameR
        (fun r hr => by
          have n : ∀ q : Fin 32, q ∈ ipClob → r ≠ q := fun q hq e => hr (e ▸ hq)
          rw [u10.regs, updz (by simp) (n a1 (by decide)), updz (by simp) (n a0 (by decide)),
            updz (by simp) (n a0 (by decide)), updz (by simp) (n s6 (by decide)),
            updz (by simp) (n a1 (by decide)), updz z2 (n a0 (by decide))])
        (by rw [u10.regs]; simp +decide only [upd, ↓reduceIte]; exact sp2)
        (by rw [u10.regs]; simp +decide only [upd, ↓reduceIte]; exact inv2.s0)
        (by rw [u10.regs]; simp +decide only [upd, ↓reduceIte]; exact inv2.s1)
        (by rw [u10.regs]; rfl)
      obtain ⟨m11, c11, u11, sp11, a011, fr11, mem11⟩ := ip_reserved env u10.self (inv10.code env code0)
        (n := 3) ip_at_1ba ip_at_1be (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
        (even_at P env.hP 0x1C2 (by decide)) inv10.sp
        (by rw [u10.regs]; simp +decide only [upd, ↓reduceIte]; show reg m2 sp + _ = _; rw [sp2])
        (by rw [u10.regs]; simp +decide only [upd, ↓reduceIte]) (by decide) inv10.rdp inv10.rdl
      have hpos2 := adv p e hb
      obtain ⟨invM', adv'⟩ := IInv.adv env inv10 hpos2 (My := m11.mem) (n := 3) (c := 32) (N := 16)
        (by omega) fun x hx => by rw [mem11 x hx, reservedMem_pos]
      have cf11 : CallFr m11.mem m2.mem G := callFr_pos env fun x hx => by rw [mem11 x hx, reservedMem_pos]
      have inv11 : IInv R G ptr len out ilen M0 f0 m11.mem (reg m11) := invM'.regs fr11
      have hc11 := (inv11.code env code0).parse
      have z11 := inv11.zero
      rw [resR env inv10 hpos2] at a011
      obtain ⟨m12, d12, u12⟩ := u11.alu hc11 ip_at_1c2 (off' := 0x1C4) (by decide)
      obtain ⟨m13, d13, u13⟩ := u12.aluImm hc11 ip_at_1c4 (off' := 0x1C8) (by decide)
      obtain ⟨m14, d14, u14⟩ := u13.aluImm hc11 ip_at_1c8 (off' := 0x1CC) (by decide)
      have inv14 : IInv R G ptr len out ilen M0 f0 m11.mem (reg m14) := inv11.frameR
        (fun r hr => by
          have n : ∀ q : Fin 32, q ∈ ipClob → r ≠ q := fun q hq e => hr (e ▸ hq)
          rw [u14.regs, updz (by simp) (n a0 (by decide)), updz (by simp) (n a0 (by decide)),
            updz z11 (n a1 (by decide))])
        (by rw [u14.regs]; simp +decide only [upd, ↓reduceIte]; exact inv11.sp)
        (by rw [u14.regs]; simp +decide only [upd, ↓reduceIte]; exact inv11.s0)
        (by rw [u14.regs]; simp +decide only [upd, ↓reduceIte]; exact inv11.s1)
        (by rw [u14.regs]; rfl)
      have e14a0 : reg m14 a0 = aluEval .add (aluEval .and (reg m11 a0) 0xFF) 0xFFFFFF01 := by
        rw [u14.regs, upd_a0, upd_a0, updz z11 (by decide)]
      have e14a1 : reg m14 a1 = reg m11 a0 := by
        rw [u14.regs, updz (by simp) (by decide), updz (by simp) (by decide), upd_same (by decide), z11]
        exact BitVec.zero_add _
      have u14' := u14.self
      have pre14 : Steps m m14 := (pre.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
        (.single d10)))))))).trans (c11.trans (.cons d12 (.cons d13 (.single d14))))
      unfold rdRes rdB
      revert a011
      rcases hb2 : bytesResult ptr len e 3 with _ | ⟨p2, e2⟩ <;> intro a011 <;> dsimp only at a011
      · obtain ⟨m15, d15, u15⟩ := u14'.taken hc11 0x212 ip_at_1cc (by decide)
          (by rw [e14a0, inv14.zero, a011]; decide)
        exact IErrDone.pre (pre14.trans (.single d15)) (lp_e212 env code0 inv14 u15 (by rw [e14a1, a011]; rfl))
      · show RdPost P R G ptr len out ilen M0 f0 Mx g m (Except.bind
          (if allZero M0 p2 (3 : Word).toNat = true then .ok e2 else .error 4)
          fun pos => segA M0 ptr len pos (M0 p - 1))
        by_cases hz3 : allZero M0 p2 (3 : Word).toNat = true
        · rw [ite_eq_left hz3]
          rw [ite_eq_left hz3] at a011
          obtain ⟨m15, d15, u15⟩ := u14'.notTaken hc11 0x1CE ip_at_1cc (by decide)
            (by rw [e14a0, inv14.zero, a011]; decide)
          have k11 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ s6 →
              reg m11 r = g r := fun r h0 h1 h2 h3 h4 h5 h7 h6 => by
            rw [fr11 r h0 h1 h2 h3 h4 h5 h7, u10.regs, updz (by simp) h1, updz (by simp) h0,
              updz (by simp) h0, updz (by simp) h6, updz (by simp) h1, updz z2 h0, k2 r h0 h1 h2 h3 h4 h5 h7]
          exact RdPost.pre (pre14.trans (.single d15)) _ (lp_rdA env code0 inv14 u15 (adv' p2 e2 hb2)
            (cf11.byteFr.trans cf2.byteFr)
            (by rw [u14.regs, updz (by simp) (show (s6 : Fin 32) ≠ a0 by decide),
              updz (by simp) (show (s6 : Fin 32) ≠ a0 by decide), updz z11 (show (s6 : Fin 32) ≠ a1 by decide),
              fr11 s6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              u10.regs]
                simp +decide only [upd, ↓reduceIte])
            (fun r h0 h1 h2 h3 h4 h5 h7 h6 _ => by
              rw [u14.regs, updz (by simp) h0, updz (by simp) h0, updz z11 h1, k11 r h0 h1 h2 h3 h4 h5 h7 h6]))
        · rw [ite_eq_right hz3]
          rw [ite_eq_right hz3] at a011
          obtain ⟨m15, d15, u15⟩ := u14'.taken hc11 0x212 ip_at_1cc (by decide)
            (by rw [e14a0, inv14.zero, a011]; decide)
          exact IErrDone.pre (pre14.trans (.single d15)) (lp_e212 env code0 inv14 u15
            (by rw [e14a1, a011]; rfl))

end Loop

end C3.RV32
