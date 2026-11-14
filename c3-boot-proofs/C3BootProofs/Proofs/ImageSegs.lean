import C3BootProofs.Proofs.ImageHeader
import C3BootProofs.Image.BootloaderV0

/-!
# `image::parse`: the segment array and the segment loop

The 16 segments live at `G + 0x24`, 16 bytes each: address, offset, and
length words, then a word whose low byte is the kind. `ArrInv` says the
first segments hold what the loop has read and the rest are zero.
-/

namespace C3.RV32

open C3.ImageV0

set_option maxRecDepth 20000

/-- Slot `j` holds `s`. -/
def SlotOk (M : Word → BitVec 8) (G : Word) (j : Nat) (s : SegW) : Prop :=
  memLoad32 M (G + BitVec.ofNat 32 (0x24 + 16 * j)) = s.addr ∧
  memLoad32 M (G + BitVec.ofNat 32 (0x28 + 16 * j)) = s.off ∧
  memLoad32 M (G + BitVec.ofNat 32 (0x2C + 16 * j)) = s.len ∧
  M (G + BitVec.ofNat 32 (0x30 + 16 * j)) = s.kind

/-- Slot `j` is zero. -/
def SlotZ (M : Word → BitVec 8) (G : Word) (j : Nat) : Prop :=
  ∀ w, w < 4 → memLoad32 M (G + BitVec.ofNat 32 (0x24 + 16 * j + 4 * w)) = 0

def ArrInv (M : Word → BitVec 8) (G : Word) (segs : List SegW) : Prop :=
  (∀ j (h : j < segs.length), SlotOk M G j segs[j]) ∧
  ∀ j, segs.length ≤ j → j < 16 → SlotZ M G j

/-- `M'` and `M` agree on the segment array. -/
def ArrAgree (M' M : Word → BitVec 8) (G : Word) : Prop :=
  ∀ k, k < 0x100 → M' (G + BitVec.ofNat 32 (0x24 + k)) = M (G + BitVec.ofNat 32 (0x24 + k))

theorem ArrAgree.load {M' M : Word → BitVec 8} {G : Word} (h : ArrAgree M' M G) {c : Nat}
    (h1 : 0x24 ≤ c) (h2 : c + 4 ≤ 0x124) :
    memLoad32 M' (G + BitVec.ofNat 32 c) = memLoad32 M (G + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc, show c + j = 0x24 + (c + j - 0x24) by omega]
    exact h _ (by omega)

theorem ArrInv.agree {M' M : Word → BitVec 8} {G : Word} {segs : List SegW} (a : ArrInv M G segs)
    (h : ArrAgree M' M G) (hl : segs.length ≤ 16) : ArrInv M' G segs := by
  refine ⟨fun j hj => ?_, fun j h1 h2 w hw => ?_⟩
  · obtain ⟨e1, e2, e3, e4⟩ := a.1 j hj
    refine ⟨by rw [h.load (by omega) (by omega), e1], by rw [h.load (by omega) (by omega), e2],
      by rw [h.load (by omega) (by omega), e3], ?_⟩
    rw [show 0x30 + 16 * j = 0x24 + (12 + 16 * j) by omega, h _ (by omega),
      show 0x24 + (12 + 16 * j) = 0x30 + 16 * j by omega, e4]
  · rw [h.load (by omega) (by omega)]; exact a.2 j h1 h2 w hw

theorem ArrAgree.refl (M : Word → BitVec 8) (G : Word) : ArrAgree M M G := fun _ _ => rfl

theorem ArrAgree.trans {M'' M' M : Word → BitVec 8} {G : Word} (h1 : ArrAgree M'' M' G)
    (h2 : ArrAgree M' M G) : ArrAgree M'' M G := fun k hk => (h1 k hk).trans (h2 k hk)

/-- A word stored outside the segment array leaves it alone. -/
theorem ArrAgree.st32 (M : Word → BitVec 8) (G : Word) (c : Nat) (v : Word)
    (hc : c + 4 ≤ 0x24 ∨ 0x124 ≤ c) (hc2 : c + 4 ≤ 0x200) :
    ArrAgree (memStore32 M (G + BitVec.ofNat 32 c) v) M G := fun k hk =>
  memStore32_get_sep (sep_offsets G (by omega) (by omega) (by omega))

theorem memStore32_lo (M : Word → BitVec 8) (a v : Word) : memStore32 M a v a = v.extractLsb' 0 8 := by
  have n10 : a ≠ a + 1 := by
    have := add_ofNat_ne a (c := 0) (d := 1) (by decide) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have n20 : a ≠ a + 2 := by
    have := add_ofNat_ne a (c := 0) (d := 2) (by decide) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have n30 : a ≠ a + 3 := by
    have := add_ofNat_ne a (c := 0) (d := 3) (by decide) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  unfold memStore32
  rw [memStore8_ne n30, memStore8_ne n20, memStore8_ne n10, memStore8_same]

section Segs

variable {P R G ptr len out ilen : Word} {M0 Mx : Word → BitVec 8} {f0 g : Fin 32 → Word}

/-- `IInv` holds after a word stored in the frame's scratch words or the
segment array. -/
theorem IInv.st32 (env : IEnv P R G ptr len out) (inv : IInv R G ptr len out ilen M0 f0 Mx g)
    (c : Nat) (v : Word) (hc : c + 4 ≤ 0x18 ∨ (0x24 ≤ c ∧ c + 4 ≤ 0x12C)) :
    IInv R G ptr len out ilen M0 f0 (memStore32 Mx (G + BitVec.ofNat 32 c) v) g :=
  inv.mem env fun x h1 h2 => memStore32_get_sep (by
    rw [env.g_ofs]
    rcases hc with hc | hc
    · exact h1.sub (c := 0x30 + c) (l := 4) (by omega)
    · have := h2.sub (c := 0x30 + c - 0x50) (l := 4) (by omega)
      rwa [add_ofNat_assoc, show 0x50 + (0x30 + c - 0x50) = 0x30 + c by omega] at this)

theorem dec_ofNat : ∀ t, t < 17 → 1 ≤ t → BitVec.ofNat 32 t + 0xFFFFFFFF = BitVec.ofNat 32 (t - 1) := by
  decide

theorem ofNat_ne0 : ∀ t, t < 17 → 1 ≤ t → BitVec.ofNat 32 t ≠ 0 := by decide

/-- The loop at 0x160 that zeroes the segment array, from slot `j` with `t`
slots left. -/
theorem ip_zero (env : IEnv P R G ptr len out) (code0 : ICode M0 P) :
    ∀ t j, j + t = 16 → 1 ≤ t → ∀ {Mx : Word → BitVec 8} {g : Fin 32 → Word} {m : Machine},
      IInv R G ptr len out ilen M0 f0 Mx g → St Mx P m 0x160 g →
      g a0 = G + BitVec.ofNat 32 (0x24 + 16 * j) → g a1 = BitVec.ofNat 32 t →
      ∃ m' My g', Steps m m' ∧ St My P m' 0x170 g' ∧ IInv R G ptr len out ilen M0 f0 My g' ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → g' r = g r) ∧
        (∀ c, c + 4 ≤ 0x24 + 16 * j ∨ 0x124 ≤ c → c + 4 ≤ 0x200 →
          memLoad32 My (G + BitVec.ofNat 32 c) = memLoad32 Mx (G + BitVec.ofNat 32 c)) ∧
        (∀ k, k < 0x24 + 16 * j → My (G + BitVec.ofNat 32 k) = Mx (G + BitVec.ofNat 32 k)) ∧
        (∀ j', j ≤ j' → j' < 16 → SlotZ My G j')
  | 0, _, _, h, _, _, _, _, _, _, _ => absurd h (by decide)
  | t + 1, j, hj, _, Mx, g, m, inv, s, ha0, ha1 => by
    have hc := (inv.code env code0).parse
    have hz := inv.zero
    obtain ⟨m1, d1, u1⟩ := s.aluImm hc ip_at_160 (off' := 0x162) (by decide)
    have z1 : aluEval .add (g x0) 0 = 0 := by show g 0 + 0 = 0; rw [hz]; rfl
    rw [z1] at u1
    have g1o : ∀ r, r ≠ a2 → upd g a2 0 r = g r := fun r h => updz hz h
    have e0 : upd g a2 0 a0 = G + BitVec.ofNat 32 (0x24 + 16 * j) := by rw [g1o a0 (by decide), ha0]
    have e2 : upd g a2 0 a2 = 0 := upd_same (by decide)
    have al : ∀ w, w < 4 → (G + BitVec.ofNat 32 (0x24 + 16 * j + 4 * w)).toNat % 4 = 0 := fun w _ =>
      aligned_add env.hG (by omega)
    have ad : ∀ w : Nat, w < 4 → G + BitVec.ofNat 32 (0x24 + 16 * j) + BitVec.ofNat 32 (4 * w) =
        G + BitVec.ofNat 32 (0x24 + 16 * j + 4 * w) := fun w _ => add_ofNat_assoc _ _ _
    obtain ⟨m2, d2, u2⟩ := u1.sw hc ip_at_162 (off' := 0x164) (by decide)
      (by rw [e0, add_lit_zero]; have := al 0 (by omega); rwa [Nat.mul_zero, Nat.add_zero] at this)
    rw [e0, e2, add_lit_zero] at u2
    have inv2 := inv.st32 env (0x24 + 16 * j) 0 (Or.inr ⟨by omega, by omega⟩)
    have hc2 := (inv2.code env code0).parse
    obtain ⟨m3, d3, u3⟩ := u2.sw hc2 ip_at_164 (off' := 0x166) (by decide)
      (by rw [e0, show (4 : Word) = BitVec.ofNat 32 (4 * 1) from rfl, ad 1 (by omega)]; exact al 1 (by omega))
    rw [e0, e2, show (4 : Word) = BitVec.ofNat 32 (4 * 1) from rfl, ad 1 (by omega)] at u3
    have inv3 := inv2.st32 env (0x24 + 16 * j + 4 * 1) 0 (Or.inr ⟨by omega, by omega⟩)
    have hc3 := (inv3.code env code0).parse
    obtain ⟨m4, d4, u4⟩ := u3.sw hc3 ip_at_166 (off' := 0x168) (by decide)
      (by rw [e0, show (8 : Word) = BitVec.ofNat 32 (4 * 2) from rfl, ad 2 (by omega)]; exact al 2 (by omega))
    rw [e0, e2, show (8 : Word) = BitVec.ofNat 32 (4 * 2) from rfl, ad 2 (by omega)] at u4
    have inv4 := inv3.st32 env (0x24 + 16 * j + 4 * 2) 0 (Or.inr ⟨by omega, by omega⟩)
    have hc4 := (inv4.code env code0).parse
    obtain ⟨m5, d5, u5⟩ := u4.sw hc4 ip_at_168 (off' := 0x16A) (by decide)
      (by rw [e0, show (0xC : Word) = BitVec.ofNat 32 (4 * 3) from rfl, ad 3 (by omega)]; exact al 3 (by omega))
    rw [e0, e2, show (0xC : Word) = BitVec.ofNat 32 (4 * 3) from rfl, ad 3 (by omega)] at u5
    have inv5 := inv4.st32 env (0x24 + 16 * j + 4 * 3) 0 (Or.inr ⟨by omega, by omega⟩)
    have hc5 := (inv5.code env code0).parse
    obtain ⟨m6, d6, u6⟩ := u5.aluImm hc5 ip_at_16a (off' := 0x16C) (by decide)
    obtain ⟨m7, d7, u7⟩ := u6.aluImm hc5 ip_at_16c (off' := 0x16E) (by decide)
    generalize hM5 : memStore32 (memStore32 (memStore32 (memStore32 Mx (G + BitVec.ofNat 32 (0x24 + 16 * j)) 0)
      (G + BitVec.ofNat 32 (0x24 + 16 * j + 4 * 1)) 0) (G + BitVec.ofNat 32 (0x24 + 16 * j + 4 * 2)) 0)
      (G + BitVec.ofNat 32 (0x24 + 16 * j + 4 * 3)) 0 = M5 at u7 inv5 hc5
    have g7a0 : upd (upd (upd g a2 0) a0 (aluEval .add (upd g a2 0 a0) 0x10)) a1
        (aluEval .add (upd (upd g a2 0) a0 (aluEval .add (upd g a2 0 a0) 0x10) a1) 0xFFFFFFFF) a0 =
        G + BitVec.ofNat 32 (0x24 + 16 * (j + 1)) := by
      rw [updz (by simp) (by decide), upd_a0, e0]; show _ + _ = _
      rw [show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl, add_ofNat_assoc]
      congr 2 <;> omega
    have g7a1 : upd (upd (upd g a2 0) a0 (aluEval .add (upd g a2 0 a0) 0x10)) a1
        (aluEval .add (upd (upd g a2 0) a0 (aluEval .add (upd g a2 0 a0) 0x10) a1) 0xFFFFFFFF) a1 =
        BitVec.ofNat 32 t := by
      rw [upd_same (by decide), updz (by simp) (by decide), g1o a1 (by decide), ha1]
      show BitVec.ofNat 32 (t + 1) + 0xFFFFFFFF = _
      rw [dec_ofNat (t + 1) (by omega) (by omega)]; rfl
    have g7o : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 →
        upd (upd (upd g a2 0) a0 (aluEval .add (upd g a2 0 a0) 0x10)) a1
          (aluEval .add (upd (upd g a2 0) a0 (aluEval .add (upd g a2 0 a0) 0x10) a1) 0xFFFFFFFF) r = g r :=
      fun r h0 h1 h2 => by rw [updz (by simp) h1, updz (by simp) h0, g1o r h2]
    have inv7 : IInv R G ptr len out ilen M0 f0 M5
        (upd (upd (upd g a2 0) a0 (aluEval .add (upd g a2 0 a0) 0x10)) a1
          (aluEval .add (upd (upd g a2 0) a0 (aluEval .add (upd g a2 0 a0) 0x10) a1) 0xFFFFFFFF)) :=
      inv5.regs fun r h0 h1 h2 _ _ _ _ => by rw [g7o r h0 h1 h2]
    -- What the four stores did.
    have Mout : ∀ c, c + 4 ≤ 0x24 + 16 * j ∨ 0x24 + 16 * (j + 1) ≤ c → c + 4 ≤ 0x200 →
        memLoad32 M5 (G + BitVec.ofNat 32 c) = memLoad32 Mx (G + BitVec.ofNat 32 c) := fun c h1 h2 => by
      rw [← hM5, memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega))]
    have Mbyte : ∀ k, (k < 0x24 + 16 * j ∨ 0x24 + 16 * (j + 1) ≤ k) → k < 0x200 →
        M5 (G + BitVec.ofNat 32 k) = Mx (G + BitVec.ofNat 32 k) := fun k h1 h2 => by
      rw [← hM5, memStore32_get_sep (sep_offsets G (by omega) (by omega) (by omega)),
        memStore32_get_sep (sep_offsets G (by omega) (by omega) (by omega)),
        memStore32_get_sep (sep_offsets G (by omega) (by omega) (by omega)),
        memStore32_get_sep (sep_offsets G (by omega) (by omega) (by omega))]
    have Mz : SlotZ M5 G j := fun w hw => by
      rw [← hM5]
      rcases (by omega : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) with rfl | rfl | rfl | rfl
      · rw [memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega)),
          memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega)),
          memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega)), Nat.mul_zero,
          Nat.add_zero, memLoad32_store32_same]
      · rw [memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega)),
          memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega)),
          memLoad32_store32_same]
      · rw [memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega)),
          memLoad32_store32_same]
      · rw [memLoad32_store32_same]
    by_cases ht : t = 0
    · subst ht
      obtain ⟨m8, d8, u8⟩ := u7.notTaken hc5 0x170 ip_at_16e (by decide)
        (by rw [g7a1, show upd (upd (upd g a2 0) a0 (aluEval .add (upd g a2 0 a0) 0x10)) a1
          (aluEval .add (upd (upd g a2 0) a0 (aluEval .add (upd g a2 0 a0) 0x10) a1) 0xFFFFFFFF) x0 = 0
          from rfl]; decide)
      refine ⟨m8, M5, _, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7
        (.single d8))))))), u8, inv7, g7o, fun c h1 h2 => Mout c (by omega) h2,
        fun k hk => Mbyte k (by omega) (by omega), fun j' h1 h2 => ?_⟩
      have : j' = j := by omega
      subst this; exact Mz
    · obtain ⟨m8, d8, u8⟩ := u7.taken hc5 0x160 ip_at_16e (by decide)
        (by rw [g7a1, show upd (upd (upd g a2 0) a0 (aluEval .add (upd g a2 0 a0) 0x10)) a1
          (aluEval .add (upd (upd g a2 0) a0 (aluEval .add (upd g a2 0 a0) 0x10) a1) 0xFFFFFFFF) x0 = 0
          from rfl]; exact bne_iff_ne.mpr (ofNat_ne0 t (by omega) (by omega)))
      obtain ⟨m', My, g', c', u', inv', ko, mo, bo, zo⟩ :=
        ip_zero env code0 t (j + 1) (by omega) (by omega) inv7 u8 g7a0 g7a1
      refine ⟨m', My, g', (Steps.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7
        (.single d8)))))))).trans c', u', inv', fun r h0 h1 h2 => by rw [ko r h0 h1 h2, g7o r h0 h1 h2],
        fun c h1 h2 => ?_, fun k hk => ?_, fun j' h1 h2 => ?_⟩
      · rcases h1 with h1 | h1
        · rw [mo c (Or.inl (by omega)) h2, Mout c (Or.inl h1) h2]
        · rw [mo c (Or.inr h1) h2, Mout c (Or.inr (by omega)) h2]
      · rw [bo k (by omega), Mbyte k (Or.inl hk) (by omega)]
      · by_cases hj' : j' = j
        · subst hj'
          intro w hw
          rw [mo _ (Or.inl (by omega)) (by omega)]; exact Mz w hw
        · exact zo j' (by omega) h2

/-- `IInv` holds for any registers that agree outside `ipClob` and keep
`sp`, `s0`, and `s1`. -/
theorem IInv.frameR (inv : IInv R G ptr len out ilen M0 f0 Mx g) {g' : Fin 32 → Word}
    (h : ∀ r, r ∉ ipClob → g' r = g r) (hsp : g' RV32.sp = G) (hs0 : g' RV32.s0 = out) (hs1 : g' RV32.s1 = ilen)
    (hz : g' 0 = 0) : IInv R G ptr len out ilen M0 f0 Mx g' :=
  ⟨inv.outside, inv.slots, inv.rdp, inv.rdl, hsp, hs0, hs1, fun r hr => by rw [h r hr, inv.keep r hr], hz⟩

end Segs

/-- The segment loop's invariant at offset 0x188, with `segs` read so far. -/
structure LInv (R G ptr len out ilen : Word) (M0 : Word → BitVec 8) (f0 : Fin 32 → Word)
    (sv cnt : BitVec 8) (entry : Word) (segs : List SegW) (pos prev : Word)
    (Mx : Word → BitVec 8) (g : Fin 32 → Word) : Prop where
  inv : IInv R G ptr len out ilen M0 f0 Mx g
  pos : memLoad32 Mx (G + 0x18 + 8) = pos
  arr : ArrInv Mx G segs
  hl : segs.length ≤ cnt.toNat
  hc : cnt.toNat ≤ 16
  s2 : g s2 = sv.zeroExtend 32
  s11 : g s11 = cnt.zeroExtend 32 <<< 4
  s8 : g s8 = BitVec.ofNat 32 (0x100 - 16 * segs.length)
  s9 : g s9 = G + BitVec.ofNat 32 (0x2C + 16 * segs.length)
  s5 : g s5 = prev
  mask : memLoad32 Mx (G + 0x14) = 0xFFFF
  ent : memLoad32 Mx (G + 8) = entry
  cntw : memLoad32 Mx (G + 0xC) = cnt.zeroExtend 32

section Segs

variable {P R G ptr len out ilen : Word} {M0 Mx : Word → BitVec 8} {f0 g : Fin 32 → Word}

/-- **Setup**: from offset 0x15A, the segment array zeroed, then the loop's
registers; the loop starts at 0x188 with no segments read. -/
theorem ip_setup (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (s : St Mx P m 0x15A g)
    {pos entry : Word} {sv cnt : BitVec 8} (hpos : memLoad32 Mx (G + 0x18 + 8) = pos)
    (h2 : g s2 = sv.zeroExtend 32) (hent : memLoad32 Mx (G + 8) = entry)
    (hcw : memLoad32 Mx (G + 0xC) = cnt.zeroExtend 32) (hc16 : cnt.toNat ≤ 16) :
    ∃ m' My g', Steps m m' ∧ St My P m' 0x188 g' ∧
      LInv R G ptr len out ilen M0 f0 sv cnt entry [] pos (cnt.zeroExtend 32 <<< 4 + 0x14) My g' := by
  have hc := (inv.code env code0).parse
  have hz := inv.zero
  obtain ⟨m1, d1, u1⟩ := s.aluImm hc ip_at_15a (off' := 0x15C) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.aluImm hc ip_at_15c (off' := 0x15E) (by decide)
  have g2o : ∀ r, r ≠ a0 → r ≠ a1 →
      upd (upd g a0 (aluEval .add (g sp) 0x24)) a1 (aluEval .add (upd g a0 (aluEval .add (g sp) 0x24) x0) 0x10) r
        = g r := fun r h0 h1 => by rw [updz (by simp) h1, updz hz h0]
  have g2a1 : upd (upd g a0 (aluEval .add (g sp) 0x24)) a1
      (aluEval .add (upd g a0 (aluEval .add (g sp) 0x24) x0) 0x10) a1 = BitVec.ofNat 32 16 := by
    rw [upd_same (by decide)]; show upd g a0 _ 0 + _ = _; rw [upd_zero]; rfl
  have g2a0 : upd (upd g a0 (aluEval .add (g sp) 0x24)) a1
      (aluEval .add (upd g a0 (aluEval .add (g sp) 0x24) x0) 0x10) a0 = G + BitVec.ofNat 32 (0x24 + 16 * 0) := by
    rw [updz (by simp) (by decide), upd_a0]; show g sp + _ = _; rw [inv.sp]; rfl
  obtain ⟨m3, d3, u3⟩ := u2.notTaken hc 0x160 ip_at_15e (by decide) (by rw [g2a1]; rfl)
  have inv2 : IInv R G ptr len out ilen M0 f0 Mx (upd (upd g a0 (aluEval .add (g sp) 0x24)) a1
      (aluEval .add (upd g a0 (aluEval .add (g sp) 0x24) x0) 0x10)) :=
    inv.regs fun r h0 h1 _ _ _ _ _ => g2o r h0 h1
  obtain ⟨m4, M4, g4, c4, u4, inv4, k4, lo4, -, z4⟩ :=
    ip_zero env code0 16 0 (by omega) (by omega) inv2 u3 g2a0 g2a1
  have k4' : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → g4 r = g r := fun r h0 h1 h2 => by
    rw [k4 r h0 h1 h2, g2o r h0 h1]
  have hc4 := (inv4.code env code0).parse
  have z4' := inv4.zero
  have sp4 := inv4.sp
  -- 0x170: the address word, then the loop's registers.
  obtain ⟨m5, d5, u5⟩ := u4.sw hc4 ip_at_170 (off' := 0x172) (by decide)
    (by rw [sp4]; exact aligned_add env.hG (k := 0x10) (by decide))
  rw [sp4, z4'] at u5
  have inv5 := inv4.st32 env 0x10 0 (Or.inl (by omega))
  have hc5 := (inv5.code env code0).parse
  obtain ⟨m6, d6, u6⟩ := u5.lui hc5 ip_at_172 (off' := 0x174) (by decide)
  obtain ⟨m7, d7, u7⟩ := u6.lw hc5 ip_at_174 (off' := 0x176) (by decide)
    (by rw [updz z4' (by decide), sp4]; exact aligned_add env.hG (k := 0xC) (by decide))
  have v7 : memLoad32 (memStore32 M4 (G + 0x10) 0) (upd g4 a0 0x10000 sp + 0xC) = cnt.zeroExtend 32 := by
    rw [updz z4' (by decide), sp4,
      memLoad32_store32_sep (show Sep (G + 0x10) 4 (G + 0xC) 4 from
        sep_offsets G (c := 0x10) (n := 4) (d := 0xC) (k := 4) (by omega) (by omega) (by omega)),
      show G + 0xC = G + BitVec.ofNat 32 0xC from rfl, lo4 0xC (by omega) (by omega)]
    exact hcw
  rw [v7] at u7
  obtain ⟨m8, d8, u8⟩ := u7.aluImm hc5 ip_at_176 (off' := 0x178) (by decide)
  obtain ⟨m9, d9, u9⟩ := u8.aluImm hc5 ip_at_178 (off' := 0x17A) (by decide)
  obtain ⟨m10, d10, u10⟩ := u9.sw hc5 ip_at_17a (off' := 0x17C) (by decide)
    (by simp +decide only [upd, ↓reduceIte]; rw [sp4]; exact aligned_add env.hG (k := 0x14) (by decide))
  have v10 : upd (upd (upd (upd g4 a0 0x10000) s11 (cnt.zeroExtend 32)) s11
      (aluEval .sll (upd (upd g4 a0 0x10000) s11 (cnt.zeroExtend 32) s11) 4)) a0
      (aluEval .add (upd (upd (upd g4 a0 0x10000) s11 (cnt.zeroExtend 32)) s11
        (aluEval .sll (upd (upd g4 a0 0x10000) s11 (cnt.zeroExtend 32) s11) 4) a0) 0xFFFFFFFF) sp = G := by
    simp +decide only [upd, ↓reduceIte]; exact sp4
  have v10a : upd (upd (upd (upd g4 a0 0x10000) s11 (cnt.zeroExtend 32)) s11
      (aluEval .sll (upd (upd g4 a0 0x10000) s11 (cnt.zeroExtend 32) s11) 4)) a0
      (aluEval .add (upd (upd (upd g4 a0 0x10000) s11 (cnt.zeroExtend 32)) s11
        (aluEval .sll (upd (upd g4 a0 0x10000) s11 (cnt.zeroExtend 32) s11) 4) a0) 0xFFFFFFFF) a0 = 0xFFFF := by
    simp +decide only [upd, ↓reduceIte]
  rw [v10, v10a] at u10
  have inv10 := inv5.st32 env 0x14 0xFFFF (Or.inl (by omega))
  have hc10 := (inv10.code env code0).parse
  obtain ⟨m11, d11, u11⟩ := u10.aluImm hc10 ip_at_17c (off' := 0x180) (by decide)
  obtain ⟨m12, d12, u12⟩ := u11.aluImm hc10 ip_at_180 (off' := 0x184) (by decide)
  obtain ⟨m13, d13, u13⟩ := u12.aluImm hc10 ip_at_184 (off' := 0x188) (by decide)
  refine ⟨m13, _, _, .cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (.cons d6 (.cons d7 (.cons d8
    (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.single d13)))))))))))), u13, ?_⟩
  have M10 : ∀ c, c + 4 ≤ 0x10 ∨ (0x18 ≤ c) → c + 4 ≤ 0x200 →
      memLoad32 (memStore32 (memStore32 M4 (G + 0x10) 0) (G + 0x14) 0xFFFF) (G + BitVec.ofNat 32 c) =
        memLoad32 M4 (G + BitVec.ofNat 32 c) := fun c h1 h2 => by
    rw [memLoad32_store32_sep (show Sep (G + 0x14) 4 (G + BitVec.ofNat 32 c) 4 from
        sep_offsets G (c := 0x14) (n := 4) (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (show Sep (G + 0x10) 4 (G + BitVec.ofNat 32 c) 4 from
        sep_offsets G (c := 0x10) (n := 4) (by omega) (by omega) (by omega))]
  refine ⟨inv10.frameR (fun r hr => ?_) ?_ ?_ ?_ ?_, ?_, ⟨fun j h => absurd h (by simp), fun j _ h2 w hw => ?_⟩,
    by simp, hc16, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have n : ∀ q : Fin 32, q ∈ ipClob → r ≠ q := fun q hq e => hr (e ▸ hq)
    rw [updz (by simp) (n s9 (by decide)), updz (by simp) (n s8 (by decide)),
      updz (by simp) (n s5 (by decide)), updz (by simp) (n a0 (by decide)),
      updz (by simp) (n s11 (by decide)), updz (by simp) (n s11 (by decide)), updz z4' (n a0 (by decide))]
  · simp +decide only [upd, ↓reduceIte]; exact sp4
  · simp +decide only [upd, ↓reduceIte]; exact inv4.s0
  · simp +decide only [upd, ↓reduceIte]; exact inv4.s1
  · rfl
  · rw [show G + 0x18 + 8 = G + BitVec.ofNat 32 0x20 by rw [BitVec.add_assoc]; rfl,
      M10 0x20 (Or.inr (by omega)) (by omega), lo4 0x20 (Or.inl (by omega)) (by omega),
      show G + BitVec.ofNat 32 0x20 = G + 0x18 + 8 by rw [BitVec.add_assoc]; rfl, hpos]
  · rw [M10 _ (Or.inr (by omega)) (by omega)]; exact z4 j (by omega) h2 w hw
  · simp +decide only [upd, ↓reduceIte]; rw [k4' s2 (by decide) (by decide) (by decide)]; exact h2
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rw [sp4]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · exact memLoad32_store32_same _ _ _
  · rw [show G + 8 = G + BitVec.ofNat 32 8 from rfl, M10 8 (Or.inl (by omega)) (by omega),
      lo4 8 (Or.inl (by omega)) (by omega)]; exact hent
  · rw [show G + 0xC = G + BitVec.ofNat 32 0xC from rfl, M10 0xC (Or.inl (by omega)) (by omega),
      lo4 0xC (Or.inl (by omega)) (by omega)]; exact hcw

end Segs

end C3.RV32
