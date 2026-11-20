import C3BootProofs.Proofs.SvZLib
import C3BootProofs.Proofs.Dec256Calls

/-!
# `sigstore::verify`: wrappers for the end of the P-256 check

The calls between the inversion of the sum's `Z` and the comparison of its
affine `x` with `r`: the field's `conditional_select` with both operands in
the frame, `multiply`, `CtOption::map`, and `retrieve`. Each wraps the
caller-agnostic call in `P2Lib.lean` or `Dec256Calls.lean` for
`sigstore::verify`'s frame.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gd C3.RV32.P2

set_option maxRecDepth 20000

/-- A callee's frame-preservation fact, in the forms the stages use: it
keeps the bytes outside the frame, and the frame outside `[co, co + w)`. -/
theorem sv_frOut {B : Word} {M M' : Word → BitVec 8} {L : Word} {k co w : Nat}
    (hL : L = BitVec.ofNat 32 (2 ^ 32 - k)) (hk : k ≤ 0x21A0) (hk0 : 0 < k) (hco : co + w ≤ 0x1690)
    (f : ∀ x, Sep (B + 0x21A0 + L) k x 1 → Sep (B + 0x21A0 + BitVec.ofNat 32 co) w x 1 → M' x = M x) :
    (∀ x, SvR B x → M' x = M x) ∧ SvKeepL B M M' [(co, w)] := by
  subst hL
  refine ⟨fun x hx => f x (by rw [sv_spX B k hk]; exact svR_spX hx (by omega) hk0 hk) (svR_hi hx hco),
    fun e he hL => ?_⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  exact f _ (by rw [sv_spX B k hk, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

theorem acc_sel {M M' : Word → BitVec 8} {o a b c : Word}
    (W : ∀ i, i < 8 → memLoad32 M' (o + BitVec.ofNat 32 (4 * i)) =
      if c = 1 then memLoad32 M (b + BitVec.ofNat 32 (4 * i)) else memLoad32 M (a + BitVec.ofNat 32 (4 * i))) :
    accV M' o 8 = if c = 1 then accV M b 8 else accV M a 8 := by
  by_cases h : c = 1
  · rw [ite_eq_left h]; exact accV_congr2 8 fun i hi => by rw [W i hi, ite_eq_left h]
  · rw [ite_eq_right h]; exact accV_congr2 8 fun i hi => by rw [W i hi, ite_eq_right h]

theorem sv_sepLow {B : Word} {c l k : Nat} (hc : c + l ≤ 0x1690) (hk : k ≤ 0x21A0) :
    Sep (B + 0x21A0 + BitVec.ofNat 32 c) l (B + 0x21A0 + BitVec.ofNat 32 (2 ^ 32 - k)) k := by
  rw [sv_spX B k hk, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)

set_option maxHeartbeats 8000000 in
/-- **A call to the P-256 field's `conditional_select`** of the limbs at
offsets `ca` and `cb` by the choice `c`, into offset `co`. -/
theorem sv_cselF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o c : Word} {co ca cb : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (K : P2Code M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = CS2) (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 ca) (ha2 : reg n a2 = B + 0x21A0 + BitVec.ofNat 32 cb)
    (ha3 : reg n a3 = c) (hc : c = 0 ∨ c = 1)
    (hco : co + 32 ≤ 0x1690) (hca : ca + 32 ≤ 0x1690) (hcb : cb + 32 ≤ 0x1690) (acb : cb % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 =
        (if c = 1 then accV M (B + 0x21A0 + BitVec.ofNat 32 cb) 8 else accV M (B + 0x21A0 + BitVec.ofNat 32 ca) 8) ∧
      SvKeepL B M n'.mem [(co, 32)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  obtain ⟨n', c1, s1, W, f, sp1, k1⟩ := c2_csel s C.self K FS h1 h2 hb hev rsp ha0 ha1 ha2 ha3 hc hco hca hcb
    rfl rfl rfl acb
  obtain ⟨fR, K1⟩ := sv_frOut (k := 0x50) (by decide) (by decide) (by decide) hco f
  exact ⟨n', c1, s1, sp1, k1, acc_sel W, K1, fR⟩

set_option maxHeartbeats 8000000 in
/-- **A call to the P-256 field's `multiply`** of the limbs at offsets `cx`
and `cy`, each below `p`, into offset `co`: their Montgomery product. -/
theorem sv_fmulF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {co cx cy : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (K : P2Code M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = FMUL) (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cx) (ha2 : reg n a2 = B + 0x21A0 + BitVec.ofNat 32 cy)
    (hco : co + 32 ≤ 0x1690) (hcx : cx + 32 ≤ 0x1690) (hcy : cy + 32 ≤ 0x1690)
    (aco : co % 4 = 0) (acx : cx % 4 = 0) (acy : cy % 4 = 0)
    (hX : accV M (B + 0x21A0 + BitVec.ofNat 32 cx) 8 < p256) (hY : accV M (B + 0x21A0 + BitVec.ofNat 32 cy) 8 < p256) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 =
        p2fm (accV M (B + 0x21A0 + BitVec.ofNat 32 cx) 8) (accV M (B + 0x21A0 + BitVec.ofNat 32 cy) 8) ∧
      SvKeepL B M n'.mem [(co, 32)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  obtain ⟨n', c1, s1, V, f, sp1, k1⟩ := c2_fmul s C.self K FS h1 h2 hb hev rsp ha0 ha1 ha2 hco rfl aco
    (sv_sepLow (k := 0x130) hcx (by decide)) (sv_al F (by omega) acx)
    (sv_sepLow (k := 0x130) hcy (by decide)) (sv_al F (by omega) acy) hX hY
  obtain ⟨fR, K1⟩ := sv_frOut (k := 0x130) (by decide) (by decide) (by decide) hco f
  exact ⟨n', c1, s1, sp1, fun q hq => k1 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide), V, K1, fR⟩

set_option maxHeartbeats 8000000 in
/-- **A call to `CtOption<MontyFieldElement<p256>>::map`** of the option at
offset `cx`, its limbs and then its choice byte, into offset `co`: the limbs
when the choice is 1, otherwise zero, and the choice. -/
theorem sv_cmapF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {co cx : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (K : P2Code M) (G : GdCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = CMAP2) (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cx) (hco : co + 0x21 ≤ 0x1690) (hcx : cx + 0x21 ≤ 0x1690)
    (acx : cx % 4 = 0)
    (hc : M (B + 0x21A0 + BitVec.ofNat 32 (cx + 0x20)) = 0 ∨ M (B + 0x21A0 + BitVec.ofNat 32 (cx + 0x20)) = 1) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 =
        (if M (B + 0x21A0 + BitVec.ofNat 32 (cx + 0x20)) = 1 then accV M (B + 0x21A0 + BitVec.ofNat 32 cx) 8
          else 0) ∧
      n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x20)) = M (B + 0x21A0 + BitVec.ofNat 32 (cx + 0x20)) ∧
      SvKeepL B M n'.mem [(co, 0x21)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have e20 : ∀ c, B + 0x21A0 + BitVec.ofNat 32 c + 0x20 = B + 0x21A0 + BitVec.ofNat 32 (c + 0x20) := fun c => by
    rw [show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, add_ofNat_assoc]
  obtain ⟨n', c1, s1, W, top, f, sp1, k1⟩ := c2_cmap s C.self K G FS h1 h2 hb hev rsp ha0 ha1 hco hcx rfl rfl acx
    (by rw [e20]; exact hc)
  rw [e20, e20] at top
  rw [e20] at W
  obtain ⟨fR, K1⟩ := sv_frOut (k := 0x80) (by decide) (by decide) (by decide) hco f
  refine ⟨n', c1, s1, sp1, k1, ?_, top, K1, fR⟩
  by_cases h : M (B + 0x21A0 + BitVec.ofNat 32 (cx + 0x20)) = 1
  · rw [ite_eq_left h]; exact accV_congr2 8 fun i hi => by rw [W i hi, ite_eq_left h]
  · rw [ite_eq_right h]
    exact (accV_zero_iff 8).2 fun i hi => by rw [W i hi, ite_eq_right h]

set_option maxHeartbeats 8000000 in
/-- **A call to the P-256 field's `retrieve`** of the Montgomery limbs at
offset `cx`, below `p`, into offset `co`: the plain value. -/
theorem sv_fretF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {co cx : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (K : P2Code M) (G : GdCode M) (D : P2Data M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = RT2) (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cx) (hco : co + 32 ≤ 0x1690) (hcx : cx + 32 ≤ 0x1690)
    (aco : co % 4 = 0) (acx : cx % 4 = 0) (hX : accV M (B + 0x21A0 + BitVec.ofNat 32 cx) 8 < p256) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 = p2fm (accV M (B + 0x21A0 + BitVec.ofNat 32 cx) 8) 1 ∧
      SvKeepL B M n'.mem [(co, 32)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  obtain ⟨n', c1, s1, V, f, sp1, k1⟩ := c2_rt s C.self K G D FS h1 h2 hb hev rsp ha0 ha1 hco hcx rfl rfl aco acx hX
  obtain ⟨fR, K1⟩ := sv_frOut (k := 0x40) (by decide) (by decide) (by decide) hco f
  exact ⟨n', c1, s1, sp1, k1, V, K1, fR⟩

theorem acc_selP {M M' : Word → BitVec 8} {o a b : Word} {P : Prop} [Decidable P]
    (W : ∀ i, i < 8 → memLoad32 M' (o + BitVec.ofNat 32 (4 * i)) =
      if P then memLoad32 M (b + BitVec.ofNat 32 (4 * i)) else memLoad32 M (a + BitVec.ofNat 32 (4 * i))) :
    accV M' o 8 = if P then accV M b 8 else accV M a 8 := by
  by_cases h : P
  · rw [ite_eq_left h]; exact accV_congr2 8 fun i hi => by rw [W i hi, ite_eq_left h]
  · rw [ite_eq_right h]; exact accV_congr2 8 fun i hi => by rw [W i hi, ite_eq_right h]

set_option maxHeartbeats 16000000 in
/-- **A call to `CtOption<AffinePoint<NistP256>>::unwrap_or`** of the option
at offset `cs`, its point's `x` and `y` and then its choice byte at 0x44,
with the default point at `d` among the image's constants, into offset `co`:
the option's point when its choice is 1, otherwise the default. -/
theorem sv_uorF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o d : Word} {co cs : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (K : P2Code M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 unwrapOr256Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cs) (ha2 : reg n a2 = d)
    (hco : co + 0x41 ≤ 0x1690) (hcs : cs + 0x45 ≤ 0x1690) (acs : cs % 4 = 0)
    (hsd : co + 0x41 ≤ cs ∨ cs + 0x45 ≤ co) (hd1 : 0x3FCC4200 ≤ d.toNat) (hd2 : d.toNat + 0x41 ≤ 0x3FCC4E60)
    (hc : M (B + 0x21A0 + BitVec.ofNat 32 (cs + 0x44)) = 0 ∨ M (B + 0x21A0 + BitVec.ofNat 32 (cs + 0x44)) = 1) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 =
        (if M (B + 0x21A0 + BitVec.ofNat 32 (cs + 0x44)) = 1 then accV M (B + 0x21A0 + BitVec.ofNat 32 cs) 8
          else accV M d 8) ∧
      SvKeepL B M n'.mem [(co, 0x41)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hSl := FS.lo; have hSh := FS.hi; have hSa := FS.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have e44 : B + 0x21A0 + BitVec.ofNat 32 cs + 0x44 = B + 0x21A0 + BitVec.ofNat 32 (cs + 0x44) := by
    rw [show (0x44 : Word) = BitVec.ofNat 32 0x44 from rfl, add_ofNat_assoc]
  have env : UO2Env n1.mem (BitVec.ofNat 32 unwrapOr256Address) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 co)
      (B + 0x21A0 + BitVec.ofNat 32 cs) d := by
    rw [mem1]
    refine ⟨by decide, K.uor2, ?_, ?_, ?_, ?_, by omega, by omega, sv_al F (by omega) acs,
      by rw [sv_at F _ (by omega)]; omega, by omega, by rw [sv_at F _ (by omega)]; omega,
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide),
      FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide),
      FS.lowN (k := 0x70) (by decide) (by decide) hco, FS.lowN (k := 0x70) (by decide) (by decide) hcs,
      (FS.lowData (c := 0x70) (by decide) rfl hd1 (by omega)).symm,
      sepS (B + 0x21A0) hsd (by omega) (by omega), FS.bufData hco hd1 hd2⟩
    · rw [show BitVec.ofNat 32 unwrapOr256Address + 0xE460 = BitVec.ofNat 32 condSelect256Address by decide]
      exact K.csel2
    · rw [show BitVec.ofNat 32 unwrapOr256Address + 0xE460 + 0x323E = MCS by decide]; exact C.K.stub
    · rw [show BitVec.ofNat 32 unwrapOr256Address + 0xE460 + 0x323E + 8 = MCS + 8 by decide]; exact C.K.body
    · rw [show BitVec.ofNat 32 unwrapOr256Address + 0xE460 + 0xFFFFC076 = BitVec.ofNat 32 sliceCtAssignAddress by
        decide]; exact C.K.sca
  obtain ⟨n2, c2, pc2, sp2, W1, -, -, k2, f2⟩ := unwrapOr256_correct n1 env pc1 (by rw [r1 sp (by decide), rsp])
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [mem1, e44]; exact hc) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [mem1, e44] at W1
  rw [mem1] at f2
  obtain ⟨fR, K1⟩ := sv_frOut (k := 0x70) (by decide) (by decide) (by decide) hco f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], acc_selP W1,
    K1, fR⟩

set_option maxHeartbeats 16000000 in
/-- **A call to `<Scalar as ConstantTimeEq>::ct_eq`** for P-256 of the
scalars at offsets `ca` and `cb`: 1 when their limbs agree, otherwise 0. -/
theorem sv_sctF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {ca cb : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (K : P2Code M)
    (SC : CodeIn M (BitVec.ofNat 32 p256ScalarCtEqAddress) p256ScalarCtEqCode) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 p256ScalarCtEqAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 ca)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cb) (hca : ca + 32 ≤ 0x1690) (hcb : cb + 32 ≤ 0x1690)
    (aca : ca % 4 = 0) (acb : cb % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      reg n' a0 = (if ∀ i : Nat, i < 8 → memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 ca + BitVec.ofNat 32 (4 * i)) =
        memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 cb + BitVec.ofNat 32 (4 * i)) then 1 else 0) ∧
      SvKeepL B M n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hSl := FS.lo; have hSh := FS.hi; have hSa := FS.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have env : P2SEnv n1.mem (BitVec.ofNat 32 p256ScalarCtEqAddress) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 ca)
      (B + 0x21A0 + BitVec.ofNat 32 cb) := by
    rw [mem1]
    refine ⟨by decide, SC, ?_, ?_, ?_, ?_, ?_, ?_, by omega, by omega, sv_al F (by omega) aca,
      sv_al F (by omega) acb,
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowN (k := 0x54) (by decide) (by decide) hca, FS.lowN (k := 0x54) (by decide) (by decide) hcb⟩
    · rw [show BitVec.ofNat 32 p256ScalarCtEqAddress + 0xFFFFFB5E = BitVec.ofNat 32 uint8CtEqAddress by decide]
      exact K.u8ce
    · rw [show BitVec.ofNat 32 p256ScalarCtEqAddress + 0xFFFFFB5E + 0x80 = BitVec.ofNat 32 splitAt8Address by decide]
      exact K.spl8
    · rw [show BitVec.ofNat 32 p256ScalarCtEqAddress + 0xFFFFFB5E + 0xFFFFBCE6 = BitVec.ofNat 32 limbCtEqAddress by
        decide]; exact C.K.lce
    · rw [show BitVec.ofNat 32 p256ScalarCtEqAddress + 0xFFFFFB5E + 0xFFFF12EE = BitVec.ofNat 32 uintRefIsZeroAddress by
        decide]; exact C.K.uiz
    · rw [show BitVec.ofNat 32 p256ScalarCtEqAddress + 0xFFFFFB5E + 0xFFFF12EE + 0x1A =
        BitVec.ofNat 32 uintRefIsNonzeroAddress by decide]; exact C.K.refnz
    · rw [show BitVec.ofNat 32 p256ScalarCtEqAddress + 0xFFFFB93E = BitVec.ofNat 32 blackBoxU8Address by decide]
      exact C.K.bb
  obtain ⟨n2, c2, pc2, sp2, a02, k2, f2⟩ := p256ScalarCtEq_correct n1 env pc1 (by rw [r1 sp (by decide), rsp])
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev)
  rw [mem1] at a02 f2
  have k0 := sv_frOut (k := 0x54) (co := 0) (w := 1) (by decide) (by decide) (by decide) (by decide)
    (fun x hx _ => f2 x hx)
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], a02,
    fun e he _ => f2 _ ?_, k0.1⟩
  rw [show (0xFFFFFFAC : Word) = BitVec.ofNat 32 (2 ^ 32 - 0x54) from rfl, sv_spX B 0x54 (by decide), ← sv_base']
  exact sepS B (by omega) (by omega) (by omega)

set_option maxHeartbeats 8000000 in
/-- **A call to `hybrid_array`'s zeroing `from_fn`** for 32 bytes at offset
`co`. -/
theorem sv_z32F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {co : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (K : P2Code M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 shaZero32Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (hco : co + 32 ≤ 0x1690) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + j)) = 0) ∧
      SvKeepL B M n'.mem [(co, 32)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hSl := FS.lo; have hSh := FS.hi; have hSa := FS.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨n2, c2, pc2, sp2, k2, f2⟩ := shaZero32_correct n1 (d := B + 0x21A0 + BitVec.ofNat 32 co)
    (by rw [mem1]; exact K.sz) (by rw [mem1]; exact C.K.stub) (by rw [mem1]; exact C.K.body) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
    (by rw [r1 sp (by decide), rsp]) hSa (by omega) (by omega) (by rw [sv_at F _ (by omega)]; omega)
    (FS.lowN (k := 0x40) (by decide) (by decide) hco)
  rw [mem1] at f2
  have hlow : ∀ e, e < 0x1690 → Sep (B + 0x21A0 + 0xFFFFFFC0) 0x40 (B + 0x21A0 + BitVec.ofNat 32 e) 1 := fun e he => by
    rw [show (0xFFFFFFC0 : Word) = BitVec.ofNat 32 (2 ^ 32 - 0x40) from rfl, sv_spX B 0x40 (by decide), ← sv_base']
    exact sepS B (by omega) (by omega) (by omega)
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => by
    rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], fun j hj => ?_, fun e he hL => ?_,
    fun x hx => ?_⟩
  · rw [f2 _ (hlow _ (by omega))]
    unfold fillBytes
    rw [ite_eq_left (by
      rw [← add_ofNat_assoc, BitVec.add_comm (B + 0x21A0 + BitVec.ofNat 32 co), BitVec.add_sub_cancel,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hj)]
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    rw [f2 _ (hlow e (by omega))]
    exact fillBytes_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega)) (Nat.le_refl 32)
  · have hx' : Sep (B + 0x21A0 + 0xFFFFFFC0) 0x40 x 1 := by
      rw [show (0xFFFFFFC0 : Word) = BitVec.ofNat 32 (2 ^ 32 - 0x40) from rfl, sv_spX B 0x40 (by decide)]
      exact svR_spX hx (by decide) (by decide) (by decide)
    rw [f2 x hx']
    exact fillBytes_sep (svR_hi hx hco) (Nat.le_refl 32)

set_option maxHeartbeats 8000000 in
/-- **A call to `bytes2scalar`** for P-256 of the 32 bytes at offset `cb`,
into offset `co`: the big-endian value reduced modulo the order. -/
theorem sv_by2Fs {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {co cb : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (BE : BYEnv M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BY)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cb)
    (hco : co + 32 ≤ 0x1690) (hco4 : co % 4 = 0) (hcb : cb + 32 ≤ 0x1690) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 =
        beNat (memBytes M (B + 0x21A0 + BitVec.ofNat 32 cb) 32) % C3.p256.n ∧
      SvKeepL B M n'.mem [(co, 32)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have e1 : B + 0x21A0 + 0xFFFFFF20 = B + BitVec.ofNat 32 0x20C0 := sv_spX B 0xE0 (by decide)
  obtain ⟨n2, c2, pc2, sp2, k2, A2, f2⟩ := bytes2scalar256_correct n1 (sp0 := B + 0x21A0)
    (out := B + 0x21A0 + BitVec.ofNat 32 co) (b := B + 0x21A0 + BitVec.ofNat 32 cb) (by rw [mem1]; exact BE) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [r1 sp (by decide), rsp])
    (by rw [hS]; omega) (by rw [hS]; omega) (by rw [hS]; unfold dramEnd; omega)
    (by rw [sv_at F _ (by omega)]; unfold dramEnd; omega) (sv_al F (by omega) hco4)
    (by rw [sv_at F _ (by omega)]; omega)
    (by rw [e1, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (by rw [e1, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (by rw [e1]; exact F.bufData (by decide) (by decide) (by decide))
  rw [mem1, e1] at f2
  rw [mem1] at A2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], A2,
    fun e he hL => ?_, fun x hx => f2 x (svR_spX hx (by decide) (by decide) (by decide)) (svR_hi hx hco)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

end C3.RV32.Sv
