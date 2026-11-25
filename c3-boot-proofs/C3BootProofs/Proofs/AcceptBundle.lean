import C3BootProofs.Proofs.AcceptBundleCall

/-!
# `boot_main`'s first closure: the bundle stage

From 0x1816 to the call to `sigstore::verify` at 0x1A46: move the trust root
to `sp + 0x1870`, read the bundle part with a `Reader` at `sp + 0xDD0`
(`Reader::magic`, `Reader::version_1`, and `bundle::field` six times), and
lay the `Bundle` out at `sp + 0x1320` for `sigstore::verify`, with the
image's digest at `sp + 0x108`.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3

/-! ## The frame -/

/-- The memory after the trust root's move and its first five bytes: the
frame as the stage leaves it apart from the slots in `acbV`. -/
def acbMi (M : Word → BitVec 8) (B : Word) : Word → BitVec 8 :=
  memStore8 (memStore32 (copyBytes M (acSlot B 0x1875) (acSlot B 0xDD0) 0x423) (acSlot B 0x1870) 0x3FCC6621)
    (acSlot B 0x1874) 0x2B

theorem acb_ne1 {a x : Word} (h : Sep a 1 x 1) : x ≠ a := fun e =>
  h 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e])

theorem acb_Mi {M : Word → BitVec 8} {B x : Word} (h : AcbOut acbW B x) : acbMi M B x = M x := by
  have h1 : Sep (acSlot B 0x1874) 1 x 1 := acb_sep h (p := (0x52C0, 0x428)) (by decide) (by decide) (by decide)
  have h2 : Sep (acSlot B 0x1870) 4 x 1 := acb_sep h (p := (0x52C0, 0x428)) (by decide) (by decide) (by decide)
  have h3 : Sep (acSlot B 0x1875) 0x423 x 1 :=
    acb_sep h (p := (0x52C0, 0x428)) (by decide) (by decide) (by decide)
  unfold acbMi
  rw [memStore8_ne (acb_ne1 h1), memStore32_get_sep h2, copyBytes_sep h3 (Nat.le_refl _)]

theorem acb_st8 {M M' : Word → BitVec 8} {a x : Word} {v : BitVec 8} (h : M x = M' x) :
    memStore8 M a v x = memStore8 M' a v x := by
  unfold memStore8; split
  · rfl
  · exact h

theorem acb_st32 {M M' : Word → BitVec 8} {a x v : Word} (h : M x = M' x) :
    memStore32 M a v x = memStore32 M' a v x := by
  unfold memStore32; exact acb_st8 (acb_st8 (acb_st8 (acb_st8 h)))

/-- What holds of every state the stage reaches from `n0`. -/
structure AcbK (B : Word) (n0 n : Machine) : Prop where
  sp : reg n sp = B + 0x3A50
  gp : reg n (3 : Fin 32) = reg n0 (3 : Fin 32)
  tp : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)
  keep : ∀ x, AcbOut acbV B x → n.mem x = acbMi n0.mem B x

/-- What the stage keeps of its start `n0`. -/
structure AcbG (B Bf g t r : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (L : Nat) (n0 : Machine) :
    Prop where
  C : CodeIn n0.mem AC bootMainClosure0Code
  E : AcBundleEnv n0.mem
  Y : AcbBuf B Bf L
  I : AcInv B Bf g t v M0 n0
  r : memLoad32 n0.mem (acSlot B 0x40) = r

section G

variable {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {L : Nat} {n0 n : Machine}

theorem AcbK.kw (K : AcbK B n0 n) : ∀ x, AcbOut acbW B x → n.mem x = n0.mem x := fun x hx =>
  (K.keep x (acb_VW hx)).trans (acb_Mi hx)

theorem AcbG.hi (G : AcbG B Bf g t r v M0 L n0) (K : AcbK B n0 n) :
    ∀ x : Word, 0x40000000 ≤ x.toNat → n.mem x = n0.mem x := fun x hx =>
  K.kw x (acb_hi G.Y.fr (by decide) hx)

set_option maxRecDepth 100000 in
theorem AcbG.code (G : AcbG B Bf g t r v M0 L n0) (K : AcbK B n0 n) : CodeIn n.mem AC bootMainClosure0Code :=
  acb_codeHi G.C (by decide) (by decide) (G.hi K)

set_option maxRecDepth 100000 in
theorem AcbG.env (G : AcbG B Bf g t r v M0 L n0) (K : AcbK B n0 n) : AcBundleEnv n.mem :=
  G.E.hi (G.hi K)

theorem AcbG.buf (G : AcbG B Bf g t r v M0 L n0) (K : AcbK B n0 n) {c : Nat} (hc : c + 4 ≤ acBufLen) :
    memLoad32 n.mem (Bf + BitVec.ofNat 32 c) = memLoad32 n0.mem (Bf + BitVec.ofNat 32 c) :=
  acb_ldBuf (K.kw) (by decide) G.Y.hs hc

theorem AcbG.inv (G : AcbG B Bf g t r v M0 L n0) (K : AcbK B n0 n) : AcInv B Bf g t v M0 n where
  sp := K.sp
  gp := K.gp.trans G.I.gp
  tp := K.tp.trans G.I.tp
  saves k hk := by
    refine (acb_ld (K.kw) (c := 0x5A6C - 4 * k) ?_ (by omega) (by decide)).trans (G.I.saves k hk)
    intro p hp
    simp only [acbW, acbV, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  out x h1 h2 := (K.kw x (acb_stack (by decide) h1)).trans (G.I.out x h1 h2)

theorem AcbG.res (G : AcbG B Bf g t r v M0 L n0) (K : AcbK B n0 n) : memLoad32 n.mem (acSlot B 0x40) = r :=
  (acb_ld (K.kw) (c := 0x3A50 + 0x40) (by decide) (by decide) (by decide)).trans G.r

end G

/-- The closure is at the reject exit with a code below 0x27. -/
def AcbEx (n : Machine) : Prop := n.pc = AC + 0x7D6 ∧ (reg n (21 : Fin 32) &&& 0xFF).toNat < 0x27

/-- From `n`, the stage reaches the reject exit, or a state that `P` holds of. -/
def AcbOr (B : Word) (n0 n : Machine) (P : Machine → Prop) : Prop :=
  ∃ n', Steps n n' ∧ AcbK B n0 n' ∧ (AcbEx n' ∨ P n')

theorem acb_bind {B : Word} {n0 n : Machine} {P P' : Machine → Prop} (h : AcbOr B n0 n P)
    (k : ∀ n1, AcbK B n0 n1 → P n1 → AcbOr B n0 n1 P') : AcbOr B n0 n P' := by
  obtain ⟨n1, c1, K1, h1 | h1⟩ := h
  · exact ⟨n1, c1, K1, Or.inl h1⟩
  · obtain ⟨n2, c2, K2, h2⟩ := k n1 K1 h1
    exact ⟨n2, c1.trans c2, K2, h2⟩

theorem acb_ret {B : Word} {n0 n : Machine} {P : Machine → Prop} (K : AcbK B n0 n) (h : P n) : AcbOr B n0 n P :=
  ⟨n, .refl _, K, Or.inr h⟩

theorem acb_stage {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {L : Nat} {n0 : Machine}
    {o' : Nat} {Q : Machine → Prop} (G : AcbG B Bf g t r v M0 L n0)
    (h : AcbOr B n0 n0 (fun n => n.pc = AC + BitVec.ofNat 32 o' ∧ Q n)) :
    AcStage B Bf g t r v M0 n0 o' Q := by
  obtain ⟨n, c, K, ex | ⟨hp, hq⟩⟩ := h
  · exact ⟨n, c, Or.inr ⟨G.inv K, Or.inl (Or.inr (Or.inr (Or.inl ⟨ex.1, G.res K, ex.2⟩)))⟩⟩
  · exact ⟨n, c, Or.inr ⟨G.inv K, Or.inr ⟨hp, hq⟩⟩⟩

theorem acb_x6a {B : Word} {n0 n : Machine} {P : Machine → Prop} (K : AcbK B n0 n)
    (s : St n.mem AC n 0x1A6A (reg n)) (C : CodeIn n.mem AC bootMainClosure0Code)
    (hb : (reg n (8 : Fin 32) &&& 0xFF).toNat < 0x27) : AcbOr B n0 n P := by
  obtain ⟨n', c, pc, mem, rg, r21⟩ := acb_t6a s C
  refine ⟨n', c, ⟨?_, ?_, ?_, fun x hx => by rw [mem]; exact K.keep x hx⟩, Or.inl ⟨pc, by rw [r21]; exact hb⟩⟩
  · rw [rg sp (by decide)]; exact K.sp
  · rw [rg 3 (by decide)]; exact K.gp
  · rw [rg 4 (by decide)]; exact K.tp

theorem acb_x66 {B : Word} {n0 n : Machine} {P : Machine → Prop} (K : AcbK B n0 n)
    (s : St n.mem AC n 0x1A66 (reg n)) (C : CodeIn n.mem AC bootMainClosure0Code)
    (hb : (n.mem (acSlot B 0x354)).toNat < 0x27) : AcbOr B n0 n P := by
  obtain ⟨n', c, pc, mem, rg, r21⟩ := acb_t66 s C K.sp
  refine ⟨n', c, ⟨?_, ?_, ?_, fun x hx => by rw [mem]; exact K.keep x hx⟩,
    Or.inl ⟨pc, by rw [r21, acb_zb]; exact hb⟩⟩
  · rw [rg sp (by decide)]; exact K.sp
  · rw [rg 3 (by decide)]; exact K.gp
  · rw [rg 4 (by decide)]; exact K.tp

theorem acb_spk (B : Word) {k : Word} {c : Nat} (h : (0x3A50 : Word) + k = BitVec.ofNat 32 c) :
    B + 0x3A50 + k = B + BitVec.ofNat 32 c := by
  rw [BitVec.add_assoc, h]

theorem acb_pre {B : Word} {n0 n n' : Machine} {P : Machine → Prop} (c : Steps n n') (h : AcbOr B n0 n' P) :
    AcbOr B n0 n P := by
  obtain ⟨n2, c2, K2, h2⟩ := h
  exact ⟨n2, c.trans c2, K2, h2⟩

/-- `AcbK` survives steps that keep the memory, `sp`, `gp`, and `tp`. -/
theorem AcbK.regs {B : Word} {n0 n n' : Machine} {l : List Nat} (K : AcbK B n0 n) (hm : n'.mem = n.mem)
    (hr : ∀ x : Fin 32, x.val ∉ l → reg n' x = reg n x) (h2 : (2 : Nat) ∉ l := by decide)
    (h3 : (3 : Nat) ∉ l := by decide) (h4 : (4 : Nat) ∉ l := by decide) : AcbK B n0 n' :=
  ⟨by rw [hr (2 : Fin 32) h2]; exact K.sp, by rw [hr 3 h3]; exact K.gp, by rw [hr 4 h4]; exact K.tp,
    fun x hx => by rw [hm]; exact K.keep x hx⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- A call to `bundle::field` at `o`, the load of the result's pointer into
`rd`, and the branch to 0x1A66 when it is zero. -/
theorem acb_fstep {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {L : Nat} {n0 n : Machine}
    (G : AcbG B Bf g t r v M0 L n0) (K : AcbK B n0 n) {o o' q : Nat} {imm off lo hi bimm blen : Word}
    {rd : Fin 32} (s : St n.mem AC n o (reg n)) (R : AcbRd B Bf L q n.mem) (hq : q ≤ L)
    (h1 : fetchRel bootMainClosure0Code o = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (o + 4) = some (.jalr ra ra off, 4))
    (hb : AC + BitVec.ofNat 32 o + imm + off = BitVec.ofNat 32 bundleFieldAddress)
    (hl : (AC + BitVec.ofNat 32 (o + 8)).toNat % 2 = 0)
    (h3 : fetchRel bootMainClosure0Code (o + 8) = some (.load .lw rd sp 0x350, 4))
    (e3 : BitVec.ofNat 32 (o + 8) + 4 = BitVec.ofNat 32 (o + 12))
    (h4 : fetchRel bootMainClosure0Code (o + 12) = some (.branch .beq rd x0 bimm, blen))
    (hT : BitVec.ofNat 32 (o + 12) + bimm = BitVec.ofNat 32 0x1A66)
    (hF : BitVec.ofNat 32 (o + 12) + blen = BitVec.ofNat 32 o')
    (hrd : rd.val ∉ [0, 2, 3, 4])
    (ra0 : reg n a0 = acSlot B 0x350) (ra1 : reg n a1 = acSlot B 0xDD0) (ra2 : reg n a2 = lo)
    (ra3 : reg n a3 = hi) :
    AcbOr B n0 n (fun n' => St n'.mem AC n' o' (reg n') ∧
      (∀ x : Fin 32, x.val ∉ [1, 6, 10, 11, 12, 13, 14, 15] → x ≠ rd → reg n' x = reg n x) ∧
      reg n' rd = Bf + BitVec.ofNat 32 (q + 4) ∧
      memLoad32 n'.mem (acSlot B 0x354) = memLoad32 n0.mem (Bf + BitVec.ofNat 32 q) ∧
      q + 4 + (memLoad32 n0.mem (Bf + BitVec.ofNat 32 q)).toNat ≤ L ∧
      lo.toNat ≤ (memLoad32 n0.mem (Bf + BitVec.ofNat 32 q)).toNat ∧
      (memLoad32 n0.mem (Bf + BitVec.ofNat 32 q)).toNat ≤ hi.toNat ∧
      AcbRd B Bf L (q + 4 + (memLoad32 n0.mem (Bf + BitVec.ofNat 32 q)).toNat) n'.mem ∧
      ∀ x, AcbOut acbFc B x → n'.mem x = n.mem x) := by
  have hL := G.Y.hL
  have hr0 : rd.val ≠ 0 := fun e => hrd (by rw [e]; decide)
  obtain ⟨n1, c1, s1, rg1, fr1, p1, l1, res⟩ :=
    acb_fcall s (G.code K) (G.env K) G.Y R hq h1 h2 hb hl K.sp ra0 ra1 ra2 ra3
  have K1 : AcbK B n0 n1 := ⟨by rw [rg1 sp (by decide)]; exact K.sp, by rw [rg1 3 (by decide)]; exact K.gp,
    by rw [rg1 4 (by decide)]; exact K.tp, fun x hx => (fr1 x (acb_FcV hx)).trans (K.keep x hx)⟩
  have C1 := G.code K1
  have eA : B + 0x3A50 + 0x350 = acSlot B 0x350 := acb_spk B (by decide)
  obtain ⟨n2, e2, s2⟩ := s1.self.lw C1 h3 e3 (by rw [K1.sp, eA]; exact acb_al G.Y.fr _ (by decide) (by decide))
  rw [K1.sp, eA] at s2
  have rg2 : ∀ x : Fin 32, x ≠ rd → reg n2 x = reg n1 x := fun x hx => by rw [s2.regs, updz s1.zero hx]
  have K2 : AcbK B n0 n2 := ⟨by rw [rg2 sp (acb_ne hrd).symm]; exact K1.sp,
    by rw [rg2 3 (acb_ne hrd).symm]; exact K1.gp, by rw [rg2 4 (acb_ne hrd).symm]; exact K1.tp,
    fun x hx => by rw [s2.mem]; exact K1.keep x hx⟩
  have vrd : reg n2 rd = memLoad32 n1.mem (acSlot B 0x350) := by rw [s2.regs, upd_same hr0]
  rcases res with ⟨f0, f4⟩ | ⟨g1, g2, g3, g4, g5, g6⟩
  · obtain ⟨n3, e3', s3⟩ := s2.taken C1 0x1A66 h4 hT (by rw [upd_same hr0, f0]; rfl)
    have K3 : AcbK B n0 n3 := K2.regs (l := []) (by rw [s3.mem, s2.mem]) (fun x _ => by rw [s3.regs, s2.regs])
    refine acb_pre c1 (acb_pre (.cons e2 (.cons e3' (.refl _))) ?_)
    exact acb_x66 K3 ⟨s3.pc, rfl, fun _ => rfl⟩ (G.code K3) (by rw [s3.mem]; exact f4)
  · have hne : Bf + BitVec.ofNat 32 (q + 4) ≠ 0 := (G.Y.sv.sub (c := q + 4) (l := 0) (by omega)).pos_ne
    have hbuf : memLoad32 n.mem (Bf + BitVec.ofNat 32 q) = memLoad32 n0.mem (Bf + BitVec.ofNat 32 q) :=
      G.buf K (by unfold acBufLen; omega)
    rw [hbuf] at g1 g2 g3 g5 g6
    obtain ⟨n3, e3', s3⟩ := s2.notTaken C1 o' h4 hF (by
      rw [upd_same hr0, g4]; simp only [branchTaken, x0, upd_zero]; exact beq_eq_false_iff_ne.mpr hne)
    have K3 : AcbK B n0 n3 := K2.regs (l := []) (by rw [s3.mem, s2.mem]) (fun x _ => by rw [s3.regs, s2.regs])
    refine acb_pre c1 (acb_pre (.cons e2 (.cons e3' (.refl _))) (acb_ret K3 ⟨⟨s3.pc, rfl, fun _ => rfl⟩,
      fun x hx hxr => by rw [s3.regs, updz s1.zero hxr, rg1 x hx], by rw [s3.regs, upd_same hr0, g4],
      by rw [s3.mem]; exact g5, g1, g2, g3,
      ⟨by rw [s3.mem]; exact p1, by rw [s3.mem]; exact l1, by rw [s3.mem]; exact g6⟩,
      fun x hx => by rw [s3.mem]; exact fr1 x hx⟩))

set_option maxRecDepth 100000 in
/-- After `Reader::magic` or `Reader::version_1`: `s0 := a0`, then the branch
to 0x1A6A unless the low byte of `a0` is 0xFF. -/
theorem acb_chk {B : Word} {n0 n : Machine} {o o1 o2 o3 o4 : Nat} {bimm c : Word} {P : Prop}
    (K : AcbK B n0 n) (s : St n.mem AC n o (reg n)) (C : CodeIn n.mem AC bootMainClosure0Code)
    (h1 : fetchRel bootMainClosure0Code o = some (.alu .add (8 : Fin 32) x0 a0, 2))
    (h2 : fetchRel bootMainClosure0Code o1 = some (.aluImm .and a0 a0 0xFF, 4))
    (h3 : fetchRel bootMainClosure0Code o2 = some (.aluImm .add a0 a0 0xFFFFFF01, 4))
    (h4 : fetchRel bootMainClosure0Code o3 = some (.branch .bne a0 x0 bimm, 4))
    (e1 : BitVec.ofNat 32 o + 2 = BitVec.ofNat 32 o1) (e2 : BitVec.ofNat 32 o1 + 4 = BitVec.ofNat 32 o2)
    (e3 : BitVec.ofNat 32 o2 + 4 = BitVec.ofNat 32 o3) (eT : BitVec.ofNat 32 o3 + bimm = BitVec.ofNat 32 0x1A6A)
    (eF : BitVec.ofNat 32 o3 + 4 = BitVec.ofNat 32 o4) (hc : c = 2 ∨ c = 3)
    (ha : reg n a0 = 0 ∨ reg n a0 = c ∨ (reg n a0 = 0xFFFFFFFF ∧ P)) :
    AcbOr B n0 n (fun n' => St n'.mem AC n' o4 (reg n') ∧ n'.mem = n.mem ∧
      (∀ x : Fin 32, x.val ∉ [8, 10] → reg n' x = reg n x) ∧ P) := by
  have hz := s.zero
  obtain ⟨m1, c1, s1⟩ := s.alu C h1 e1
  obtain ⟨m2, c2, s2⟩ := s1.aluImm C h2 e2
  obtain ⟨m3, c3, s3⟩ := s2.aluImm C h3 e3
  have r10 : (upd (upd (upd (reg n) 8 (aluEval .add (reg n x0) (reg n a0))) a0
      (aluEval .and (upd (reg n) 8 (aluEval .add (reg n x0) (reg n a0)) a0) 0xFF)) a0
      (aluEval .add (upd (upd (reg n) 8 (aluEval .add (reg n x0) (reg n a0))) a0
        (aluEval .and (upd (reg n) 8 (aluEval .add (reg n x0) (reg n a0)) a0) 0xFF) a0) 0xFFFFFF01)) a0 =
      (reg n a0 &&& 0xFF) + 0xFFFFFF01 := by
    simp +decide only [upd, ↓reduceIte, aluEval]
  have r8 : (upd (upd (upd (reg n) 8 (aluEval .add (reg n x0) (reg n a0))) a0
      (aluEval .and (upd (reg n) 8 (aluEval .add (reg n x0) (reg n a0)) a0) 0xFF)) a0
      (aluEval .add (upd (upd (reg n) 8 (aluEval .add (reg n x0) (reg n a0))) a0
        (aluEval .and (upd (reg n) 8 (aluEval .add (reg n x0) (reg n a0)) a0) 0xFF) a0) 0xFFFFFF01))
      (8 : Fin 32) = reg n a0 := by
    simp +decide only [upd, ↓reduceIte, aluEval]; exact BitVec.zero_add _
  have rk : ∀ x : Fin 32, x.val ∉ [8, 10] → reg m3 x = reg n x := fun x hx => by
    rw [s3.regs, updz (upd_zero _ _ _) (acb_ne hx), updz (upd_zero _ _ _) (acb_ne hx), updz hz (acb_ne hx)]
  have hm : m3.mem = n.mem := s3.mem
  have K3 : AcbK B n0 m3 := K.regs hm rk
  have C3 : CodeIn m3.mem AC bootMainClosure0Code := by rw [hm]; exact C
  have taken : ∀ w : Word, reg n a0 = w → (w &&& 0xFF) + 0xFFFFFF01 ≠ 0 → (w &&& 0xFF).toNat < 0x27 →
      AcbOr B n0 n (fun n' => St n'.mem AC n' o4 (reg n') ∧ n'.mem = n.mem ∧
        (∀ x : Fin 32, x.val ∉ [8, 10] → reg n' x = reg n x) ∧ P) := fun w hw hne hlt => by
    obtain ⟨m4, c4, s4⟩ := s3.taken C 0x1A6A h4 eT (by
      rw [r10, hw]; simp only [branchTaken, x0, upd_zero]; exact bne_iff_ne.mpr hne)
    have K4 : AcbK B n0 m4 := K3.regs (l := []) (by rw [s4.mem, hm]) (fun x _ => by rw [s4.regs, s3.regs])
    refine acb_pre (.cons c1 (.cons c2 (.cons c3 (.cons c4 (.refl _))))) ?_
    exact acb_x6a K4 ⟨s4.pc, by rw [s4.mem], fun _ => rfl⟩ (by rw [s4.mem]; exact C)
      (by rw [s4.regs, r8, hw]; exact hlt)
  rcases ha with h0 | hc' | ⟨hf, hp⟩
  · exact taken 0 h0 (by decide) (by decide)
  · rcases hc with rfl | rfl
    · exact taken 2 hc' (by decide) (by decide)
    · exact taken 3 hc' (by decide) (by decide)
  · obtain ⟨m4, c4, s4⟩ := s3.notTaken C o4 h4 eF (by
      rw [r10, hf]; simp only [branchTaken, x0, upd_zero]; decide)
    have K4 : AcbK B n0 m4 := K3.regs (l := []) (by rw [s4.mem, hm]) (fun x _ => by rw [s4.regs, s3.regs])
    refine acb_pre (.cons c1 (.cons c2 (.cons c3 (.cons c4 (.refl _))))) (acb_ret K4 ⟨⟨s4.pc, rfl, fun _ => rfl⟩,
      by rw [s4.mem], fun x hx => by rw [s4.regs, ← rk x hx, s3.regs], hp⟩)

/-- From the copy of the root's keys to the call of `Reader::magic`. -/
def acbI : List BInstr :=
  [.lui a0 0x3FCC6000, .aluImm .add a0 a0 0x621, .aluImm .add a1 x0 0x2B, .lui a2 0x1000,
   .aluImm .add a2 a2 0x310, .alu .add a2 a2 sp, .sw a2 a0 0x560, .sb a2 a1 0x564, .aluImm .add a0 sp 0x7FF,
   .aluImm .add a0 a0 0x91, .lw a1 sp 0x34, .sw a0 a1 0x540, .lw a1 sp 0x38, .sw a0 a1 0x544, .sw a0 x0 0x548,
   .lui a1 0x4E423000, .aluImm .add a1 a1 0x343, .aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x5D1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem acbI_end : blockEnd bootMainClosure0Code 0x181A acbI = some 0x185E := by decide

/-- What the stage needs at 0x1816: the bundle part's pointer and length at
`sp + 0x34` and `sp + 0x38`, and the arguments of the copy of the root's
keys. -/
structure AcBundlePre (B Bf : Word) (L : Nat) (n : Machine) : Prop where
  bf : memLoad32 n.mem (acSlot B 0x34) = Bf
  len : memLoad32 n.mem (acSlot B 0x38) = BitVec.ofNat 32 L
  hL : L ≤ 0x4000
  sv : Sv.SvIn (B + 0x13F0) Bf 0x4000
  a0 : reg n a0 = acSlot B 0x1875
  a1 : reg n a1 = acSlot B 0xDD0
  a2 : reg n a2 = 0x423
  ra : reg n ra = AC + BitVec.ofNat 32 0x1812 + 0x15000

theorem acb_cm (k B : Word) (c : Nat) : k + (B + BitVec.ofNat 32 c) = B + BitVec.ofNat 32 c + k :=
  BitVec.add_comm _ _

theorem acb_lst {M : Word → BitVec 8} {B v : Word} {c d : Nat} (h : c + 4 ≤ d ∨ d + 4 ≤ c)
    (hc : c + 4 ≤ 2 ^ 32) (hd : d + 4 ≤ 2 ^ 32) :
    memLoad32 (memStore32 M (B + BitVec.ofNat 32 c) v) (B + BitVec.ofNat 32 d) =
      memLoad32 M (B + BitVec.ofNat 32 d) :=
  memLoad32_store32_sep (sep_offsets B h hc hd)

theorem acb_lsb {M : Word → BitVec 8} {B : Word} {v : BitVec 8} {c d : Nat} (h : c + 1 ≤ d ∨ d + 4 ≤ c)
    (hc : c + 1 ≤ 2 ^ 32) (hd : d + 4 ≤ 2 ^ 32) :
    memLoad32 (memStore8 M (B + BitVec.ofNat 32 c) v) (B + BitVec.ofNat 32 d) =
      memLoad32 M (B + BitVec.ofNat 32 d) :=
  memLoad32_store8_sep (sep_offsets B h hc hd)

theorem acb_ldC {M M' : Word → BitVec 8} {B : Word}
    (h : ∀ x, Sep (B + BitVec.ofNat 32 0x3A40) 16 x 1 →
      M' x = copyBytes M (acSlot B 0x1875) (acSlot B 0xDD0) 0x423 x)
    {c : Nat} (h1 : 0x3A50 ≤ c) (h2 : c + 4 ≤ 0x52C5) :
    memLoad32 M' (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc, h _ (sep_offsets B (by omega) (by decide) (by omega)),
      copyBytes_sep (sep_offsets B (n := 0x423) (c := 0x3A50 + 0x1875) (by omega) (by decide) (by omega))
        (Nat.le_refl _)]

theorem acb_hiC {M M' : Word → BitVec 8} {B : Word} (F : Fr B 0x5A70)
    (h : ∀ x, Sep (B + BitVec.ofNat 32 0x3A40) 16 x 1 →
      M' x = copyBytes M (acSlot B 0x1875) (acSlot B 0xDD0) 0x423 x) :
    ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x := fun x hx => by
  rw [h x (F.hiOut (by decide) hx), copyBytes_sep (F.hiOut (c := 0x3A50 + 0x1875) (by decide) hx) (Nat.le_refl _)]

set_option hygiene false in
/-- Closes a block's alignment and code-separation conditions in the frame `F`. -/
macro "acb_ok" : tactic => `(tactic| all_goals first
  | exact acb_al F _ (by decide) (by decide)
  | exact acb_stackCode F (by decide) (by decide) (by decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- From 0x1816 to the call of `Reader::magic`: copy the root's keys, store
the root's header, and set up the reader over the bundle part. -/
theorem acb_init {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {L : Nat} {n0 : Machine}
    (G : AcbG B Bf g t r v M0 L n0) (s : St n0.mem AC n0 0x1816 (reg n0)) (P : AcBundlePre B Bf L n0) :
    ∃ n, Steps n0 n ∧ AcbK B n0 n ∧ St n.mem AC n 0x185E (reg n) ∧ reg n a0 = acSlot B 0xDD0 ∧
      reg n a1 = 0x4E423343 ∧ AcbRd B Bf L 0 n.mem := by
  have F := G.Y.fr
  obtain ⟨n1, c1, s1, rg1, mem1⟩ := acb_cpy s G.C G.E F G.I.sp P.a0 P.a1 P.a2 P.ra
  have rsp1 : reg n1 sp = B + BitVec.ofNat 32 0x3A50 := by rw [rg1 sp (by decide)]; exact G.I.sp
  have hz := s1.zero
  have C1 : CodeIn n1.mem AC bootMainClosure0Code := acb_codeHi G.C (by decide) (by decide) (acb_hiC F mem1)
  obtain ⟨n2, c2, u2⟩ := s1.block acbI C1 acbI_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acbI]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp1]
    simp (disch := decide) only [aluEval, acb_cm, Dq.frame_lit, BitVec.reduceToNat, Nat.reduceAdd,
      BitVec.reduceAdd]
    repeat' apply And.intro
    acb_ok)
  have hb : memLoad32 n1.mem (B + BitVec.ofNat 32 0x3A84) = Bf :=
    (acb_ldC mem1 (by decide) (by decide)).trans P.bf
  have hl : memLoad32 n1.mem (B + BitVec.ofNat 32 0x3A88) = BitVec.ofNat 32 L :=
    (acb_ldC mem1 (by decide) (by decide)).trans P.len
  have m2 : n2.mem = memStore32 (memStore32 (memStore32 (memStore8 (memStore32 n1.mem (acSlot B 0x1870)
      0x3FCC6621) (acSlot B 0x1874) 0x2B) (acSlot B 0xDD0) Bf) (acSlot B 0xDD4) (BitVec.ofNat 32 L))
      (acSlot B 0xDD8) 0 := by
    rw [u2.mem]; simp only [runBlock, BInstr.run, acbI]; simp +decide only [upd, ↓reduceIte]; rw [rsp1]
    simp (disch := decide) only [acSlot, aluEval, acb_cm, Dq.frame_lit, BitVec.reduceToNat, Nat.reduceAdd,
      BitVec.reduceAdd, acb_lst, acb_lsb, hb, hl]
    rfl
  have g : ∀ q, reg n2 q = (runBlock acbI (n1.mem, reg n1)).2 q := fun q => by rw [u2.regs]
  have rk : ∀ q : Fin 32, q.val ∈ [2, 3, 4] → reg n2 q = reg n1 q := fun q hq => by
    rw [g, runBlock_reg _ _ _ q hz (by simp only [acbI]; revert hq; revert q; decide)]
  have K2 : AcbK B n0 n2 := ⟨by rw [rk sp (by decide)]; exact rsp1, by rw [rk 3 (by decide), rg1 3 (by decide)],
    by rw [rk 4 (by decide), rg1 4 (by decide)], fun x hx => by
      rw [m2, memStore32_get_sep (a := acSlot B 0xDD8) (acb_sep hx (p := (0x4820, 0xC)) (by decide) (by decide) (by decide)),
        memStore32_get_sep (a := acSlot B 0xDD4) (acb_sep hx (p := (0x4820, 0xC)) (by decide) (by decide) (by decide)),
        memStore32_get_sep (a := acSlot B 0xDD0) (acb_sep hx (p := (0x4820, 0xC)) (by decide) (by decide) (by decide))]
      unfold acbMi
      exact acb_st8 (acb_st32 (mem1 x (acb_sep hx (p := (0, 0x3A50)) (by decide) (by decide) (by decide))))⟩
  refine ⟨n2, c1.trans c2, K2, ⟨u2.pc, rfl, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g]; simp +decide only [runBlock, BInstr.run, acbI, upd, ↓reduceIte]; rw [rsp1]
    simp (disch := decide) only [acSlot, aluEval, Dq.frame_lit, BitVec.reduceToNat, Nat.reduceAdd]
  · rw [g]; simp +decide only [runBlock, BInstr.run, acbI, upd, ↓reduceIte, aluEval]
  · rw [m2]; simp (disch := decide) only [acSlot, Nat.reduceAdd, acb_lst, memLoad32_store32_same]
  · rw [m2]; simp (disch := decide) only [acSlot, Nat.reduceAdd, acb_lst, memLoad32_store32_same]
  · rw [m2]; simp (disch := decide) only [acSlot, Nat.reduceAdd, memLoad32_store32_same]; rfl

/-- `AcbK` survives a call that keeps `sp`, `gp`, and `tp`, and the memory
outside `acbFc`. -/
theorem AcbK.call {B : Word} {n0 n n' : Machine} {l : List Nat} (K : AcbK B n0 n)
    (hr : ∀ x : Fin 32, x.val ∉ l → reg n' x = reg n x) (hf : ∀ x, AcbOut acbFc B x → n'.mem x = n.mem x)
    (h2 : (2 : Nat) ∉ l := by decide) (h3 : (3 : Nat) ∉ l := by decide) (h4 : (4 : Nat) ∉ l := by decide) :
    AcbK B n0 n' :=
  ⟨by rw [hr (2 : Fin 32) h2]; exact K.sp, by rw [hr 3 h3]; exact K.gp, by rw [hr 4 h4]; exact K.tp,
    fun x hx => (hf x (acb_FcV hx)).trans (K.keep x hx)⟩

theorem acb_dd0 (B : Word) : B + 0x3A50 + 0x7FF + 0x5D1 = acSlot B 0xDD0 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

/-- Two steps that set `a0` to `sp + 0x7FF + 0x5D1`, the reader. -/
theorem acb_rdr {B : Word} {n0 n : Machine} {o : Nat} (K : AcbK B n0 n) (s : St n.mem AC n o (reg n))
    (C : CodeIn n.mem AC bootMainClosure0Code)
    (h1 : fetchRel bootMainClosure0Code o = some (.aluImm .add a0 sp 0x7FF, 4))
    (h2 : fetchRel bootMainClosure0Code (o + 4) = some (.aluImm .add a0 a0 0x5D1, 4))
    (e1 : BitVec.ofNat 32 o + 4 = BitVec.ofNat 32 (o + 4))
    (e2 : BitVec.ofNat 32 (o + 4) + 4 = BitVec.ofNat 32 (o + 8)) :
    ∃ n', Steps n n' ∧ AcbK B n0 n' ∧ St n'.mem AC n' (o + 8) (reg n') ∧ n'.mem = n.mem ∧
      reg n' a0 = acSlot B 0xDD0 ∧ ∀ x : Fin 32, x ≠ a0 → reg n' x = reg n x := by
  have hz := s.zero
  obtain ⟨m1, c1, s1⟩ := s.aluImm C h1 e1
  obtain ⟨m2, c2, s2⟩ := s1.aluImm C h2 e2
  have rk : ∀ x : Fin 32, x ≠ a0 → reg m2 x = reg n x := fun x hx => by
    rw [s2.regs, updz (upd_zero _ _ _) hx, updz hz hx]
  refine ⟨m2, .cons c1 (.cons c2 (.refl _)), K.regs (l := [10]) s2.mem (fun x hx => rk x (acb_ne hx)),
    ⟨s2.pc, rfl, fun _ => rfl⟩, s2.mem, ?_, rk⟩
  rw [s2.regs]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [K.sp, acb_dd0]

set_option maxRecDepth 100000 in
/-- From the call of `Reader::magic` to the first field: the magic and the
version. -/
theorem acb_hdr {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {L : Nat} {n0 n : Machine}
    (G : AcbG B Bf g t r v M0 L n0) (K : AcbK B n0 n) (s : St n.mem AC n 0x185E (reg n))
    (ra0 : reg n a0 = acSlot B 0xDD0) (ra1 : reg n a1 = 0x4E423343) (R : AcbRd B Bf L 0 n.mem) :
    AcbOr B n0 n (fun n' => St n'.mem AC n' 0x1892 (reg n') ∧ AcbRd B Bf L 6 n'.mem ∧ 6 ≤ L ∧
      memLoad32 n0.mem Bf = 0x4E423343 ∧ (n0.mem (Bf + 4)).toNat + 256 * (n0.mem (Bf + 4 + 1)).toNat = 1) := by
  obtain ⟨n1, c1, s1, rg1, fr1, res1⟩ :=
    acb_mcall s (G.code K) (G.env K) G.Y R ac_at_185e ac_at_1862 (by decide) (by decide) K.sp ra0 ra1
  have K1 : AcbK B n0 n1 := K.call rg1 fr1
  refine acb_pre c1 (acb_bind (acb_chk (o4 := 0x1874) K1 s1 (G.code K1) ac_at_1866 ac_at_1868 ac_at_186c ac_at_1870
    (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl rfl) res1) ?_)
  rintro n2 K2 ⟨s2, m2, -, h4L, hmag, R4⟩
  obtain ⟨n3, c3, K3, s3, m3, ra3, -⟩ := acb_rdr K2 s2 (G.code K2) ac_at_1874 ac_at_1878 (by decide) (by decide)
  have R3 : AcbRd B Bf L 4 n3.mem := by rw [m3, m2]; exact R4
  obtain ⟨n4, c4, s4, rg4, fr4, res4⟩ :=
    acb_vcall s3 (G.code K3) (G.env K3) G.Y R3 ac_at_187c ac_at_1880 (by decide) (by decide) K3.sp ra3
  have K4 : AcbK B n0 n4 := K3.call rg4 fr4
  refine acb_pre c3 (acb_pre c4 (acb_bind (acb_chk (o4 := 0x1892) K4 s4 (G.code K4) ac_at_1884 ac_at_1886 ac_at_188a
    ac_at_188e (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inr rfl) res4) ?_))
  rintro n5 K5 ⟨s5, m5, -, h6L, hver, R6⟩
  have e5 : Bf + 4 + 1 = Bf + BitVec.ofNat 32 5 := add_ofNat_assoc _ _ _
  have v4 : n3.mem (Bf + 4) = n0.mem (Bf + 4) := K3.kw _ (acb_buf (by decide) G.Y.hs (j := 4) (by decide))
  have v5 : n3.mem (Bf + 4 + 1) = n0.mem (Bf + 4 + 1) := by
    rw [e5]; exact K3.kw _ (acb_buf (by decide) G.Y.hs (by decide))
  have hm : memLoad32 n.mem Bf = memLoad32 n0.mem Bf := by
    have := G.buf K (c := 0) (by decide); rwa [add_ofNat_zero] at this
  refine acb_ret K5 ⟨s5, by rw [m5]; exact R6, h6L, by rw [← hm]; exact hmag, by rw [← v4, ← v5]; exact hver⟩

#exit

end C3.RV32.Ac
