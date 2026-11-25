import C3BootProofs.Proofs.AcceptTargetsDoc
import C3BootProofs.Proofs.DerOid

/-!
# The digest string

From 0xA94: the `sha256` value must be a string. Its 64 hex digits are
copied to `sp + 0x351` when the string is 0x42 bytes, and `s1` is zero
exactly then. Then `act_b10` reads `trusted_root.json`.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.Json

set_option maxRecDepth 200000

theorem act_q34 : ∀ b : BitVec 8, (BitVec.zeroExtend 32 b + 0xFFFFFFDE == 0) = true → b.toNat = 34 := by
  decide

theorem act_a0 {B : Word} {f : Fin 32 → Word} (h : f sp = B + 0x3A50) (a k : Word) (c : Nat)
    (hc : (0x3A50 + (a + k).toNat) % 2 ^ 32 = c) : a + f sp + k = B + BitVec.ofNat 32 c := by
  rw [BitVec.add_comm a, BitVec.add_assoc]; exact act_spc h _ c hc

section
variable {romBase : Word} {romCode : List Nat} {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8}
  {M : Word → BitVec 8} {f : Fin 32 → Word}

theorem act_succ {w : Word} (h : w + 1 ≠ 0) : (w + 1).toNat = w.toNat + 1 := by
  have hw := w.isLt
  rcases Nat.lt_or_ge (w.toNat + 1) (2 ^ 32) with h1 | h1
  · rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h1
  · exfalso; apply h; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, show w.toNat = 2 ^ 32 - 1 by omega]; rfl

theorem act_uge {l : Nat} (h : (!(BitVec.ofNat 32 l).ult 2) = true) (hl : l < 2 ^ 32) : 2 ≤ l := by
  rw [Bool.not_eq_true'] at h
  simp only [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat] at h
  have : (2 : Word).toNat = 2 := rfl
  omega

theorem act_l42 {l : Nat} (h : BitVec.ofNat 32 l + 0xFFFFFFBE = 0) (hl : l < 2 ^ 32) : l = 0x42 := by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have h1 : (0xFFFFFFBE : Word).toNat = 0xFFFFFFBE := rfl
  have h2 : (0 : Word).toNat = 0 := rfl
  omega

theorem act_last {q : Word} {l : Nat} (h : 1 ≤ l) (hl : l < 2 ^ 32) :
    q + BitVec.ofNat 32 l + 0xFFFFFFFF = q + BitVec.ofNat 32 (l - 1) := by
  rw [BitVec.add_assoc]
  refine congrArg (q + ·) (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  show (l % 2 ^ 32 + 4294967295) % 2 ^ 32 = (l - 1) % 2 ^ 32
  omega

theorem act_zb : ∀ b : BitVec 8, b.toNat < 0x27 → (BitVec.zeroExtend 32 b &&& 0xFF).toNat < 0x27 := by decide

/-- **From 0xAF4**: `i + 1`, with `Overflow` (6) when `i` is the last
`u32`, then `act_b10`. -/
theorem act_af4 {flash : Nat → BitVec 8} {R : Nat} (hROM : RomRead flash R romBase romCode)
    (hR4 : R % 4 = 0) (hR : R ≤ 0x3A50 - 0x180)
    (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f)
    (hr : memLoad32 M (acSlot B 0x40) = r) {pinned : Bytes} {parts : TufParts} {root : TufRoot} {re te : Nat}
    {x21 x25 x27 : Word} {Mi : Word → BitVec 8} {hiW loW : Word} {val : Nat} {body : Bytes}
    (hO : ∀ x, ActOut B Bf x → M x = Mi x)
    (h18 : memLoad32 M (acSlot B 0x18) = hiW) (h14 : memLoad32 M (acSlot B 0x14) = loW)
    (hval : hiW.toNat * 2 ^ 32 + loW.toNat = val)
    (hdoc : ActDoc flash M (acSlot B 0x244) (f 24) ((memLoad32 M (acSlot B 0x1C)).toNat + 1) parts.trustedRoot)
    (hs4 : f 20 = Bf + 0x4000)
    (hbody : f 9 = 0 → memBytes M (acSlot B 0x351) 64 = body)
    (hspec : val = parts.trustedRoot.length → body = hexBytes (sha256 parts.trustedRoot) →
      verifyTuf pinned parts = some (root.version, min re te))
    (h20 : memLoad32 M (acSlot B 0x20) = BitVec.ofNat 32 te)
    (h24 : memLoad32 M (acSlot B 0x24) = BitVec.ofNat 32 (te / 2 ^ 32))
    (h28 : memLoad32 M (acSlot B 0x28) = BitVec.ofNat 32 re)
    (h2C : memLoad32 M (acSlot B 0x2C) = BitVec.ofNat 32 (re / 2 ^ 32))
    (hs3 : f 19 = acSlot B 0x890) (hs6 : f 22 = acSlot B 0x1310)
    (hs5 : f 21 = x21) (hs9 : f 25 = x25) (hs11 : f 27 = x27) :
    WP bootMainClosure0Code AC (actQ B Bf g t r v M0 (AcTargetsPost pinned parts root re B Bf x21 x25 x27 Mi))
      M 0xAF4 f := by
  have F := X.F
  refine WP.zero fun hz => ?_
  have e1c : f sp + 0x1C = acSlot B 0x1C := act_spc hI.rsp _ _ rfl
  refine WP.lw ac_at_af4 (by rw [e1c]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.aluImm ac_at_af6 ?_; wn
  refine WP.branch ac_at_af8 (fun hb => ?_) (fun _ => ?_)
  · wn
    have hne : memLoad32 M (acSlot B 0x1C) + 1 ≠ 0 := by
      revert hb; act_r; rw [e1c]; simp only [branchTaken]; intro hb e; rw [e] at hb; exact absurd hb (by decide)
    refine act_b10 hROM hR4 hR X (hI.regs (by act_r) (by act_r) (by act_r)) hr hO h18 h14 hval
      (by act_r; rw [e1c, act_succ hne]; exact hdoc) (by act_r; exact hs4) (by act_r; exact hbody) hspec
      h20 h24 h28 h2C (by act_r; exact hs3) (by act_r; exact hs6) (by act_r; exact hs5) (by act_r; exact hs9)
      (by act_r; exact hs11)
  · wn
    refine WP.aluImm ac_at_afa ?_; wn
    refine WP.jal ac_at_afc (by decide) ?_; wn
    exact act_x6a (hI.regs (by act_r) (by act_r) (by act_r)) hr (by act_r <;> decide)

theorem act_a94 {flash : Nat → BitVec 8} {R : Nat} (hROM : RomRead flash R romBase romCode)
    (hR4 : R % 4 = 0) (hR : R ≤ 0x3A50 - 0x180)
    (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f)
    (hr : memLoad32 M (acSlot B 0x40) = r) {pinned : Bytes} {parts : TufParts} {root : TufRoot} {re te : Nat}
    {x21 x25 x27 : Word} {Mi : Word → BitVec 8} {hiW loW : Word} {val : Nat} {q : Word} {l : Nat}
    (hO : ∀ x, ActOut B Bf x → M x = Mi x)
    (h18 : memLoad32 M (acSlot B 0x18) = hiW) (h14 : memLoad32 M (acSlot B 0x14) = loW)
    (hval : hiW.toNat * 2 ^ 32 + loW.toNat = val)
    (hdoc : ActDoc flash M (acSlot B 0x244) (f 24) ((memLoad32 M (acSlot B 0x1C)).toNat + 1) parts.trustedRoot)
    (hs4 : f 20 = Bf + 0x4000)
    (hfs : (memLoad32 M (acSlot B 0x1ED0) = 0 ∧ (M (acSlot B 0x1ED4)).toNat < 0x27) ∨
      (memLoad32 M (acSlot B 0x1ED0) = q ∧ memLoad32 M (acSlot B 0x1ED4) = BitVec.ofNat 32 l ∧
        Bf.toNat + 0x4000 ≤ q.toNat ∧ q.toNat + l ≤ Bf.toNat + 0x6800))
    (hspec : ∀ body, strBody (memBytes M q l) = some body → val = parts.trustedRoot.length →
      body = hexBytes (sha256 parts.trustedRoot) → verifyTuf pinned parts = some (root.version, min re te))
    (h20 : memLoad32 M (acSlot B 0x20) = BitVec.ofNat 32 te)
    (h24 : memLoad32 M (acSlot B 0x24) = BitVec.ofNat 32 (te / 2 ^ 32))
    (h28 : memLoad32 M (acSlot B 0x28) = BitVec.ofNat 32 re)
    (h2C : memLoad32 M (acSlot B 0x2C) = BitVec.ofNat 32 (re / 2 ^ 32))
    (hs3 : f 19 = acSlot B 0x890) (hs6 : f 22 = acSlot B 0x1310)
    (hs5 : f 21 = x21) (hs9 : f 25 = x25) (hs11 : f 27 = x27) :
    WP bootMainClosure0Code AC (actQ B Bf g t r v M0 (AcTargetsPost pinned parts root re B Bf x21 x25 x27 Mi))
      M 0xA94 f := by
  have F := X.F
  refine WP.zero fun hz => ?_
  refine WP.lui ac_at_a94 ?_; wn
  refine WP.aluImm ac_at_a96 ?_; wn
  refine WP.alu ac_at_a9a ?_; wn
  have e0 : (8192 + 4294966704 + f sp + 288 : Word) = acSlot B 0x1ED0 := act_a0 hI.rsp _ _ _ rfl
  have e4 : (8192 + 4294966704 + f sp + 292 : Word) = acSlot B 0x1ED4 := act_a0 hI.rsp _ _ _ rfl
  refine WP.lw ac_at_a9c (by act_r; rw [e0]; exact X.al (by decide) (by decide)) ?_; wn
  rcases hfs with ⟨hp0, he⟩ | ⟨hpq, hpl, hq1, hq2⟩
  · refine WP.branch ac_at_aa0 (fun _ => ?_) (fun hb => ?_)
    · wn
      refine WP.lui ac_at_b00 ?_; wn
      refine WP.aluImm ac_at_b02 ?_; wn
      refine WP.alu ac_at_b06 ?_; wn
      refine WP.lbu ac_at_b08 ?_; wn
      refine WP.jal ac_at_b0c (by decide) ?_; wn
      exact act_x6a (hI.regs (by act_r) (by act_r) (by act_r)) hr (by act_r; rw [e4]; exact act_zb _ he)
    · exfalso; revert hb; act_r; rw [e0, hp0]; decide
  have hq0 : q ≠ 0 := fun e => by rw [e] at hq1; simp at hq1
  have hbh := X.bhi
  have hbl : acBufLen = 0xB954 := rfl
  refine WP.branch ac_at_aa0 (fun hb => ?_) (fun _ => ?_)
  · exfalso; revert hb; act_r; rw [e0, hpq]; simp only [branchTaken]; intro hb; exact hq0 (beq_iff_eq.mp hb)
  wn
  refine WP.lui ac_at_aa2 ?_; wn
  refine WP.aluImm ac_at_aa4 ?_; wn
  refine WP.alu ac_at_aa8 ?_; wn
  refine WP.lw ac_at_aaa (by act_r; rw [e4]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.aluImm ac_at_aae ?_; wn
  refine WP.aluImm ac_at_ab0 ?_; wn
  have hl32 : l < 2 ^ 32 := by omega
  refine WP.branch ac_at_ab4 (fun hb => ?_) (fun _ => ?_)
  rotate_left
  · wn; refine WP.jal ac_at_ab8 (by decide) ?_; wn
    exact act_x6a (hI.regs (by act_r) (by act_r) (by act_r)) hr (by act_r <;> decide)
  wn
  have hl2 : 2 ≤ l := by
    revert hb; act_r; rw [e4, hpl]; simp only [branchTaken]; exact fun h => act_uge h hl32
  refine WP.lbu ac_at_abc ?_; wn
  refine WP.aluImm ac_at_ac0 ?_; wn
  refine WP.branch ac_at_ac4 (fun hb => ?_) (fun _ => ?_)
  rotate_left
  · wn; refine WP.jal ac_at_ac6 (by decide) ?_; wn
    exact act_x6a (hI.regs (by act_r) (by act_r) (by act_r)) hr (by act_r <;> decide)
  wn
  have hc0 : (M q).toNat = 34 := by
    revert hb; act_r; rw [e0, hpq, act_z0]; simp only [branchTaken]; exact act_q34 _
  refine WP.alu ac_at_aca ?_; wn
  refine WP.lbu ac_at_ace ?_; wn
  refine WP.aluImm ac_at_ad2 ?_; wn
  refine WP.branch ac_at_ad6 (fun hb => ?_) (fun _ => ?_)
  rotate_left
  · wn; refine WP.jal ac_at_ad8 (by decide) ?_; wn
    exact act_x6a (hI.regs (by act_r) (by act_r) (by act_r)) hr (by act_r <;> decide)
  wn
  have hc1 : (M (q + BitVec.ofNat 32 (l - 1))).toNat = 34 := by
    revert hb; act_r; rw [e0, hpq, e4, hpl, act_last (by omega) hl32]; simp only [branchTaken]; exact act_q34 _
  have hsb : strBody (memBytes M q l) = some (((memBytes M q l).drop 1).take (l - 2)) := by
    unfold strBody
    rw [memBytes_length, memBytes_getD (by omega), memBytes_getD (by omega), add_ofNat_zero, hc0, hc1,
      if_neg (by omega), if_neg (by decide), if_neg (by decide)]
  refine WP.aluImm ac_at_adc ?_; wn
  refine WP.branch ac_at_ae0 (fun hb => ?_) (fun hb => ?_)
  · wn
    refine act_af4 hROM hR4 hR X (hI.regs (by act_r) (by act_r) (by act_r)) hr hO h18 h14 hval
      (by act_r; exact hdoc) (by act_r; exact hs4) (fun h9 => ?_) (hspec _ hsb) h20 h24 h28 h2C
      (by act_r; exact hs3) (by act_r; exact hs6) (by act_r; exact hs5) (by act_r; exact hs9) (by act_r; exact hs11)
    exfalso; revert hb h9; act_r; rw [e4, hpl]; simp only [branchTaken]; intro hb h9; rw [h9] at hb
    exact absurd hb (by decide)
  have hl : l = 0x42 := by
    revert hb; act_r; rw [e4, hpl]; simp only [branchTaken, bne_eq_false_iff_eq]; exact fun h => act_l42 h hl32
  subst hl
  wn
  refine WP.aluImm ac_at_ae2 ?_; wn
  refine WP.aluImm ac_at_ae4 ?_; wn
  refine WP.aluImm ac_at_ae8 ?_; wn
  have hqB : q = Bf + BitVec.ofNat 32 (q.toNat - Bf.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [X.bfLo (by omega)]; omega
  have hsrc : q + 1 = Bf + BitVec.ofNat 32 (q.toNat - Bf.toNat + 1) := by
    conv => lhs; rw [hqB]
    exact add_ofNat_assoc Bf _ _
  refine act_mc (dst := acSlot B 0x351) (src := q + 1) (N := 64) X (hI.regs (by act_r) (by act_r) (by act_r))
    ac_at_aec ac_at_af0 (by decide) (by decide) (by act_r; exact act_spc hI.rsp _ _ rfl)
    (by act_r; rw [e0, hpq]) (by act_r <;> rfl) (X.low (by decide))
    (by rw [hsrc, X.bfLo (by omega)]; omega) (X.ss (by decide) (by decide) (Or.inr (by decide)))
    (by rw [hsrc]; exact (X.sbf (a := 0x3A40) (n := 16) (by decide) (by omega)).symm)
    (by rw [hsrc]; exact X.sbf (by decide) (by omega)) fun m2 hO2 => ?_
  have hk : ∀ x, Sep x 1 B 0x3A50 → Sep x 1 (acSlot B 0x351) 64 → m2.mem x = M x := fun x a b => by
    rw [hO2 x (a.subR (c := 0x3A40) (l := 16) (by decide))]; exact copyBytes_sep b.symm (Nat.le_refl _)
  have hkf : ∀ c, c + 1 ≤ 0x5A70 → 0x3A50 ≤ c → (c + 1 ≤ 0x3DA1 ∨ 0x3DE1 ≤ c) →
      m2.mem (B + BitVec.ofNat 32 c) = M (B + BitVec.ofNat 32 c) := fun c h0 h1 h2 =>
    hk _ (X.sB0 h0 h1) (X.ss h0 (by decide) h2)
  have hld : ∀ c, c + 4 ≤ 0x5A70 → 0x3A50 ≤ c → (c + 4 ≤ 0x3DA1 ∨ 0x3DE1 ≤ c) →
      memLoad32 m2.mem (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) := fun c h0 h1 h2 =>
    memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hkf _ (by omega) (by omega) (by omega)
  have kO : ∀ x, ActOut B Bf x → m2.mem x = M x := fun x hx => hk x hx.1 (by
    have := hx.2.2.2.1.subR (c := 1) (l := 64) (by decide); rwa [add_ofNat_assoc] at this)
  refine act_af4 hROM hR4 hR X ((hI.mem F X.sB kO).regs (by act_r) (by act_r) (by act_r))
    ((hld (0x3A50 + 0x40) (by decide) (by decide) (by decide)).trans hr)
    (fun x hx => (kO x hx).trans (hO x hx))
    ((hld (0x3A50 + 0x18) (by decide) (by decide) (by decide)).trans h18)
    ((hld (0x3A50 + 0x14) (by decide) (by decide) (by decide)).trans h14) hval ?_ (by act_r; exact hs4)
    (fun _ => ?_) (hspec _ hsb)
    ((hld (0x3A50 + 0x20) (by decide) (by decide) (by decide)).trans h20)
    ((hld (0x3A50 + 0x24) (by decide) (by decide) (by decide)).trans h24)
    ((hld (0x3A50 + 0x28) (by decide) (by decide) (by decide)).trans h28)
    ((hld (0x3A50 + 0x2C) (by decide) (by decide) (by decide)).trans h2C)
    (by act_r; exact hs3) (by act_r; exact hs6) (by act_r; exact hs5) (by act_r; exact hs9) (by act_r; exact hs11)
  · rw [hld (0x3A50 + 0x1C) (by decide) (by decide) (by decide)]
    intro o l' h
    rw [act_tid_congr (M := M) (M' := m2.mem)
      (fun j hj => by rw [add_ofNat_assoc]; exact hkf _ (by omega) (by omega) (by omega))] at h
    exact hdoc o l' h
  · rw [show 66 - 2 = 64 from rfl, memBytes_drop_take (by decide)]
    refine memBytes_ext fun i hi => ?_
    have hs : Sep (acSlot B 0x351 + BitVec.ofNat 32 i) 1 (B + BitVec.ofNat 32 0x3A40) 16 := by
      rw [add_ofNat_assoc]; exact X.ss (by omega) (by decide) (Or.inr (by omega))
    rw [hO2 _ hs, copyBytes_at hi (by decide)]; rfl

end

end C3.RV32.Ac
