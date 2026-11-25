import C3BootProofs.Proofs.AcceptTargetsCalls
import C3BootProofs.Proofs.AcceptTargetsSpec

/-!
# The end of the `targets.json` stage

From 0xBC0: the check of `trusted_root.json`'s length against `targets`,
and of its SHA-256 digest, in hex, against the `sha256` hash in `targets`.
The exits at 0xC02 and 0xC0A, which the whole stage shares, are here too.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.Json

set_option maxRecDepth 20000

theorem act_z (x : Word) : 0 + x = x := BitVec.zero_add x

/-- Evaluates a run of `upd` and `clob` and the `add`s in it. -/
macro "act_r" : tactic => `(tactic| simp +decide only [upd_app, clob_app, ↓reduceIte, ev_add, act_z])

theorem act_spc {B : Word} {f : Fin 32 → Word} (h : f sp = B + 0x3A50) (k : Word) (c : Nat)
    (hc : (0x3A50 + k.toNat) % 2 ^ 32 = c) : f sp + k = B + BitVec.ofNat 32 c := by
  rw [h, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, ← hc, Nat.mod_mod]
  rfl

section
variable {romBase : Word} {romCode : List Nat} {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8}
  {P : Machine → Prop} {M : Word → BitVec 8} {f : Fin 32 → Word}

/-- **The exit at 0xC02**: `s0 = 0x24` (`TrustedRootHash`), then the exit
at 0x1A6A. -/
theorem act_c02 (hI : ActI B Bf g t v M0 M f) (hr : memLoad32 M (acSlot B 0x40) = r) :
    WP bootMainClosure0Code AC (actQ B Bf g t r v M0 P) M 0xC02 f := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm ac_at_c02 ?_; wn
  refine WP.jal ac_at_c06 (by decide) ?_; wn
  exact act_x6a (hI.put (q := 8) (by decide) _) hr (by act_r; rw [hz]; decide)

/-- **The exit at 0xC0A**: `s0` is the error byte at `s6 + 0x564`, then the
exit at 0x1A6A. -/
theorem act_c0a (hI : ActI B Bf g t v M0 M f) (hr : memLoad32 M (acSlot B 0x40) = r)
    (hc : (M (f 22 + 0x564)).toNat < 0x27) :
    WP bootMainClosure0Code AC (actQ B Bf g t r v M0 P) M 0xC0A f := by
  refine WP.lbu ac_at_c0a ?_; wn
  refine WP.jal ac_at_c0e (by decide) ?_; wn
  refine act_x6a (hI.put (q := 8) (by decide) _) hr ?_
  act_r
  rw [BitVec.toNat_and]
  refine Nat.lt_of_le_of_lt Nat.and_le_left ?_
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
  have := (M (f 22 + 0x564)).isLt
  omega

/-- **The checks of `trusted_root.json`**, from 0xBC0. The length in
`targets` is `hi * 2^32 + lo` from `sp + 0x18` and `sp + 0x14`, `doc`
holds the `L` bytes of the trusted root, the hex of its digest is at
`sp + 0x1ED0`, and when `s1` is zero the `sha256` hash in `targets` is at
`sp + 0x351`. `hspec` is what `verifyTuf` needs of the two checks. -/
theorem act_tail (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f)
    (hr : memLoad32 M (acSlot B 0x40) = r) {pinned : Bytes} {parts : TufParts} {root : TufRoot} {re te : Nat}
    {x21 x25 x27 : Word} {Mi : Word → BitVec 8} {hiW loW : Word} {val : Nat} {body : Bytes}
    (hO : ∀ x, ActOut B Bf x → M x = Mi x)
    (h18 : memLoad32 M (acSlot B 0x18) = hiW) (h14 : memLoad32 M (acSlot B 0x14) = loW)
    (hval : hiW.toNat * 2 ^ 32 + loW.toNat = val)
    (hL : f 24 = BitVec.ofNat 32 parts.trustedRoot.length) (hLt : parts.trustedRoot.length ≤ 0x2800)
    (hdoc : memBytes M (Bf + 0x4000) parts.trustedRoot.length = parts.trustedRoot)
    (hhex : memBytes M (acSlot B 0x1ED0) 64 = hexBytes (sha256 parts.trustedRoot))
    (hbody : f 9 = 0 → memBytes M (acSlot B 0x351) 64 = body)
    (hspec : val = parts.trustedRoot.length → body = hexBytes (sha256 parts.trustedRoot) →
      verifyTuf pinned parts = some (root.version, min re te))
    (h20 : memLoad32 M (acSlot B 0x20) = BitVec.ofNat 32 te)
    (h24 : memLoad32 M (acSlot B 0x24) = BitVec.ofNat 32 (te / 2 ^ 32))
    (h28 : memLoad32 M (acSlot B 0x28) = BitVec.ofNat 32 re)
    (h2C : memLoad32 M (acSlot B 0x2C) = BitVec.ofNat 32 (re / 2 ^ 32))
    (hs2 : f 18 = Bf + 0x4000) (hs3 : f 19 = acSlot B 0x890) (hs6 : f 22 = acSlot B 0x1310)
    (hs5 : f 21 = x21) (hs9 : f 25 = x25) (hs11 : f 27 = x27) :
    WP bootMainClosure0Code AC (actQ B Bf g t r v M0 (AcTargetsPost pinned parts root re B Bf x21 x25 x27 Mi))
      M 0xBC0 f := by
  have F := X.F
  refine WP.zero fun hz => ?_
  refine WP.lw ac_at_bc0 (by rw [hI.rsp]; exact ac_fa F 0x18 (by decide) (by decide)) ?_; wn
  rw [act_spc hI.rsp 0x18 (0x3A50 + 0x18) rfl, show B + BitVec.ofNat 32 (0x3A50 + 0x18) = acSlot B 0x18 from rfl,
    h18]
  refine WP.branch ac_at_bc2 (fun _ => ?_) (fun hb => ?_)
  · wn; exact act_c02 (hI.put (by decide) _) hr
  have hh : hiW = 0 := by revert hb; act_r; simp [branchTaken]
  wn
  refine WP.lw ac_at_bc4 (by act_r; rw [hI.rsp]; exact ac_fa F 0x14 (by decide) (by decide)) ?_; wn
  rw [act_spc hI.rsp 0x14 (0x3A50 + 0x14) rfl, show B + BitVec.ofNat 32 (0x3A50 + 0x14) = acSlot B 0x14 from rfl,
    h14]
  have hTL : parts.trustedRoot.length < 2 ^ 32 := by omega
  refine WP.branch ac_at_bc6 (fun _ => ?_) (fun hb => ?_)
  · wn; exact act_c02 (hI.put (by decide) _) hr
  have hlo : loW = BitVec.ofNat 32 parts.trustedRoot.length := by revert hb; act_r; rw [hL]; intro hb; simp only [branchTaken] at hb; exact (bne_eq_false_iff_eq.mp hb).symm
  have hv : val = parts.trustedRoot.length := by
    rw [← hval, hh, hlo, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hTL]; simp
  wn
  refine WP.lui ac_at_bca ?_; wn
  refine WP.aluImm ac_at_bcc ?_; wn
  refine WP.alu ac_at_bd0 ?_; wn
  refine WP.lui ac_at_bd4 ?_; wn
  refine WP.aluImm ac_at_bd6 ?_; wn
  refine WP.alu ac_at_bda ?_; wn
  refine WP.aluImm ac_at_bde ?_; wn
  refine WP.alu ac_at_be2 ?_; wn
  have e1 : f sp + (0x2000 + 0xFFFFF871) = B + BitVec.ofNat 32 0x52C1 := act_spc hI.rsp _ _ rfl
  have e2 : f sp + (0x2000 + 0xFFFFFED0) = B + BitVec.ofNat 32 0x5920 := act_spc hI.rsp _ _ rfl
  refine act_mc (dst := B + BitVec.ofNat 32 0x52C1) (src := B + BitVec.ofNat 32 0x5920) (N := 64) X (hI.regs (by act_r) (by act_r) (by act_r)) ac_at_be4 ac_at_be8 (by decide) (by decide)
    (by act_r; exact e1) (by act_r; exact e2) (by act_r) (X.low (by decide)) (X.low (by decide))
    (X.ss (by decide) (by decide) (Or.inr (by decide))) (X.ss (by decide) (by decide) (Or.inr (by decide)))
    (X.ss (by decide) (by decide) (Or.inl (by decide))) fun m2 hO2 => ?_
  have hcp : ∀ x, Sep x 1 (B + BitVec.ofNat 32 0x52C1) 64 → Sep x 1 (B + BitVec.ofNat 32 0x3A40) 16 →
      m2.mem x = M x := fun x h1 h2 => by rw [hO2 x h2, copyBytes_sep h1.symm (Nat.le_refl _)]
  have hcpy : memBytes m2.mem (B + BitVec.ofNat 32 0x52C1) 64 = hexBytes (sha256 parts.trustedRoot) := by
    rw [← hhex]
    refine memBytes_ext fun i hi => ?_
    have hs : Sep (B + BitVec.ofNat 32 0x52C1 + BitVec.ofNat 32 i) 1 (B + BitVec.ofNat 32 0x3A40) 16 := by
      rw [add_ofNat_assoc]; exact X.ss (by omega) (by decide) (Or.inr (by omega))
    rw [hO2 _ hs, copyBytes_at hi (by decide), add_ofNat_assoc]
  have hkeep : ∀ x, ActOut B Bf x → m2.mem x = M x := fun x hx => by
    refine hcp x ?_ ?_
    · have h := (hx.2.2.2.2.1).subR (c := 0x11) (l := 64) (by decide)
      rw [show acSlot B 0x1860 + BitVec.ofNat 32 0x11 = B + BitVec.ofNat 32 0x52C1 by
        rw [add_ofNat_assoc]] at h
      exact h
    · exact hx.1.subR (c := 0x3A40) (l := 16) (by decide)
  have hI2 : ActI B Bf g t v M0 m2.mem f := hI.mem F X.sB hkeep
  have ld : ∀ c, c + 4 ≤ 0x5A70 → (c + 4 ≤ 0x3A40 ∨ 0x3A50 ≤ c) → (c + 4 ≤ 0x52C1 ∨ 0x5301 ≤ c) →
      memLoad32 m2.mem (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) := fun c h0 h1 h2 =>
    memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      exact hcp _ (X.ss (by omega) (by decide) (by omega)) (X.ss (by omega) (by decide) (by omega))
  have hr2 : memLoad32 m2.mem (acSlot B 0x40) = r := (ld _ (by decide) (by decide) (by decide)).trans hr
  wn
  refine WP.branch ac_at_bec (fun _ => ?_) (fun hb => ?_)
  · wn; exact act_c02 (hI2.regs (by act_r) (by act_r) (by act_r)) hr2
  have h9 : f 9 = 0 := by revert hb; act_r; intro hb; simp only [branchTaken] at hb; exact bne_eq_false_iff_eq.mp hb
  wn
  refine WP.aluImm ac_at_bee ?_; wn
  refine WP.aluImm ac_at_bf2 ?_; wn
  refine WP.alu ac_at_bf6 ?_; wn
  refine act_cmp (p := B + BitVec.ofNat 32 0x3DA1) (q := B + BitVec.ofNat 32 0x52C1) (n := 64) X
    (hI2.regs (by act_r) (by act_r) (by act_r)) ac_at_bf8 ac_at_bfc (by decide) (by decide)
    (by act_r; exact act_spc hI.rsp _ _ rfl) (by act_r; exact e1) (by act_r) (by decide) fun m3 hc3 hm3 => ?_
  rw [hm3]; wn
  refine WP.branch ac_at_c00 (fun ht => ?_) (fun _ => ?_)
  · wn
    refine act_stop fun m hpc hm hf => Or.inr ⟨(hI2.regs (f' := reg m) (by rw [hf]; act_r) (by rw [hf]; act_r)
      (by rw [hf]; act_r)).inv m hm rfl, Or.inr ⟨by rw [hpc]; rfl, ?_⟩⟩
    have ha0 : reg m3 a0 = 0 := by revert ht; act_r; intro ht; simp only [branchTaken] at ht; exact beq_iff_eq.mp ht
    have hbd : body = hexBytes (sha256 parts.trustedRoot) := by
      rw [← hbody h9, ← hcpy, ← hc3.mp ha0]
      exact (memBytes_congr fun i hi => by
        rw [add_ofNat_assoc]
        exact hcp _ (X.ss (by omega) (by decide) (Or.inl (by omega))) (X.ss (by omega) (by decide) (Or.inr (by omega)))).symm
    have hm' : m.mem = m2.mem := hm
    have hr' : ∀ q, reg m q = _ := fun q => congrFun hf q
    refine ⟨⟨te, hspec hv hbd, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_⟩
    · rw [hm', ld _ (by decide) (by decide) (by decide)]; exact h20
    · rw [hm', ld _ (by decide) (by decide) (by decide)]; exact h24
    · rw [hm', ld _ (by decide) (by decide) (by decide)]; exact h28
    · rw [hm', ld _ (by decide) (by decide) (by decide)]; exact h2C
    · rw [hr']; act_r; exact hs2
    · rw [hr']; act_r; exact hL
    · rw [hm']
      refine Eq.trans (memBytes_congr fun i hi => ?_) hdoc
      have hd : Bf + 0x4000 + BitVec.ofNat 32 i = Bf + BitVec.ofNat 32 (0x4000 + i) := add_ofNat_assoc Bf 0x4000 i
      rw [hd]
      have hbl : acBufLen = 0xB954 := rfl
      exact hcp _ (X.sbf (by decide) (by omega)).symm (X.sbf (by decide) (by omega)).symm
    · rw [hr']; act_r; exact hs3
    · rw [hr']; act_r; exact hs6
    · rw [hr']; act_r; exact hs5
    · rw [hr']; act_r; exact hs9
    · rw [hr']; act_r; exact hs11
    · rw [hm', hkeep x hx]; exact hO x hx
  · wn; exact act_c02 (hI2.regs (by act_r) (by act_r) (by act_r)) hr2

end

end C3.RV32.Ac
