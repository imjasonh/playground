import C3BootProofs.Proofs.AcceptTargetsFld

/-!
# `targets.json`'s expiry

From 0x93A: `expires` on `targets.json`'s `signed` value, the expiry to
`sp + 0x20`, then `act_99a`.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.Json

set_option maxRecDepth 200000

theorem act_texRes_frame {M M' : Word → BitVec 8} {s out : Word} {r : Except Nat Nat} (h : TexRes M M' s out r) :
    ∀ x, Sep x 1 s 308 → Sep x 1 out 16 → M' x = M x := by
  rcases r with _ | _
  · exact h.1
  · exact h.1

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- A call to `expires` on the `n` bytes at `p`. -/
theorem act_callTex {hi lo out s p : Word} {n : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = TEX) (hev : (off + 8) % 2 = 0)
    (hc : TexCode M) (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (hsp : f sp = s + BitVec.ofNat 32 308) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (hsw : s.toNat + 308 ≤ 0x40000000) (hro : Sep s 308 (BitVec.ofNat 32 roWindowAddress) roWindowSize)
    (hp0 : p.toNat ≠ 0) (hpw : p.toNat + n + 4 ≤ 0x40000000) (hSp : Sep s 308 p (n + 4))
    (how : out.toNat + 16 ≤ 0x40000000) (hso : Sep out 16 s 308)
    (hSb : Sep s 308 base code.length) (hsb : Sep out 16 base code.length)
    (k : ∀ m2 : Machine, TexRes M m2.mem s out (expiresModel (memBytes M p n)) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := TEX) (cl := jClob)
    (P := fun m2 => TexRes M m2.mem s out (expiresModel (memBytes M p n)))
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc' i hi => by
      rw [act_texRes_frame hP _ (hSb.symm.sub (c := i) (l := 1) hi) (hsb.symm.sub (c := i) (l := 1) hi)]
      exact hc' i hi) k
  obtain ⟨m2, c2, pc2, hR, hfr⟩ := tufExpires_correct m1 (retAddr := base + BitVec.ofNat 32 (off + 8))
    (by rw [hmem1]; exact hc) hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1)
    (by rw [hreg1]; rsimp; exact ha2) (by rw [hreg1]; rsimp; exact hsp) (by rw [hreg1]; rsimp)
    (even_clear _ (even_at base hb _ hev)) hal halo hsw hro hp0 hpw hSp how hso
  rw [hmem1] at hR
  exact ⟨m2, c2, pc2, hR, hfr⟩

end

section
variable {romBase : Word} {romCode : List Nat} {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8}
  {M M' : Word → BitVec 8} {f : Fin 32 → Word} {Q : Post} {off : Nat}

/-- A call to `expires` from the closure. -/
theorem act_tex (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f) {hi lo p : Word} {n c : Nat}
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = TEX) (hev : (off + 8) % 2 = 0)
    (h0 : f a0 = B + BitVec.ofNat 32 c) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (hc : 0x3A50 ≤ c ∧ c + 16 ≤ 0x5A70 ∧ c % 4 = 0) (hp0 : p.toNat ≠ 0) (hpw : p.toNat + n + 4 ≤ 0x40000000)
    (hSp : Sep (B + BitVec.ofNat 32 0x391C) 308 p (n + 4))
    (k : ∀ m2 : Machine, TexRes M m2.mem (B + BitVec.ofNat 32 0x391C) (B + BitVec.ofNat 32 c)
        (expiresModel (memBytes M p n)) →
      WP bootMainClosure0Code AC Q m2.mem (off + 8)
        (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  refine act_callTex h1 h2 htgt hev (X.E hI).tex h0 ha1 ha2 ?_ (X.al (by decide) (by decide))
    (X.al (by omega) hc.2.2) (X.low (by decide)) (X.sro (by decide)) hp0 hpw hSp (X.low (by omega))
    (X.ss (by omega) (by decide) (Or.inr (by omega))) (X.sc (by decide) (by decide) (by decide))
    (X.sc (by omega) (by decide) (by decide)) k
  rw [hI.rsp, add_ofNat_assoc]; rfl

theorem act_tres_kp {c : Nat} {r : Except Nat Nat}
    (h : TexRes M M' (B + BitVec.ofNat 32 0x391C) (B + BitVec.ofNat 32 c) r) : ActKp B c 16 M M' :=
  fun x a b => act_texRes_frame h x (a.subR (c := 0x391C) (l := 308) (by decide)) b

theorem act_st_kp2 (c : Nat) (w1 w2 : Word) :
    ActKp B c 8 M (memStore32 (memStore32 M (B + BitVec.ofNat 32 c) w1) (B + BitVec.ofNat 32 (c + 4)) w2) :=
  fun x _ b => by
    rw [memStore32_get_sep (by have := b.symm.sub (c := 4) (l := 4) (by decide); rwa [add_ofNat_assoc] at this),
      memStore32_get_sep (by have := b.symm.sub (c := 0) (l := 4) (by decide); rwa [BitVec.add_zero] at this)]

theorem act_out_20 : ∀ x, ActOut B Bf x → Sep x 1 (B + BitVec.ofNat 32 0x3A70) 8 := fun x hx => by
  have := hx.2.2.1.subR (c := 0) (l := 8) (by decide)
  rwa [add_ofNat_assoc] at this

theorem act_ofNat_mod (t : Nat) : BitVec.ofNat 32 (t % 2 ^ 32) = BitVec.ofNat 32 t := by
  apply BitVec.eq_of_toNat_eq; simp

/-- **From 0x93A**: `expires` on the `signed` value `dS` at `S`, the expiry
to `sp + 0x20`, then `act_99a`. -/
theorem act_93a {flash : Nat → BitVec 8} {R : Nat} (hROM : RomRead flash R romBase romCode)
    (hR4 : R % 4 = 0) (hR : R ≤ 0x3A50 - 0x180)
    (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f)
    (hr : memLoad32 M (acSlot B 0x40) = r) {pinned : Bytes} {parts : TufParts} {root : TufRoot} {re : Nat}
    {x21 x25 x27 : Word} {Mi : Word → BitVec 8} {S : Word} {sl : Nat} {dS : Bytes}
    (hO : ∀ x, ActOut B Bf x → M x = Mi x)
    (hdoc : ActDoc flash M (acSlot B 0x244) (f 24) ((memLoad32 M (acSlot B 0x1C)).toNat + 1) parts.trustedRoot)
    (hs4 : f 20 = Bf + 0x4000)
    (hs2 : f 18 = S) (h864 : memLoad32 M (acSlot B 0x1864) = BitVec.ofNat 32 sl)
    (hS1 : Bf.toNat + 0x4000 ≤ S.toNat) (hS2 : S.toNat + sl ≤ Bf.toNat + 0x6800) (hd : memBytes M S sl = dS)
    (hspec : ∀ te, expiresModel dS = .ok te →
      ∀ p1 l1 p2 l2 p3 l3 val p4 l4 p5 l5 body, objField dS (ascii!"targets") = .ok (p1, l1) →
      objGet (slice dS p1 l1) (ascii!"trusted_root.json") = .ok (some (p2, l2)) →
      objField (slice (slice dS p1 l1) p2 l2) (ascii!"length") = .ok (p3, l3) →
      u64Val (slice (slice (slice dS p1 l1) p2 l2) p3 l3) = some val →
      objField (slice (slice dS p1 l1) p2 l2) (ascii!"hashes") = .ok (p4, l4) →
      objField (slice (slice (slice dS p1 l1) p2 l2) p4 l4) (ascii!"sha256") = .ok (p5, l5) →
      strBody (slice (slice (slice (slice dS p1 l1) p2 l2) p4 l4) p5 l5) = some body →
      val = parts.trustedRoot.length →
      body = hexBytes (sha256 parts.trustedRoot) → verifyTuf pinned parts = some (root.version, min re te))
    (h28 : memLoad32 M (acSlot B 0x28) = BitVec.ofNat 32 re)
    (h2C : memLoad32 M (acSlot B 0x2C) = BitVec.ofNat 32 (re / 2 ^ 32))
    (hs3 : f 19 = acSlot B 0x890) (hs5 : f 21 = x21) (hs9 : f 25 = x25) (hs11 : f 27 = x27) :
    WP bootMainClosure0Code AC (actQ B Bf g t r v M0 (AcTargetsPost pinned parts root re B Bf x21 x25 x27 Mi))
      M 0x93A f := by
  have F := X.F
  have hbh := X.bhi
  have hbl : acBufLen = 0xB954 := rfl
  have hdl : dS.length = sl := by rw [← hd, memBytes_length]
  refine WP.zero fun hz => ?_
  refine WP.lui ac_at_93a ?_; wn
  refine WP.aluImm ac_at_93c ?_; wn
  refine WP.alu ac_at_940 ?_; wn
  have es : f sp + (4096 + 784) = acSlot B 0x1310 := act_spc hI.rsp _ _ rfl
  have e864 : acSlot B 0x1310 + 1364 = acSlot B 0x1864 := by
    rw [acSlot, acSlot, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  refine WP.lw ac_at_944 (by act_r; rw [es, e864]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_948 ?_; wn
  refine WP.aluImm ac_at_94a ?_; wn
  refine WP.alu ac_at_94e ?_; wn
  refine WP.alu ac_at_950 ?_; wn
  refine WP.alu ac_at_952 ?_; wn
  have hS0 : S.toNat ≠ 0 := by omega
  refine act_tex (c := 0x52C0) (p := S) (n := sl) X (hI.regs (by act_r) (by act_r) (by act_r))
    ac_at_954 ac_at_958 (by decide) (by decide)
    (by act_r; rw [BitVec.add_comm _ (f sp)]; exact act_spc hI.rsp _ _ rfl) (by act_r; exact hs2)
    (by act_r; rw [es, e864]; exact h864) (by decide) hS0 (by omega)
    (X.sfb (by decide) (by omega) (by omega)) fun m1 hf1 => ?_
  have k1 := act_tres_kp hf1
  rw [hd] at hf1
  have hI1 := hI.mem F X.sB (k1.out act_out_1870w)
  have L1 : ∀ c, 0x3A50 ≤ c → c + 4 ≤ 0x52C0 →
      memLoad32 m1.mem (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
    fun c h1 h2 => k1.ld X (by decide) (by omega) h1 (Or.inl (by omega))
  have hd1 : memBytes m1.mem S sl = dS := by rw [k1.bf X (by decide) (by omega) (by omega), hd]
  have e0 : acSlot B 0x1310 + 1376 = B + BitVec.ofNat 32 0x52C0 := by
    rw [acSlot, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  have e1 : acSlot B 0x1310 + 1377 = B + BitVec.ofNat 32 0x52C0 + 1 := by
    rw [acSlot, BitVec.add_assoc, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  wn
  refine WP.lui ac_at_95c ?_; wn
  refine WP.aluImm ac_at_95e ?_; wn
  refine WP.alu ac_at_962 ?_; wn
  refine WP.lbu ac_at_966 ?_; wn
  rcases hx : expiresModel dS with e | te
  · rw [hx] at hf1
    have he := act_eb_expiresModel _ e hx
    obtain ⟨_, h0, hb1⟩ := hf1
    refine WP.branch ac_at_96a (fun hb => ?_) (fun _ => ?_)
    · exfalso; revert hb; act_r; rw [es, e0, h0]; decide
    wn
    refine WP.lbu ac_at_96c ?_; wn
    refine WP.jal ac_at_970 (by decide) ?_; wn
    refine act_x6a (hI1.regs (by act_r) (by act_r) (by act_r)) ((L1 _ (by decide) (by decide)).trans hr) ?_
    act_r; rw [es, e1, hb1]; exact act_zb _ (by rw [BitVec.toNat_ofNat]; omega)
  rw [hx] at hf1
  obtain ⟨_, h0, hlo, hhi⟩ := hf1
  refine WP.branch ac_at_96a (fun _ => ?_) (fun hb => by exfalso; revert hb; act_r; rw [es, e0, h0]; decide)
  wn
  refine WP.lui ac_at_97c ?_; wn
  refine WP.aluImm ac_at_97e ?_; wn
  refine WP.alu ac_at_982 ?_; wn
  have es2 : 4096 + 784 + f sp = acSlot B 0x1310 := by rw [BitVec.add_comm]; exact es
  have e8 : acSlot B 0x1310 + 1384 = B + BitVec.ofNat 32 0x52C8 := by
    rw [acSlot, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  have e12 : acSlot B 0x1310 + 1388 = B + BitVec.ofNat 32 0x52CC := by
    rw [acSlot, BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  have q8 : B + BitVec.ofNat 32 0x52C0 + 8 = B + BitVec.ofNat 32 0x52C8 := by
    rw [BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  have q12 : B + BitVec.ofNat 32 0x52C0 + 0xC = B + BitVec.ofNat 32 0x52CC := by
    rw [BitVec.add_assoc]; exact congrArg (B + ·) (by decide)
  rw [q8, act_ofNat_mod] at hlo
  rw [q12] at hhi
  refine WP.lw ac_at_984 (by act_r; rw [es2, e8]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.sw ac_at_988 (by act_r; rw [act_spc hI.rsp _ 0x3A70 rfl]; exact X.al (by decide) (by decide))
    (by act_r; rw [act_spc hI.rsp _ 0x3A70 rfl]; exact X.sc (by decide) (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_98a ?_; wn
  refine WP.aluImm ac_at_98c ?_; wn
  refine WP.alu ac_at_990 ?_; wn
  refine WP.lw ac_at_994 (by act_r; rw [es2, e12]; exact X.al (by decide) (by decide)) ?_; wn
  refine WP.sw ac_at_998 (by act_r; rw [act_spc hI.rsp _ 0x3A74 rfl]; exact X.al (by decide) (by decide))
    (by act_r; rw [act_spc hI.rsp _ 0x3A74 rfl]; exact X.sc (by decide) (by decide) (by decide)) ?_; wn
  have es3 : aluEval AluOp.add (aluEval AluOp.add 4096 784) (f sp) = acSlot B 0x1310 := es2
  rw [es3, e8, e12, act_spc hI.rsp 32 0x3A70 rfl, act_spc hI.rsp 36 0x3A74 rfl,
    memLoad32_store32_sep (X.ss (by decide) (by decide) (Or.inl (by decide))), hlo, hhi]
  have K2 := act_st_kp2 (M := m1.mem) (B := B) 0x3A70 (BitVec.ofNat 32 te) (BitVec.ofNat 32 (te / 2 ^ 32))
  have L2 : ∀ c, 0x3A50 ≤ c → (c + 4 ≤ 0x3A70 ∨ 0x3A78 ≤ c) → c + 4 ≤ 0x52C0 → memLoad32 (memStore32 (memStore32 m1.mem (B + BitVec.ofNat 32 0x3A70)
      (BitVec.ofNat 32 te)) (B + BitVec.ofNat 32 0x3A74) (BitVec.ofNat 32 (te / 2 ^ 32))) (B + BitVec.ofNat 32 c) =
      memLoad32 M (B + BitVec.ofNat 32 c) :=
    fun c h0 h1 h2 => (K2.ld X (by decide) (by omega) h0 (by omega)).trans (L1 c h0 h2)
  refine act_99a (te := te) (S := S) (sl := sl) hROM hR4 hR X
    ((hI1.mem F X.sB (K2.out act_out_20)).regs (by act_r) (by act_r) (by act_r))
    ((L2 _ (by decide) (by decide) (by decide)).trans hr)
    (fun x hx => (K2.out act_out_20 x hx).trans ((k1.out act_out_1870w x hx).trans (hO x hx)))
    (by rw [L2 _ (by decide) (by decide) (by decide)]; act_r
        exact K2.doc X (by decide) (Or.inr (by decide)) (k1.doc X (by decide) (Or.inl (by decide)) hdoc))
    (by act_r; exact hs4) (by act_r; exact hs2) (by act_r; rw [es, e864]; exact h864) hS1 hS2
    (by rw [K2.bf X (by decide) (by omega) (by omega), hd1]) (hspec te hx)
    (by rw [show acSlot B 0x20 = B + BitVec.ofNat 32 0x3A70 from rfl,
      memLoad32_store32_sep (X.ss (by decide) (by decide) (Or.inr (by decide))), memLoad32_store32_same])
    (by rw [show acSlot B 0x24 = B + BitVec.ofNat 32 0x3A74 from rfl, memLoad32_store32_same])
    ((L2 _ (by decide) (by decide) (by decide)).trans h28) ((L2 _ (by decide) (by decide) (by decide)).trans h2C)
    (by act_r; exact hs3) (by act_r; exact es) (by act_r; exact hs5) (by act_r; exact hs9) (by act_r; exact hs11)

end

end C3.RV32.Ac
