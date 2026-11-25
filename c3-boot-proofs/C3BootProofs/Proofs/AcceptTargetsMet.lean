import C3BootProofs.Proofs.AcceptTargetsTex

/-!
# The threshold of signatures on `targets.json`

From 0x89A: copy `parse_metadata`'s result to `sp + 0x1860` and the root's
`RoleKeys` for `targets` to `sp + 0x1870`, call `RoleKeys::met`, and go on
to `act_93a` when the threshold is met.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.Json

set_option maxRecDepth 200000

section
variable {romBase : Word} {romCode : List Nat} {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8}
  {Q : Post} {M M' M'' : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- `RoleKeys::met` as `ActMetSpecPI` describes it, from
`tufRoleKeysMet_ret_pi` and `tlmr_thresholdMet`: `RoleKeys::met` returns 0
or 1 in `a0`, so bit 0 of `a0` clear is `Ok`. -/
theorem act_metSpec_pi : ActMetSpecPI := by
  intro m retAddr s R A MP SP ML SL t md dj sj role es hpc ha0 ha1 hsp hra hret hal hlo hhi hds hro hc halR hRw hSR
    hMw hML hSM hS0 hSw hSL hSS halA hSA hA0 hA4 hA8 hAC hrk hR hw hB hmsg hsj hps
  obtain ⟨m', st, q⟩ := tufRoleKeysMet_ret_pi m hpc ha0 ha1 hsp hra hret hal hlo hhi hds hro hc halR hRw hSR hMw hML
    hSM hS0 hSw hSL hSS halA hSA hA0 hA4 hA8 hAC hR hw
  refine ⟨m', st, ?_⟩
  rcases q with h | ⟨hp, hM, hr, hS, h01, hE⟩
  · exact .inl h
  refine .inr ⟨hp, hM, hr, fun h0 h1 => ?_, fun h0 => hE fun e => h0 (by rw [e]; rfl)⟩
  have e0 : reg m' a0 = 0 := by
    rcases h01 with e | e
    · exact e
    · rw [e] at h0; exact absurd h0 (by decide)
  have S := hS e0 fun e => h1 (by rw [e]; rfl)
  rw [hmsg] at S
  exact tlmr_thresholdMet hrk hB (metLookup_spec hsj hps) S

/-- `act_metSpec_pi` with any panic. -/
theorem act_metSpec : ActMetSpec := by
  intro m retAddr s R A MP SP ML SL t md dj sj role es hpc ha0 ha1 hsp hra hret hal hlo hhi hds hro hc halR hRw hSR
    hMw hML hSM hS0 hSw hSL hSS halA hSA hA0 hA4 hA8 hAC hrk hR hw hB hmsg hsj hps
  obtain ⟨m', st, q⟩ := act_metSpec_pi m hpc ha0 ha1 hsp hra hret hal hlo hhi hds hro hc halR hRw hSR hMw hML hSM
    hS0 hSw hSL hSS halA hSA hA0 hA4 hA8 hAC hrk hR hw hB hmsg hsj hps
  exact ⟨m', st, q.imp_left And.right⟩

/-- A call to `RoleKeys::met(rk, meta)` from the closure, with `rk` at
`sp + 0x1870` and `meta` at `sp + 0x1860`. -/
theorem act_met (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f)
    {hi lo MP SP : Word} {ML SL tt : Nat} {md : Meta} {dj sj : Json} {role : Bytes}
    {es : List (Bytes × Option TufKey)}
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = TRM) (hev : (off + 8) % 2 = 0)
    (hQ : ∀ m, ¬ InvBounds → Halting m → Q m.pc m.mem (reg m))
    (h0 : f a0 = B + BitVec.ofNat 32 0x52C0) (ha1 : f a1 = B + BitVec.ofNat 32 0x52B0)
    (hMw : MP.toNat + ML ≤ 0x40000000) (hML : ML < 2 ^ 31) (hSM : Sep (B + BitVec.ofNat 32 0x130) 0x3920 MP ML)
    (hS0 : SP.toNat ≠ 0) (hSw : SP.toNat + SL ≤ 0x40000000) (hSL : SL < 2 ^ 31)
    (hSS : Sep (B + BitVec.ofNat 32 0x130) 0x3920 SP SL)
    (hA0 : memLoad32 M (B + BitVec.ofNat 32 0x52B0) = MP)
    (hA4 : memLoad32 M (B + BitVec.ofNat 32 0x52B0 + BitVec.ofNat 32 4) = BitVec.ofNat 32 ML)
    (hA8 : memLoad32 M (B + BitVec.ofNat 32 0x52B0 + BitVec.ofNat 32 8) = SP)
    (hAC : memLoad32 M (B + BitVec.ofNat 32 0x52B0 + BitVec.ofNat 32 12) = BitVec.ofNat 32 SL)
    (hrk : roleKeys dj role = some (tt, es)) (hR : RkAt M (B + BitVec.ofNat 32 0x52C0) tt (es.map C3.Json.rkTag))
    (hw : RkWf (es.map C3.Json.rkTag)) (hB : RkBytes es) (hmsg : memBytes M MP ML = encode md.signed)
    (hsj : JVal true (memBytes M SP SL) sj) (hps : (sj.asArr >>= List.mapM sigPair) = some md.sigs)
    (k : ∀ m2 : Machine, (∀ x, Sep x 1 (B + BitVec.ofNat 32 0x130) 0x3920 → m2.mem x = M x) →
      (reg m2 a0 &&& 1 = 0 → reg m2 a1 &&& 1 ≠ 0 → thresholdMet md dj role = some true) →
      (reg m2 a0 &&& 1 ≠ 0 → (reg m2 a1 &&& 0xFF).toNat < 0x27) →
      WP bootMainClosure0Code AC Q m2.mem (off + 8)
        (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  have F := X.F
  have hSb : Sep (B + BitVec.ofNat 32 0x130) 0x3920 AC bootMainClosure0Code.length :=
    X.sc (by decide) (by decide) (by decide)
  refine WP.callGenPI (tb := TRM) (cl := jClob)
    (P := fun m2 => (∀ x, Sep x 1 (B + BitVec.ofNat 32 0x130) 0x3920 → m2.mem x = M x) ∧
      (reg m2 a0 &&& 1 = 0 → reg m2 a1 &&& 1 ≠ 0 → thresholdMet md dj role = some true) ∧
      (reg m2 a0 &&& 1 ≠ 0 → (reg m2 a1 &&& 0xFF).toNat < 0x27))
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) hQ (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc' i hi => by rw [hP.1 _ (hSb.symm.sub (c := i) (l := 1) hi)]; exact hc' i hi)
    (fun m2 hP => k m2 hP.1 hP.2.1 hP.2.2)
  have hlo : (B + BitVec.ofNat 32 0x130).toNat = B.toNat + 0x130 := X.lo (by decide)
  have := F.lo
  have := F.hi
  have := F.al
  obtain ⟨m2, st, h⟩ := act_metSpec_pi m1 (retAddr := AC + BitVec.ofNat 32 (off + 8)) (s := B + BitVec.ofNat 32 0x130)
    hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1)
    (by rw [hreg1]; rsimp; rw [hI.rsp, add_ofNat_assoc]; rfl) (by rw [hreg1]; rsimp)
    (even_clear _ (even_at AC hb _ hev)) (by rw [hlo]; omega) (by rw [hlo]; omega) (by rw [hlo]; omega)
    (F.bufData (c := 0x130) (n := 0x3920) (by decide) (Nat.le_refl _) (Nat.le_refl _)) (X.sro (by decide))
    (fun M' hM' => (X.env M' fun x hB hBf => by
      rw [hM' x (hB.subR (c := 0x130) (l := 0x3920) (by decide)), hmem1]; exact hI.out x hB hBf).rm)
    (X.al (by decide) (by decide)) (X.low (by decide)) (X.ss (by decide) (by decide) (Or.inl (by decide)))
    hMw hML hSM hS0 hSw hSL hSS (X.al (by decide) (by decide)) (X.ss (by decide) (by decide) (Or.inl (by decide)))
    (by rw [hmem1]; exact hA0) (by rw [hmem1]; exact hA4) (by rw [hmem1]; exact hA8) (by rw [hmem1]; exact hAC)
    hrk (by rw [hmem1]; exact hR) hw hB (by rw [hmem1]; exact hmsg) (by rw [hmem1]; exact hsj) hps
  rcases h with ⟨hni, hh⟩ | ⟨pc2, hfr, hrg, hok, herr⟩
  · exact .inl ⟨hni, m2, st, hh⟩
  · exact .inr ⟨m2, st, pc2, ⟨fun x hx => by rw [hfr x hx, hmem1], hok, herr⟩, hrg⟩

theorem act_sepIn {x : Word} {c0 n0 d n : Nat} (h : Sep x 1 (B + BitVec.ofNat 32 c0) n0) (h1 : c0 ≤ d)
    (h2 : d + n ≤ c0 + n0) : Sep x 1 (B + BitVec.ofNat 32 d) n := by
  have := h.subR (c := d - c0) (l := n) (by omega)
  rwa [add_ofNat_assoc, show c0 + (d - c0) = d by omega] at this

theorem ActKp.trans {c0 n0 : Nat} (h1 : ActKp B c0 n0 M M') (h2 : ActKp B c0 n0 M' M'') : ActKp B c0 n0 M M'' :=
  fun x a b => (h2 x a b).trans (h1 x a b)

theorem act_kp_mc {c0 n0 d N : Nat} {src : Word}
    (h : Out (copyBytes M (B + BitVec.ofNat 32 d) src N) M' (B + BitVec.ofNat 32 0x3A40) 16) (h1 : c0 ≤ d)
    (h2 : d + N ≤ c0 + n0) : ActKp B c0 n0 M M' := fun x a b => by
  rw [h x (a.subR (c := 0x3A40) (l := 16) (by decide))]
  exact copyBytes_sep (act_sepIn b h1 h2).symm (Nat.le_refl _)

theorem act_kp_sb {c0 n0 d : Nat} {w : BitVec 8} (h1 : c0 ≤ d) (h2 : d + 1 ≤ c0 + n0) :
    ActKp B c0 n0 M (memStore8 M (B + BitVec.ofNat 32 d) w) := fun x _ b => by
  have := act_sne (act_sepIn b h1 h2) (j := 0) (by decide)
  rw [BitVec.add_zero] at this
  exact memStore8_ne this

theorem act_kp_sw {c0 n0 d : Nat} {w : Word} (h1 : c0 ≤ d) (h2 : d + 4 ≤ c0 + n0) :
    ActKp B c0 n0 M (memStore32 M (B + BitVec.ofNat 32 d) w) := fun _ _ b =>
  memStore32_get_sep (act_sepIn b h1 h2).symm

theorem act_st8_ne {c d : Nat} {w : BitVec 8} (hc : c < 2 ^ 32) (hd : d < 2 ^ 32) (h : c ≠ d) :
    memStore8 M (B + BitVec.ofNat 32 d) w (B + BitVec.ofNat 32 c) = M (B + BitVec.ofNat 32 c) :=
  memStore8_ne (act_ofNat_ne hc hd h)

theorem act_rk0 {a : Word} {tt : Nat} {es : List RkEntry} (h : RkAt M a tt es) (hw : RkWf es) : M a ≠ 0xFE := by
  obtain ⟨_, _, _, h3⟩ := h
  have hs := (h3 0 (by decide)).2.2.2
  have e0 : a + BitVec.ofNat 32 (98 * 0) = a := BitVec.add_zero a
  rcases es with _ | ⟨⟨id, k⟩, es⟩
  · have hs' : M (a + BitVec.ofNat 32 (98 * 0)) = 0xFF := hs
    rw [e0] at hs'; rw [hs']; decide
  rcases k with _ | ⟨kt, kb⟩
  · have hs' : M (a + BitVec.ofNat 32 (98 * 0)) = 0xFF := hs
    rw [e0] at hs'; rw [hs']; decide
  have hs' : M (a + BitVec.ofNat 32 (98 * 0)) = BitVec.ofNat 8 kt := hs.1
  rw [e0] at hs'
  rw [hs']
  rcases hw (id, some (kt, kb)) List.mem_cons_self (kt, kb) rfl with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;>
    (simp only at h; subst h; decide)

theorem act_fe (b : BitVec 8) (h : b.zeroExtend 32 + 0xFFFFFF02 = 0) : b = 0xFE := by
  have h1 : b.zeroExtend 32 = 0xFE := by
    rw [← BitVec.add_sub_cancel (b.zeroExtend 32) 0xFFFFFF02, h]; decide
  have h2 := congrArg BitVec.toNat h1
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)] at h2
  exact BitVec.eq_of_toNat_eq h2

theorem act_sepw {a b y : Word} {n m k : Nat} (h : Sep a n b m) (h1 : b.toNat ≤ y.toNat)
    (h2 : y.toNat + k ≤ b.toNat + m) (hm : m < 2 ^ 32) : Sep a n y k := by
  intro i hi j hj e
  refine h i hi (y.toNat - b.toNat + j) (by omega) (e.trans ?_)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show j < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show y.toNat - b.toNat + j < 2 ^ 32 by omega)]
  congr 1; omega

/-- **From 0x89A**: copy `parse_metadata`'s result for `targets.json` from
`sp + 0x1870` to `sp + 0x1860`, copy the root's `RoleKeys` for `targets` to
`sp + 0x1870`, and check the threshold of signatures, then `act_93a`. -/
theorem act_89a {flash : Nat → BitVec 8} {R : Nat} (hROM : RomRead flash R romBase romCode)
    (hR4 : R % 4 = 0) (hR : R ≤ 0x3A50 - 0x180)
    (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f)
    (hr : memLoad32 M (acSlot B 0x40) = r) {pinned : Bytes} {parts : TufParts} {root : TufRoot} {re : Nat}
    {x21 x25 x27 : Word} {Mi : Word → BitVec 8} {S SP : Word} {sl SL : Nat} {dS : Bytes} {md : Meta}
    {sj : Json}
    (hO : ∀ x, ActOut B Bf x → M x = Mi x)
    (hdoc : ActDoc flash M (acSlot B 0x244) (f 24) ((memLoad32 M (acSlot B 0x1C)).toNat + 1) parts.trustedRoot)
    (hs4 : f 20 = Bf + 0x4000)
    (hs2 : f 18 = S) (hs0 : f 8 = (M (B + BitVec.ofNat 32 0x52C4)).zeroExtend 32)
    (hl1 : memLoad32 M (B + BitVec.ofNat 32 0x52C4) = BitVec.ofNat 32 sl)
    (hq2 : memLoad32 M (B + BitVec.ofNat 32 0x52C8) = SP)
    (hl2 : memLoad32 M (B + BitVec.ofNat 32 0x52CC) = BitVec.ofNat 32 SL)
    (hS1 : Bf.toNat + 0x4000 ≤ S.toNat) (hS2 : S.toNat + sl ≤ Bf.toNat + 0x6800)
    (hP1 : Bf.toNat + 0x4000 ≤ SP.toNat) (hP2 : SP.toNat + SL ≤ Bf.toNat + 0x6800)
    (hd : memBytes M S sl = dS) (hmsg : dS = encode md.signed)
    (hsj : JVal true (memBytes M SP SL) sj) (hps : (sj.asArr >>= List.mapM sigPair) = some md.sigs)
    (hK : ActRk M (B + BitVec.ofNat 32 0x4820) root)
    (hspec : thresholdMet md root.md.signed (ascii!"targets") = some true → ∀ te, expiresModel dS = .ok te →
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
    (hs5 : f 21 = x21) (hs9 : f 25 = x25) (hs11 : f 27 = x27) :
    WP bootMainClosure0Code AC (actQ B Bf g t r v M0 (AcTargetsPost pinned parts root re B Bf x21 x25 x27 Mi))
      M 0x89A f := by
  have F := X.F
  have hbh := X.bhi
  have hbl : acBufLen = 0xB954 := rfl
  refine WP.zero fun hz => ?_
  refine WP.lui ac_at_89a ?_; wn
  refine WP.aluImm ac_at_89c ?_; wn
  refine WP.alu ac_at_8a0 ?_; wn
  refine WP.lui ac_at_8a4 ?_; wn
  refine WP.aluImm ac_at_8a6 ?_; wn
  refine WP.alu ac_at_8aa ?_; wn
  refine WP.aluImm ac_at_8ac ?_; wn
  refine act_mc (dst := B + BitVec.ofNat 32 0x52B5) (src := B + BitVec.ofNat 32 0x52C5) (N := 11) X
    (hI.regs (by act_r) (by act_r) (by act_r)) ac_at_8ae ac_at_8b2 (by decide) (by decide)
    (by act_r; rw [BitVec.add_comm]; exact act_spc hI.rsp _ _ rfl) (by act_r; exact act_spc hI.rsp _ _ rfl)
    (by act_r <;> rfl) (X.low (by decide)) (X.low (by decide)) (X.ss (by decide) (by decide) (Or.inr (by decide)))
    (X.ss (by decide) (by decide) (Or.inr (by decide))) (X.ss (by decide) (by decide) (Or.inl (by decide)))
    fun m2 hO2 => ?_
  have K2 : ActKp B 0x52B0 0x550 M m2.mem := act_kp_mc hO2 (by decide) (by decide)
  have c2 : ∀ i, i < 11 → m2.mem (B + BitVec.ofNat 32 (0x52B5 + i)) = M (B + BitVec.ofNat 32 (0x52C5 + i)) :=
    fun i hi => by
      rw [← add_ofNat_assoc, hO2 _ (by rw [add_ofNat_assoc]; exact X.ss (by omega) (by decide) (Or.inr (by omega))),
        copyBytes_at hi (by decide), add_ofNat_assoc]
  wn
  have e890 : f sp + 0x7FF + 0x91 = acSlot B 0x890 := act_spc2 hI.rsp _ _ _ rfl
  have e1310 : 4096 + 784 + f sp = acSlot B 0x1310 := by rw [BitVec.add_comm]; exact act_spc hI.rsp _ _ rfl
  have eRk : acSlot B 0x890 + 0x540 = B + BitVec.ofNat 32 0x4820 := add_ofNat_assoc B _ _
  have eRk1 : acSlot B 0x890 + 0x541 = B + BitVec.ofNat 32 0x4821 := add_ofNat_assoc B _ _
  have eL : acSlot B 0x1310 + 0x554 = B + BitVec.ofNat 32 0x52B4 := add_ofNat_assoc B _ _
  have eQ : acSlot B 0x1310 + 0x550 = B + BitVec.ofNat 32 0x52B0 := add_ofNat_assoc B _ _
  have b0 : m2.mem (B + BitVec.ofNat 32 0x4820) = M (B + BitVec.ofNat 32 0x4820) :=
    K2.at X (by decide) (by decide) (by decide) (Or.inl (by decide))
  refine WP.aluImm ac_at_8b6 ?_; wn
  refine WP.aluImm ac_at_8ba ?_; wn
  refine WP.lbu ac_at_8be ?_; wn
  refine WP.lui ac_at_8c2 ?_; wn
  refine WP.aluImm ac_at_8c4 ?_; wn
  refine WP.alu ac_at_8c8 ?_; wn
  refine WP.sb ac_at_8ca (by act_r; rw [e1310, eL]; exact X.sc (by decide) (by decide) (by decide)) ?_; wn
  have e1310' : aluEval AluOp.add (aluEval AluOp.add 4096 784) (f sp) = acSlot B 0x1310 := e1310
  rw [e1310', eL, hs0, act_lbu_low]
  have K3 := K2.trans (act_kp_sb (M := m2.mem) (w := M (B + BitVec.ofNat 32 0x52C4)) (d := 0x52B4)
    (by decide) (by decide))
  generalize hM3 : memStore8 m2.mem (B + BitVec.ofNat 32 0x52B4) (M (B + BitVec.ofNat 32 0x52C4)) = M3 at K3
  have c3 : ∀ i, i < 12 → M3 (B + BitVec.ofNat 32 (0x52B4 + i)) = M (B + BitVec.ofNat 32 (0x52C4 + i)) :=
    fun i hi => by
      rw [← hM3]
      rcases i with _ | i
      · exact memStore8_same _ _ _
      · rw [act_st8_ne (by omega) (by decide) (by omega), show 0x52B4 + (i + 1) = 0x52B5 + i by omega,
          c2 i (by omega), show 0x52C5 + i = 0x52C4 + (i + 1) by omega]
  refine WP.aluImm ac_at_8ce ?_; wn
  refine WP.aluImm ac_at_8d2 ?_; wn
  refine WP.lbu ac_at_8d6 ?_; wn
  refine WP.aluImm ac_at_8da ?_; wn
  refine WP.sw ac_at_8de (by act_r; rw [eQ]; exact X.al (by decide) (by decide))
    (by act_r; rw [eQ]; exact X.sc (by decide) (by decide) (by decide)) ?_; wn
  rw [eQ, hs2]
  have K4 := K3.trans (act_kp_sw (M := M3) (w := S) (d := 0x52B0) (by decide) (by decide))
  generalize hM4 : memStore32 M3 (B + BitVec.ofNat 32 0x52B0) S = M4 at K4
  have w4 : memLoad32 M4 (B + BitVec.ofNat 32 0x52B0) = S := by rw [← hM4]; exact memLoad32_store32_same _ _ _
  have c4 : ∀ i, i < 12 → M4 (B + BitVec.ofNat 32 (0x52B4 + i)) = M (B + BitVec.ofNat 32 (0x52C4 + i)) :=
    fun i hi => by
      rw [← hM4, memStore32_get_sep (X.ss (by decide) (by omega) (Or.inl (by omega))), c3 i hi]
  have hI4 : ActI B Bf g t v M0 M4 f := hI.mem F X.sB fun x hx => K4 x hx.1 (act_ks hx.2.2.2.2.1 0 0x550 (by decide))
  refine WP.branch ac_at_8e2 (fun hb => ?_) (fun hb => ?_)
  rotate_left
  · rcases hK with ⟨tt, es, hrk, hRk, hw, hB⟩ | ⟨e0, e1⟩
    · exfalso; revert hb; act_r
      rw [e890, eRk, b0]; intro hb
      simp only [branchTaken, bne_eq_false_iff_eq] at hb
      exact act_rk0 hRk hw (act_fe _ hb)
    refine WP.jal ac_at_8e4 (by decide) ?_; wn
    refine act_x6a (hI4.regs (by act_r) (by act_r) (by act_r))
      ((K4.ld X (c := 0x3A90) (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hr) ?_
    act_r
    have b1 : M3 (B + BitVec.ofNat 32 0x4821) = M (B + BitVec.ofNat 32 0x4821) :=
      K3.at X (by decide) (by decide) (by decide) (Or.inl (by decide))
    rw [e890, eRk1, b1]
    have e1' : (M (B + BitVec.ofNat 32 0x4821)).toNat < 0x27 := by rw [add_ofNat_assoc] at e1; exact e1
    rw [BitVec.toNat_and]
    refine Nat.lt_of_le_of_lt Nat.and_le_left ?_
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
    omega
  rcases hK with ⟨tt, es, hrk, hRk, hw, hB⟩ | ⟨e0, e1⟩
  rotate_left
  · exfalso; revert hb; act_r
    rw [e890, eRk, b0, ← add_ofNat_zero (B + BitVec.ofNat 32 0x4820), e0]
    decide
  refine WP.aluImm ac_at_8e8 ?_; wn
  refine WP.aluImm ac_at_8ec ?_; wn
  refine WP.lui ac_at_8f0 ?_; wn
  refine WP.aluImm ac_at_8f2 ?_; wn
  refine WP.alu ac_at_8f6 ?_; wn
  refine WP.aluImm ac_at_8f8 ?_; wn
  refine act_mc (dst := B + BitVec.ofNat 32 0x52C2) (src := B + BitVec.ofNat 32 0x4822) (N := 0x53E) X
    (hI4.regs (by act_r) (by act_r) (by act_r)) ac_at_8fc ac_at_900 (by decide) (by decide)
    (by act_r; rw [BitVec.add_comm]; exact act_spc hI.rsp _ _ rfl) (by act_r; exact act_spc2 hI.rsp _ _ _ rfl)
    (by act_r <;> rfl) (X.low (by decide)) (X.low (by decide)) (X.ss (by decide) (by decide) (Or.inr (by decide)))
    (X.ss (by decide) (by decide) (Or.inr (by decide))) (X.ss (by decide) (by decide) (Or.inr (by decide)))
    fun m5 hO5 => ?_
  have K5 : ActKp B 0x52B0 0x550 M4 m5.mem := act_kp_mc hO5 (by decide) (by decide)
  have c5 : ∀ i, i < 0x53E → m5.mem (B + BitVec.ofNat 32 (0x52C2 + i)) = M (B + BitVec.ofNat 32 (0x4822 + i)) :=
    fun i hi => by
      rw [← add_ofNat_assoc, hO5 _ (by rw [add_ofNat_assoc]; exact X.ss (by omega) (by decide) (Or.inr (by omega))),
        copyBytes_at hi (by decide), add_ofNat_assoc]
      exact K4.at X (by decide) (by omega) (by omega) (Or.inl (by omega))
  wn
  have eR0 : acSlot B 0x1310 + 0x560 = B + BitVec.ofNat 32 0x52C0 := add_ofNat_assoc B _ _
  have eR1 : acSlot B 0x1310 + 0x561 = B + BitVec.ofNat 32 0x52C1 := add_ofNat_assoc B _ _
  refine WP.lui ac_at_904 ?_; wn
  refine WP.aluImm ac_at_906 ?_; wn
  refine WP.alu ac_at_90a ?_; wn
  refine WP.sb ac_at_90c (by act_r; rw [e1310, eR0]; exact X.sc (by decide) (by decide) (by decide)) ?_; wn
  refine WP.sb ac_at_910 (by act_r; rw [e1310, eR1]; exact X.sc (by decide) (by decide) (by decide)) ?_; wn
  have e890' : aluEval AluOp.add (aluEval AluOp.add (f sp) 2047) 145 = acSlot B 0x890 := e890
  have b1 : M3 (B + BitVec.ofNat 32 0x4821) = M (B + BitVec.ofNat 32 0x4821) :=
    K3.at X (by decide) (by decide) (by decide) (Or.inl (by decide))
  rw [e1310', eR0, eR1, e890', eRk, eRk1, act_lbu_low, act_lbu_low, b0, b1]
  have K7 := (K4.trans K5).trans ((act_kp_sb (M := m5.mem) (w := M (B + BitVec.ofNat 32 0x4820)) (d := 0x52C0)
    (by decide) (by decide)).trans (act_kp_sb (w := M (B + BitVec.ofNat 32 0x4821)) (d := 0x52C1)
    (by decide) (by decide)))
  generalize hM7 : memStore8 (memStore8 m5.mem (B + BitVec.ofNat 32 0x52C0) (M (B + BitVec.ofNat 32 0x4820)))
    (B + BitVec.ofNat 32 0x52C1) (M (B + BitVec.ofNat 32 0x4821)) = M7 at K7
  have p7 : ∀ c, 0x52B0 ≤ c → c < 0x52C0 → M7 (B + BitVec.ofNat 32 c) = M4 (B + BitVec.ofNat 32 c) :=
    fun c h1 h2 => by
      rw [← hM7, act_st8_ne (by omega) (by decide) (by omega), act_st8_ne (by omega) (by decide) (by omega),
        hO5 _ (X.ss (by omega) (by decide) (Or.inr (by omega)))]
      exact copyBytes_sep (X.ss (by decide) (by omega) (Or.inr (by omega))) (Nat.le_refl _)
  have rk7 : ∀ o, o < 0x540 → M7 (B + BitVec.ofNat 32 0x52C0 + BitVec.ofNat 32 o) =
      M (B + BitVec.ofNat 32 0x4820 + BitVec.ofNat 32 o) := fun o ho => by
    rw [add_ofNat_assoc, add_ofNat_assoc, ← hM7]
    rcases o with _ | _ | o
    · rw [act_st8_ne (by decide) (by decide) (by decide)]; exact memStore8_same _ _ _
    · exact memStore8_same _ _ _
    · rw [act_st8_ne (by omega) (by decide) (by omega), act_st8_ne (by omega) (by decide) (by omega),
        show 0x52C0 + (o + 1 + 1) = 0x52C2 + o by omega, c5 o (by omega),
        show 0x4820 + (o + 1 + 1) = 0x4822 + o by omega]
  have q7 : ∀ j, j < 4 → ∀ c, c + 4 ≤ 12 → M7 (B + BitVec.ofNat 32 (0x52B4 + c) + BitVec.ofNat 32 j) =
      M (B + BitVec.ofNat 32 (0x52C4 + c) + BitVec.ofNat 32 j) := fun j hj c hc => by
    rw [add_ofNat_assoc, add_ofNat_assoc, p7 _ (by omega) (by omega), Nat.add_assoc, Nat.add_assoc, c4 _ (by omega)]
  have hI7 : ActI B Bf g t v M0 M7 f := hI.mem F X.sB fun x hx => K7 x hx.1 (act_ks hx.2.2.2.2.1 0 0x550 (by decide))
  have hW : ∀ c, c ≤ 0x3A50 → Sep (B + BitVec.ofNat 32 0x130) 0x3920 S sl := fun _ _ =>
    act_sepw (X.sB.sub (c := 0x130) (l := 0x3920) (by decide)) (by omega) (by omega) (by decide)
  refine WP.lui ac_at_914 ?_; wn
  refine WP.aluImm ac_at_916 ?_; wn
  refine WP.alu ac_at_91a ?_; wn
  refine WP.lui ac_at_91c ?_; wn
  refine WP.aluImm ac_at_91e ?_; wn
  refine WP.alu ac_at_922 ?_; wn
  refine act_met (MP := S) (ML := sl) (SP := SP) (SL := SL) (md := md) (sj := sj) X
    (hI7.regs (by act_r) (by act_r) (by act_r)) ac_at_924 ac_at_928 (by decide) (by decide)
    (fun m _ h m' e1 e2 e3 => .inl (by show rmH _ _ _; rw [e1, e2, e3]; exact h))
    (by act_r; rw [BitVec.add_comm]; exact act_spc hI.rsp _ _ rfl)
    (by act_r; rw [BitVec.add_comm]; exact act_spc hI.rsp _ _ rfl)
    (by omega) (by omega) (hW 0 (by decide)) ?_ (by omega) (by omega)
    (act_sepw (X.sB.sub (c := 0x130) (l := 0x3920) (by decide)) (by omega) (by omega) (by decide))
    ?_ ?_ ?_ ?_ hrk (hRk.congr fun o ho => rk7 o ho) hw hB ?_ ?_ hps fun m8 hfr hok herr => ?_
  rotate_right
  · have K8 : ActKp B 0x52B0 0x550 M m8.mem := fun x a b =>
      (hfr x (a.subR (c := 0x130) (l := 0x3920) (by decide))).trans (K7 x a b)
    have hI8 : ActI B Bf g t v M0 m8.mem f :=
      hI.mem F X.sB fun x hx => K8 x hx.1 (act_ks hx.2.2.2.2.1 0 0x550 (by decide))
    have hr8 : memLoad32 m8.mem (acSlot B 0x40) = r :=
      (K8.ld X (c := 0x3A90) (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hr
    wn
    refine WP.aluImm ac_at_92c ?_; wn
    refine WP.alu ac_at_92e ?_; wn
    refine WP.branch ac_at_930 (fun hb => ?_) (fun hb => ?_)
    rotate_left
    · refine WP.jal ac_at_932 (by decide) ?_; wn
      refine act_x6a (hI8.regs (by act_r) (by act_r) (by act_r)) hr8 ?_
      act_r
      revert hb; act_r; intro hb
      simp only [branchTaken, beq_eq_false_iff_ne] at hb
      exact herr hb
    have ha0 : reg m8 a0 &&& 1 = 0 := by
      revert hb; act_r; intro hb; simp only [branchTaken, beq_iff_eq] at hb; exact hb
    wn
    refine WP.aluImm ac_at_936 ?_; wn
    refine WP.branch ac_at_938 (fun hb => ?_) (fun hb => ?_)
    · wn
      refine WP.aluImm ac_at_974 ?_; wn
      refine WP.jal ac_at_978 (by decide) ?_; wn
      refine act_x6a (hI8.regs (by act_r) (by act_r) (by act_r)) hr8 ?_
      act_r
    have hth : thresholdMet md root.md.signed (ascii!"targets") = some true := by
      refine hok ha0 ?_
      revert hb; act_r; intro hb
      simp only [branchTaken, beq_eq_false_iff_ne] at hb; exact hb
    wn
    have h8 : ∀ c, 0x3A50 ≤ c → c < 0x5A70 → m8.mem (B + BitVec.ofNat 32 c) = M7 (B + BitVec.ofNat 32 c) :=
      fun c h1 h2 => hfr _ (X.ss (by omega) (by decide) (Or.inr (by omega)))
    have h864 : memLoad32 m8.mem (acSlot B 0x1864) = BitVec.ofNat 32 sl := by
      rw [show acSlot B 0x1864 = B + BitVec.ofNat 32 (0x52B4 + 0) from rfl, ← hl1,
        show B + BitVec.ofNat 32 0x52C4 = B + BitVec.ofNat 32 (0x52C4 + 0) from rfl]
      refine memLoad32_congr2 fun j hj => ?_
      rw [← q7 j hj 0 (by decide), add_ofNat_assoc]
      exact h8 _ (by omega) (by omega)
    have l1C : memLoad32 m8.mem (acSlot B 0x1C) = memLoad32 M (acSlot B 0x1C) :=
      K8.ld X (c := 0x3A6C) (by decide) (by decide) (by decide) (Or.inl (by decide))
    refine act_93a hROM hR4 hR X (hI8.regs (by act_r) (by act_r) (by act_r)) hr8
      (fun x hx => (K8 x hx.1 (act_ks hx.2.2.2.2.1 0 0x550 (by decide))).trans (hO x hx))
      (by act_r; rw [l1C]; exact K8.doc X (by decide) (Or.inl (by decide)) hdoc)
      (by act_r; exact hs4) (by act_r; exact hs2) h864 hS1 hS2
      (by rw [K8.bf X (by decide) (by omega) (by omega)]; exact hd) (hspec hth)
      ((K8.ld X (c := 0x3A78) (by decide) (by decide) (by decide) (Or.inl (by decide))).trans h28)
      ((K8.ld X (c := 0x3A7C) (by decide) (by decide) (by decide) (Or.inl (by decide))).trans h2C)
      (by act_r) (by act_r; exact hs5) (by act_r; exact hs9) (by act_r; exact hs11)
  · omega
  · rw [memLoad32_congr (M := M4) fun j hj => by rw [add_ofNat_assoc]; exact p7 _ (by omega) (by omega)]; exact w4
  · rw [add_ofNat_assoc, ← hl1]; exact memLoad32_congr2 fun j hj => q7 j hj 0 (by decide)
  · rw [add_ofNat_assoc, ← hq2]; exact memLoad32_congr2 fun j hj => q7 j hj 4 (by decide)
  · rw [add_ofNat_assoc, ← hl2]; exact memLoad32_congr2 fun j hj => q7 j hj 8 (by decide)
  · rw [K7.bf X (by decide) (by omega) (by omega), hd, hmsg]
  · rw [K7.bf X (by decide) (by omega) (by omega)]; exact hsj

end

end C3.RV32.Ac
