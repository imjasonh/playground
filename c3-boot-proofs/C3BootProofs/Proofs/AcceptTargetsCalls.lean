import C3BootProofs.Proofs.AcceptTargetsLib

/-!
# The `targets.json` stage's calls

`ActX` holds what the stage knows of its frame, `Buffers`, and the callees'
code. The wrappers here call each callee from the closure with the stage's
`sp` and discharge the callee's separation conditions from `ActX`.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.Json

set_option maxRecDepth 200000

/-- What the stage knows of its frame at `B`, `Buffers` at `Bf`, and the
callees' code in memory that agrees with `M0` outside them. -/
structure ActX (romBase : Word) (romCode : List Nat) (B Bf : Word) (M0 : Word → BitVec 8) : Prop where
  F : Fr B 0x5A70
  sB : Sep B 0x5A70 Bf acBufLen
  sRo : Sep B 0x5A70 (BitVec.ofNat 32 roWindowAddress) roWindowSize
  sRom : Sep B 0x5A70 romBase romCode.length
  sBR : Sep Bf acBufLen romBase romCode.length
  bal : Bf.toNat % 4 = 0
  bhi : Bf.toNat + acBufLen ≤ 0x40000000
  env : ∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → AcTargetsEnv romBase romCode M

section
variable {romBase : Word} {romCode : List Nat} {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8}

theorem ActX.E (X : ActX romBase romCode B Bf M0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    (hI : ActI B Bf g t v M0 M f) : AcTargetsEnv romBase romCode M := X.env M hI.out

theorem ActX.lo (X : ActX romBase romCode B Bf M0) {c : Nat} (h : c ≤ 0x5A70) :
    (B + BitVec.ofNat 32 c).toNat = B.toNat + c := X.F.at c h

theorem ActX.al (X : ActX romBase romCode B Bf M0) {c : Nat} (h : c ≤ 0x5A70) (h4 : c % 4 = 0) :
    (B + BitVec.ofNat 32 c).toNat % 4 = 0 := by
  have := X.F.al; rw [X.lo h]; omega

theorem ActX.low (X : ActX romBase romCode B Bf M0) {c n : Nat} (h : c + n ≤ 0x5A70) :
    (B + BitVec.ofNat 32 c).toNat + n ≤ 0x40000000 := by
  have := X.F.hi; rw [X.lo (by omega)]; omega

/-- Two stretches of the frame apart. -/
theorem ActX.ss (X : ActX romBase romCode B Bf M0) {a n b k : Nat} (ha : a + n ≤ 0x5A70) (hb : b + k ≤ 0x5A70)
    (h : a + n ≤ b ∨ b + k ≤ a) : Sep (B + BitVec.ofNat 32 a) n (B + BitVec.ofNat 32 b) k := by
  have := X.F.hi
  refine act_sep ?_ ?_ ?_
  · rw [X.lo (by omega), X.lo (by omega)]; omega
  · rw [X.lo (by omega)]; omega
  · rw [X.lo (by omega)]; omega

/-- A stretch of the frame and code above 0x40000000. -/
theorem ActX.sc (X : ActX romBase romCode B Bf M0) {a n : Nat} (ha : a + n ≤ 0x5A70) {b : Word} {k : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hbk : b.toNat + k ≤ 2 ^ 32) : Sep (B + BitVec.ofNat 32 a) n b k :=
  X.F.sepHi ha hb hbk

/-- A stretch of the frame and the read-only window. -/
theorem ActX.sro (X : ActX romBase romCode B Bf M0) {a n : Nat} (ha : a + n ≤ 0x5A70) :
    Sep (B + BitVec.ofNat 32 a) n (BitVec.ofNat 32 roWindowAddress) roWindowSize :=
  X.sRo.sub ha

/-- A stretch of the frame and one of `Buffers`. -/
theorem ActX.sbf (X : ActX romBase romCode B Bf M0) {a n : Nat} (ha : a + n ≤ 0x5A70) {c k : Nat}
    (hc : c + k ≤ acBufLen) : Sep (B + BitVec.ofNat 32 a) n (Bf + BitVec.ofNat 32 c) k :=
  (X.sB.sub ha).subR hc

/-- A stretch of `Buffers` below 0x40000000. -/
theorem ActX.bfLo (X : ActX romBase romCode B Bf M0) {c : Nat} (h : c ≤ acBufLen) :
    (Bf + BitVec.ofNat 32 c).toNat = Bf.toNat + c := by
  have := X.bhi; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem ActX.bfc (X : ActX romBase romCode B Bf M0) {c n : Nat} (h : c + n ≤ acBufLen) {b : Word} {k : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hbk : b.toNat + k ≤ 2 ^ 32) : Sep (Bf + BitVec.ofNat 32 c) n b k :=
  lowSep (by have := X.bhi; rw [X.bfLo (by omega)]; omega) hb hbk

end

/-! ## Calls -/

section
variable {romBase : Word} {romCode : List Nat} {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8}
  {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- A call to `memcpy(dst, src, N)` from the closure with `sp` at the frame. -/
theorem act_mc (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f) {hi lo dst src : Word} {N : Nat}
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 memcpyStubAddress) (hev : (off + 8) % 2 = 0)
    (h0 : f a0 = dst) (ha1 : f a1 = src) (ha2 : f a2 = BitVec.ofNat 32 N)
    (hdl : dst.toNat + N ≤ 0x40000000) (hsl : src.toNat + N ≤ 0x40000000)
    (hdF : Sep dst N (B + BitVec.ofNat 32 0x3A40) 16) (hsF : Sep src N (B + BitVec.ofNat 32 0x3A40) 16)
    (hds : Sep dst N src N)
    (k : ∀ m2 : Machine, Out (copyBytes M dst src N) m2.mem (B + BitVec.ofNat 32 0x3A40) 16 →
      WP bootMainClosure0Code AC Q m2.mem (off + 8)
        (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  have E := X.E hI
  have hF := X.F
  refine WP.callMemcpy h1 h2 htgt (by decide) hev E.mcs ⟨E.mcb, lowSep hdl (by decide) (by decide),
      X.sc (by decide) (by decide) (by decide), hdF, hsF, hds, X.al (by decide) (by decide),
      by rw [X.lo (by decide)]; have := hF.hi; omega, by omega, by omega⟩
    h0 ha1 ha2 ?_ (X.sc (by decide) (by decide) (by decide)) (lowSep hdl (by decide) (by decide)) k
  rw [hI.rsp, BitVec.add_assoc]; rfl

/-- A call to `memset(dst, 0, n)` from the closure. -/
theorem act_ms (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f) {hi lo dst : Word} {n : Nat}
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 memsetAddress) (hev : (off + 8) % 2 = 0)
    (h0 : f a0 = dst) (ha1 : f a1 = 0) (ha2 : f a2 = BitVec.ofNat 32 n) (hdl : dst.toNat + n ≤ 0x40000000)
    (k : ∀ m2 : Machine, m2.mem = fillBytes M dst 0 n →
      WP bootMainClosure0Code AC Q m2.mem (off + 8)
        (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 tpsMsClob)) :
    WP bootMainClosure0Code AC Q M off f :=
  WP.callMemsetT h1 h2 htgt (by decide) hev (X.E hI).mset h0 ha1 ha2 (by omega)
    (lowSep hdl (by decide) (by decide)) (lowSep hdl (by decide) (by decide)) fun m2 h => k m2 (by rw [h]; rfl)

/-- A call to `memcmp(p, q, n)` from the closure. -/
theorem act_cmp (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f) {hi lo p q : Word} {n : Nat}
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 memcmpAddress) (hev : (off + 8) % 2 = 0)
    (h0 : f a0 = p) (ha1 : f a1 = q) (ha2 : f a2 = BitVec.ofNat 32 n) (hn : n < 2 ^ 32)
    (k : ∀ m2 : Machine, (reg m2 a0 = 0 ↔ memBytes M p n = memBytes M q n) → m2.mem = M →
      WP bootMainClosure0Code AC Q m2.mem (off + 8)
        (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP bootMainClosure0Code AC Q M off f :=
  WP.callMemcmpIff h1 h2 htgt (by decide) hev (X.E hI).mcmp h0 ha1 ha2 hn k

/-- A call to `field(key)` from the closure, with the result at `out` in the
frame and the key in the read-only window. -/
theorem act_fld (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f) {hi lo p kq : Word}
    {n kl c : Nat}
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 jsonFieldAddress) (hev : (off + 8) % 2 = 0)
    (h0 : f a0 = B + BitVec.ofNat 32 c) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n) (ha3 : f a3 = kq)
    (ha4 : f a4 = BitVec.ofNat 32 kl) (hc : 0x3A50 ≤ c ∧ c + 8 ≤ 0x5A70 ∧ c % 4 = 0) (hkl : kl < 2 ^ 32)
    (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n < 2 ^ 32) (hSp : Sep (B + BitVec.ofNat 32 0x394C) 260 p n)
    (hSk : Sep (B + BitVec.ofNat 32 0x394C) 260 kq kl)
    (k : ∀ m2 : Machine, FieldResF M m2.mem (B + BitVec.ofNat 32 c) (B + BitVec.ofNat 32 0x394C) 260
        (fieldRes p (objField (memBytes M p n) (memBytes M kq kl))) →
      WP bootMainClosure0Code AC Q m2.mem (off + 8)
        (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  have hF := X.F
  refine WP.callField h1 h2 htgt (by decide) hev (X.E hI).fld h0 ha1 ha2 ha3 ha4 ?_ (X.al (by decide) (by decide))
    (X.al (by omega) hc.2.2) (by rw [X.lo (by decide)]; have := hF.hi; omega) hkl hp0 hpn
    (tuf_fieldSep (X.low (by decide)) (X.sro (by decide))) hSp hSk (X.ss (by omega) (by decide) (Or.inr (by omega)))
    (X.sc (by omega) (by decide) (by decide)) (X.sc (by decide) (by decide) (by decide))
    (X.sc (by omega) (by decide) (by decide)) k
  rw [hI.rsp, add_ofNat_assoc]; rfl

/-- A call to `get(key)` from the closure. -/
theorem act_get (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f) {hi lo p kq : Word}
    {n kl c : Nat}
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 jsonFieldAddress + 0x16C)
    (hev : (off + 8) % 2 = 0)
    (h0 : f a0 = B + BitVec.ofNat 32 c) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n) (ha3 : f a3 = kq)
    (ha4 : f a4 = BitVec.ofNat 32 kl) (hc : 0x3A50 ≤ c ∧ c + 12 ≤ 0x5A70 ∧ c % 4 = 0) (hkl : kl < 2 ^ 32)
    (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n < 2 ^ 32) (hSp : Sep (B + BitVec.ofNat 32 0x396C) 228 p n)
    (hSk : Sep (B + BitVec.ofNat 32 0x396C) 228 kq kl)
    (k : ∀ m2 : Machine, GetResF M m2.mem (B + BitVec.ofNat 32 c) (B + BitVec.ofNat 32 0x396C) 228
        (getRes p (objGet (memBytes M p n) (memBytes M kq kl))) →
      WP bootMainClosure0Code AC Q m2.mem (off + 8)
        (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  have hF := X.F
  refine WP.callGet h1 h2 htgt (by decide) hev (X.E hI).fld.get h0 ha1 ha2 ha3 ha4 ?_ (X.al (by decide) (by decide))
    (X.al (by omega) hc.2.2) (by rw [X.lo (by decide)]; have := hF.hi; omega) hkl hp0 hpn
    (tuf_fieldSep (X.low (by decide)) (X.sro (by decide))).get hSp hSk
    (X.ss (by omega) (by decide) (Or.inr (by omega)))
    (X.sc (by omega) (by decide) (by decide)) (X.sc (by decide) (by decide) (by decide))
    (X.sc (by omega) (by decide) (by decide)) k
  rw [hI.rsp, add_ofNat_assoc]; rfl

/-- A call to `parse_metadata` from the closure. -/
theorem act_pm (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f) {hi lo p kq : Word}
    {n kl c : Nat}
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = TPM) (hev : (off + 8) % 2 = 0)
    (h0 : f a0 = B + BitVec.ofNat 32 c) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n) (ha3 : f a3 = kq)
    (ha4 : f a4 = BitVec.ofNat 32 kl) (hc : 0x3A50 ≤ c ∧ c + 16 ≤ 0x5A70 ∧ c % 4 = 0) (hn : n < 2 ^ 31)
    (hkl : kl < 2 ^ 32) (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n < 2 ^ 32)
    (hSp : Sep (B + BitVec.ofNat 32 0x383C) 532 p n) (hSk : Sep (B + BitVec.ofNat 32 0x383C) 532 kq kl)
    (k : ∀ m2 : Machine, PmRes M m2.mem (B + BitVec.ofNat 32 0x383C) (B + BitVec.ofNat 32 c)
        (pmRes p (pmModel (memBytes M p n) (memBytes M kq kl))) →
      WP bootMainClosure0Code AC Q m2.mem (off + 8)
        (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  refine WP.callPm h1 h2 htgt hev (X.E hI).pm h0 ha1 ha2 ha3 ha4 ?_ (X.al (by decide) (by decide))
    (X.low (by decide)) (X.sro (by decide)) (X.al (by omega) hc.2.2) (X.low (by omega))
    (X.ss (by omega) (by decide) (Or.inr (by omega))) hn hp0 hpn hSp hkl hSk
    (X.sc (by decide) (by decide) (by decide)) (X.sc (by omega) (by decide) (by decide)) k
  rw [hI.rsp, add_ofNat_assoc]; rfl

/-- A call to `Value::u64` from the closure. -/
theorem act_u64 (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f) {hi lo p : Word} {n c : Nat}
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = TPR_JU) (hev : (off + 8) % 2 = 0)
    (h0 : f a0 = B + BitVec.ofNat 32 c) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (hc : 0x3A50 ≤ c ∧ c + 16 ≤ 0x5A70 ∧ c % 4 = 0) (hn : n < 2 ^ 32)
    (hSp : Sep (B + BitVec.ofNat 32 0x3A30) 32 p n)
    (k : ∀ m2 : Machine, U64ResF M m2.mem (B + BitVec.ofNat 32 c) (B + BitVec.ofNat 32 0x3A30) 32
        (u64Val (memBytes M p n)) →
      WP bootMainClosure0Code AC Q m2.mem (off + 8)
        (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  have E := X.E hI
  refine WP.callU64 h1 h2 htgt hev E.u64 E.aad h0 ha1 ha2 ?_ hn (X.al (by decide) (by decide))
    (X.al (by omega) hc.2.2) (X.low (by decide)) hSp (X.ss (by omega) (by decide) (Or.inr (by omega)))
    (X.low (by omega)) (X.sc (by decide) (by decide) (by decide)) (X.sc (by omega) (by decide) (by decide)) k
  rw [hI.rsp, add_ofNat_assoc]; rfl

/-- A call to SHA-256 from the closure. -/
theorem act_sha (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f) {hi lo p : Word} {n c : Nat}
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 sha256FnAddress) (hev : (off + 8) % 2 = 0)
    (h0 : f a0 = B + BitVec.ofNat 32 c) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (hc : 0x3A50 ≤ c ∧ c + 32 ≤ 0x5A70) (hn : n < 2 ^ 31) (hpl : p.toNat + n ≤ 0x40000000)
    (hSp : Sep p n (B + BitVec.ofNat 32 0x37E0) 0x270)
    (k : ∀ m2 : Machine, memBytes m2.mem (B + BitVec.ofNat 32 c) 32 = sha256 (memBytes M p n) →
      (∀ x, Sep x 1 (B + BitVec.ofNat 32 0x37E0) 0x270 → Sep x 1 (B + BitVec.ofNat 32 c) 32 → m2.mem x = M x) →
      WP bootMainClosure0Code AC Q m2.mem (off + 8)
        (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  have E := X.E hI
  have hF := X.F
  have e : B + 0x3A50 + 0xFFFFFD90 = B + BitVec.ofNat 32 0x37E0 := by
    rw [BitVec.add_assoc]; rfl
  refine WP.callSha256M (sp0 := B + 0x3A50) h1 h2 htgt hev ?_ hI.rsp h0 ha1 ha2 hn
    (by rw [e]; exact X.sc (by decide) (by decide) (by decide)) (X.sc (by omega) (by decide) (by decide))
    (fun m2 hs hm => k m2 hs (by rw [← e]; exact hm))
  refine ⟨E.sha.cX, E.sha.cIV, E.sha.cU, E.sha.cUBlk, E.sha.cF, E.sha.cZ, E.sha.cFBlk, E.sha.cMs, E.sha.cMS,
    E.sha.cMB, E.sha.cC, E.sha.cI, E.sha.cK, ?_, ?_, ?_, hpl, X.low (by omega), ?_, ?_, ?_, ?_⟩
  · show (B + BitVec.ofNat 32 0x3A50).toNat % 16 = 0
    have := hF.al; rw [X.lo (by decide)]; omega
  · show 0x270 ≤ (B + BitVec.ofNat 32 0x3A50).toNat
    have := hF.lo; rw [X.lo (by decide)]; omega
  · show (B + BitVec.ofNat 32 0x3A50).toNat ≤ 0x40000000
    have := X.low (c := 0x3A50) (n := 0) (by decide); omega
  · rw [e]; exact hSp
  · rw [e]; exact X.ss (by omega) (by decide) (Or.inr (by omega))
  · rw [e]; exact (tuf_sep_ro (X.sro (a := 0x37E0) (n := 0x270) (by decide)) (by decide) (by decide)).symm
  · rw [e]; exact (tuf_sep_ro (X.sro (a := 0x37E0) (n := 0x270) (by decide)) (by decide) (by decide)).symm

end

end C3.RV32.Ac
