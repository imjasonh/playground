import C3BootProofs.Proofs.TufRoleKeysMetFrame
import C3BootProofs.Proofs.TufRoleKeysMetCalls

/-!
# The code of `RoleKeys::met`'s signature checks

`RmCode` adds to `RmCodeA` the code and constants of the hash functions,
the signature parsers, and the verifiers, and `RmEnv` adds it to `RmBase`.
The lemmas here build each callee's environment from the frame.
-/

namespace C3.RV32

open C3.Image C3.Json C3.RV32.P2v C3.RV32.Pv C3.RV32.Sv C3.RV32.P3

set_option maxRecDepth 20000

abbrev ES48 : Word := BitVec.ofNat 32 ecdsaSignature48Address
abbrev ES32 : Word := BitVec.ofNat 32 ecdsaSignature32Address

/-- The `CodeIn` facts of `sha256` and its callees. -/
structure Sha256Code (M : Word → BitVec 8) : Prop where
  cX : CodeIn M (BitVec.ofNat 32 sha256FnAddress) sha256FnCode
  cIV : CodeIn M (BitVec.ofNat 32 shaIVAddress) shaIVData
  cU : CodeIn M (BitVec.ofNat 32 shaUpdateAddress) shaUpdateCode
  cUBlk : CodeIn M (BitVec.ofNat 32 shaUpdateBlocksAddress) shaUpdateBlocksCode
  cF : CodeIn M (BitVec.ofNat 32 shaFinalizeAddress) shaFinalizeCode
  cZ : CodeIn M (BitVec.ofNat 32 shaZero32Address) shaZero32Code
  cFBlk : CodeIn M (BitVec.ofNat 32 shaFinBlockAddress) shaFinBlockCode
  cMs : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  cMS : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cMB : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  cC : CodeIn M (BitVec.ofNat 32 sha256CompressAddress) sha256CompressCode
  cI : CodeIn M (BitVec.ofNat 32 sha256CompressAddress + 0x25A) rangeFromIndexCode
  cK : CodeIn M (BitVec.ofNat 32 shaKAddress) shaKData

/-- The `CodeIn` facts of `ecdsa_signature::<48>` and its callees. -/
structure Es48Code (M : Word → BitVec 8) : Prop where
  cod : CodeIn M ES48 ecdsaSignature48Code
  seq : CodeIn M (ES48 + 0xFFFFFD56) derSequenceCode
  nst : CodeIn M (ES48 + 0xFFFFFFCE) derNestedCode
  elem : CodeIn M (ES48 + 0xFFFFFEEE) derElementCode
  tlv : CodeIn M (ES48 + 0xFFFFFF14) derTlvCode
  pos : CodeIn M (ES48 + 0xFFFFFE1E) derPositiveIntegerCode
  int : CodeIn M (ES48 + 0xFFFFFE90) derIntegerCode
  zip : CodeIn M (ES48 + 0xFFFFFE6E) zipSkipNextCode
  sc : CodeIn M (ES48 + 0x10C) derScalar48Code
  ms : CodeIn M (ES48 + 0xCFE4) memsetCode
  mcs : CodeIn M (ES48 + 0xD04C) memcpyStubCode
  mcb : CodeIn M (ES48 + 0xD054) memcpyBodyCode

/-- The `CodeIn` facts of `ecdsa_signature::<32>` and its callees. -/
structure Es32Code (M : Word → BitVec 8) : Prop where
  cod : CodeIn M ES32 ecdsaSignature32Code
  seq : CodeIn M (ES32 + 0x104) derSequenceCode
  nst : CodeIn M (ES32 + 0x37C) derNestedCode
  elem : CodeIn M (ES32 + 0x29C) derElementCode
  tlv : CodeIn M (ES32 + 0x2C2) derTlvCode
  pos : CodeIn M (ES32 + 0x1CC) derPositiveIntegerCode
  int : CodeIn M (ES32 + 0x23E) derIntegerCode
  zip : CodeIn M (ES32 + 0x21C) zipSkipNextCode
  sc : CodeIn M (ES32 + 0x110) derScalar32Code
  ms : CodeIn M (ES32 + 0xD392) memsetCode
  mcs : CodeIn M (ES32 + 0xD3FA) memcpyStubCode
  mcb : CodeIn M (ES32 + 0xD402) memcpyBodyCode

/-- The code `RoleKeys::met` and its callees run, and the constants they
read. -/
structure RmCode (M : Word → BitVec 8) : Prop where
  a : RmCodeA M
  ev : EvEnv M
  iv : (s5Hv M (BitVec.ofNat 32 (img% sha512IVAddress))).toList = Sha512.h0
  edI : EdM.EdImage M
  edK : EdK.KImage M
  hf : HfEnv M
  sha : Sha256Code M
  es48 : Es48Code M
  es32 : Es32Code M
  p2v : P2vEnv M
  p2k : C3.Models.P256Consts M
  pv : PvEnv7 M

/-- `RmBase`, with the code of the signature checks. -/
structure RmEnv (M0 M1 : Word → BitVec 8) (s F R MP SP : Word) (ML SL : Nat) (g0 : Fin 32 → Word) : Prop
    extends RmBase M0 M1 s F R MP SP ML SL g0 where
  hc : ∀ M : Word → BitVec 8, (∀ x, Sep x 1 s 0x3920 → M x = M0 x) → RmCode M

/-- A halt in a panic. -/
abbrev rmH : Post := fun pc M g => pc = romPrintfEntry ∧ g ra = haltBase + 0x16 ∧ PanicCode M

/-- `rmH`, the `RoleKeys::met` postcondition's halting case, when some
inversion bound fails. -/
abbrev rmHI : Post := fun pc M g => ¬ InvBounds ∧ rmH pc M g

theorem rmQ_haltI {M0 : Word → BitVec 8} {s : Word} {g0 : Fin 32 → Word} {S : Prop} :
    ∀ m, ¬ InvBounds → Halting m → rmQ rmHI M0 s g0 S m.pc m.mem (reg m) := fun _ hB h => .inl ⟨hB, h⟩

section
variable {M0 M1 Mk : Word → BitVec 8} {s F R MP SP : Word} {ML SL : Nat} {g0 : Fin 32 → Word}

theorem RmEnv.code (E : RmEnv M0 M1 s F R MP SP ML SL g0) (hO : Out M1 Mk s 0x38EC) : RmCode Mk :=
  E.hc Mk (E.agree hO)

/-- `sha384`'s frame for a call with `sp = F`. -/
theorem RmEnv.hfF (E : RmEnv M0 M1 s F R MP SP ML SL g0) : F = s + BitVec.ofNat 32 0x34F0 + BitVec.ofNat 32 0x240 := by
  rw [add_ofNat_assoc]; exact E.hF.symm

/-- `ed25519_verify`'s frame for a call with `sp = F`. -/
theorem RmEnv.evF (E : RmEnv M0 M1 s F R MP SP ML SL g0) : F = s + BitVec.ofNat 32 0x2090 + BitVec.ofNat 32 0x16A0 := by
  rw [add_ofNat_assoc]; exact E.hF.symm

theorem RmEnv.evG (E : RmEnv M0 M1 s F R MP SP ML SL g0) : evG (s + BitVec.ofNat 32 0x2090) = s + BitVec.ofNat 32 0x1680 := by
  show s + BitVec.ofNat 32 0x2090 + 0xFFFFF5F0 = _
  rw [BitVec.add_assoc]; rfl

/-- The P-256 verifier's frame: `B = s + 0x1A0`, with `sp = B + 0x3590 = F`. -/
theorem RmEnv.p2F (E : RmEnv M0 M1 s F R MP SP ML SL g0) : F = s + BitVec.ofNat 32 0x1A0 + 0x3590 := by
  rw [show (0x3590 : Word) = BitVec.ofNat 32 0x3590 from rfl, add_ofNat_assoc]; exact E.hF.symm

theorem RmEnv.p2lo (E : RmEnv M0 M1 s F R MP SP ML SL g0) : s + BitVec.ofNat 32 0x1A0 + 0xFFFFFE60 = s := by
  rw [BitVec.add_assoc, show BitVec.ofNat 32 0x1A0 + (0xFFFFFE60 : Word) = 0 by decide, add_lit_zero]

theorem RmEnv.p2fr (E : RmEnv M0 M1 s F R MP SP ML SL g0) : Fr (s + BitVec.ofNat 32 0x1A0) 0x3590 :=
  ⟨by rw [E.SN (by decide)]; have := E.hal; omega, by rw [E.SN (by decide)]; have := E.hlo; omega,
    by rw [E.SN (by decide)]; have := E.hhi; omega, by rw [E.p2lo]; exact tex_sepL E.hds (by decide)⟩

theorem RmEnv.p2ro (E : RmEnv M0 M1 s F R MP SP ML SL g0) : P2vRoSep (s + BitVec.ofNat 32 0x1A0) := by
  unfold P2vRoSep; rw [E.p2lo]; exact tex_sepL E.hro (by decide)

/-- The P-384 verifier's frame: `B = s + 0x1590`, with `sp = B + 0x21A0 = F`. -/
theorem RmEnv.pvF (E : RmEnv M0 M1 s F R MP SP ML SL g0) : F = s + BitVec.ofNat 32 0x1590 + 0x21A0 := by
  rw [show (0x21A0 : Word) = BitVec.ofNat 32 0x21A0 from rfl, add_ofNat_assoc]; exact E.hF.symm

theorem RmEnv.pvlo (E : RmEnv M0 M1 s F R MP SP ML SL g0) :
    s + BitVec.ofNat 32 0x1590 + 0xFFFFFE60 = s + BitVec.ofNat 32 0x13F0 := by
  rw [BitVec.add_assoc]; rfl

theorem RmEnv.pvfr (E : RmEnv M0 M1 s F R MP SP ML SL g0) : Fr (s + BitVec.ofNat 32 0x1590) 0x21A0 :=
  ⟨by rw [E.SN (by decide)]; have := E.hal; omega, by rw [E.SN (by decide)]; have := E.hlo; omega,
    by rw [E.SN (by decide)]; have := E.hhi; omega,
    by rw [E.pvlo]; exact E.hds.sub (c := 0x13F0) (l := 0x2340) (by decide)⟩

/-- `sha256`'s environment for a call with `sp = F`. -/
theorem RmEnv.sha (E : RmEnv M0 M1 s F R MP SP ML SL g0) {M : Word → BitVec 8} (C : Sha256Code M) {out D : Word}
    {n : Nat} (hDw : D.toNat + n ≤ 0x40000000) (hOw : out.toNat + 32 ≤ 0x40000000)
    (sDF : Sep D n (s + BitVec.ofNat 32 0x34C0) 0x270) (sOF : Sep out 32 (s + BitVec.ofNat 32 0x34C0) 0x270) :
    Sha256Env M out D F n := by
  have hw : F + 0xFFFFFD90 = s + BitVec.ofNat 32 0x34C0 := E.Fm (c := 0x270) (by decide) rfl
  have hFn := E.FN (c := 0) (by decide); rw [add_ofNat_zero] at hFn
  refine ⟨C.cX, C.cIV, C.cU, C.cUBlk, C.cF, C.cZ, C.cFBlk, C.cMs, C.cMS, C.cMB, C.cC, C.cI, C.cK, E.halF,
    by have := E.hlo; omega, by have := E.hhi; omega, hDw, hOw, by rw [hw]; exact sDF, by rw [hw]; exact sOF,
    by rw [hw]; exact (E.roS (by decide) (d := 0xF24) (k := 256) (by decide) rfl).symm,
    by rw [hw]; exact (E.roS (by decide) (d := 0x118) (k := 32) (by decide) rfl).symm⟩

/-- `ecdsa_signature::<48>`'s environment for a call with `sp = F`. -/
theorem RmEnv.es48 (E : RmEnv M0 M1 s F R MP SP ML SL g0) {M : Word → BitVec 8} (C : Es48Code M) {out p : Word}
    {n : Nat} (how : out.toNat + 97 ≤ 0x40000000) (hp : 0 < p.toNat) (hpn : p.toNat + n < 2 ^ 32)
    (sOG : Sep out 97 (s + BitVec.ofNat 32 0x35C0) 0x170) (sDG : Sep p n (s + BitVec.ofNat 32 0x35C0) 0x170) :
    ESEnv M ES48 F out p n := by
  have hw : F + 0xFFFFFE90 = s + BitVec.ofNat 32 0x35C0 := E.Fm (c := 0x170) (by decide) rfl
  have hFn := E.FN (c := 0) (by decide); rw [add_ofNat_zero] at hFn
  have hg : ∀ {b : Word} {l : Nat}, 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 → Sep (F + 0xFFFFFE90) 0x170 b l :=
    fun hb hbl => by rw [hw]; exact E.lowS (by decide) hb hbl
  have ho : ∀ {b : Word} {l : Nat}, 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 → Sep out 97 b l :=
    fun hb hbl => lowSep how hb hbl
  exact ⟨by decide, C.cod, C.seq, C.nst, C.elem, C.tlv, C.pos, C.int, C.zip, C.sc, C.ms, C.mcs, C.mcb,
    by have := E.halF; omega, by have := E.hlo; omega, by omega, hp, hpn,
    hg (by decide) (by decide), hg (by decide) (by decide), hg (by decide) (by decide), hg (by decide) (by decide),
    hg (by decide) (by decide), hg (by decide) (by decide), hg (by decide) (by decide), hg (by decide) (by decide),
    hg (by decide) (by decide), hg (by decide) (by decide), hg (by decide) (by decide), hg (by decide) (by decide),
    ho (by decide) (by decide), ho (by decide) (by decide), ho (by decide) (by decide),
    by rw [hw]; exact sOG, by rw [hw]; exact sDG⟩

/-- `ecdsa_signature::<32>`'s environment for a call with `sp = F`. -/
theorem RmEnv.es32 (E : RmEnv M0 M1 s F R MP SP ML SL g0) {M : Word → BitVec 8} (C : Es32Code M) {out p : Word}
    {n : Nat} (how : out.toNat + 65 ≤ 0x40000000) (hp : 0 < p.toNat) (hpn : p.toNat + n < 2 ^ 32)
    (sOG : Sep out 65 (s + BitVec.ofNat 32 0x3600) 0x130) (sDG : Sep p n (s + BitVec.ofNat 32 0x3600) 0x130) :
    ES32Env M ES32 F out p n := by
  have hw : F + 0xFFFFFED0 = s + BitVec.ofNat 32 0x3600 := E.Fm (c := 0x130) (by decide) rfl
  have hFn := E.FN (c := 0) (by decide); rw [add_ofNat_zero] at hFn
  have hg : ∀ {b : Word} {l : Nat}, 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 → Sep (F + 0xFFFFFED0) 0x130 b l :=
    fun hb hbl => by rw [hw]; exact E.lowS (by decide) hb hbl
  have ho : ∀ {b : Word} {l : Nat}, 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 → Sep out 65 b l :=
    fun hb hbl => lowSep how hb hbl
  exact ⟨by decide, C.cod, C.seq, C.nst, C.elem, C.tlv, C.pos, C.int, C.zip, C.sc, C.ms, C.mcs, C.mcb,
    by have := E.halF; omega, by have := E.hlo; omega, by omega, hp, hpn,
    hg (by decide) (by decide), hg (by decide) (by decide), hg (by decide) (by decide), hg (by decide) (by decide),
    hg (by decide) (by decide), hg (by decide) (by decide), hg (by decide) (by decide), hg (by decide) (by decide),
    hg (by decide) (by decide), hg (by decide) (by decide), hg (by decide) (by decide), hg (by decide) (by decide),
    ho (by decide) (by decide), ho (by decide) (by decide), ho (by decide) (by decide),
    by rw [hw]; exact sOG, by rw [hw]; exact sDG⟩

theorem RmEnv.hf (E : RmEnv M0 M1 s F R MP SP ML SL g0) {M : Word → BitVec 8} (C : HfEnv M) {out p : Word} {len : Nat}
    (sP : Sep p len (s + BitVec.ofNat 32 0x30D0) 0x660) (sOut : Sep out 48 (s + BitVec.ofNat 32 0x30D0) 0x660)
    (hp : p.toNat + len ≤ 0x40000000) (hout : out.toNat + 48 ≤ 0x40000000) :
    HfCtx M (s + BitVec.ofNat 32 0x34F0) out p len := by
  have hw : hfG (s + BitVec.ofNat 32 0x34F0) = s + BitVec.ofNat 32 0x30D0 := by
    show s + BitVec.ofNat 32 0x34F0 + 0xFFFFFBE0 = _
    rw [BitVec.add_assoc]; rfl
  refine ⟨C, by rw [E.SN (by decide)]; have := E.hal; omega, by rw [E.SN (by decide)]; have := E.hlo; omega,
    by rw [E.SN (by decide)]; have := E.hhi; omega, ?_, by rw [hw]; exact sP, by rw [hw]; exact sOut, hp, hout⟩
  rw [hw]; exact (E.hro.sub (c := 0x30D0) (l := 0x660) (by decide)).symm

theorem RmEnv.ev (E : RmEnv M0 M1 s F R MP SP ML SL g0) {M : Word → BitVec 8} (C : RmCode M) {pk sig msg : Word}
    {len : Nat} (sPk : Sep pk 32 (s + BitVec.ofNat 32 0x1680) 0x20B0) (sSig : Sep sig 64 (s + BitVec.ofNat 32 0x1680) 0x20B0)
    (sMsg : Sep msg len (s + BitVec.ofNat 32 0x1680) 0x20B0) (hpk : pk.toNat + 32 < 2 ^ 32)
    (hsig : sig.toNat + 64 < 2 ^ 32) (hmsgW : msg.toNat + len ≤ 0x40000000) (hlen : len < 2 ^ 31) :
    EvCtx M (s + BitVec.ofNat 32 0x2090) pk sig msg len := by
  refine ⟨C.ev, by rw [E.SN (by decide)]; have := E.hal; omega, by rw [E.SN (by decide)]; have := E.hlo; omega,
    by rw [E.SN (by decide)]; have := E.hhi; omega, ?_, by rw [E.evG]; exact sPk, by rw [E.evG]; exact sSig,
    by rw [E.evG]; exact sMsg, hpk, hsig, by omega, hmsgW, hlen, C.iv⟩
  rw [E.evG]; exact (E.hro.sub (c := 0x1680) (l := 0x20B0) (by decide)).symm

end

end C3.RV32
