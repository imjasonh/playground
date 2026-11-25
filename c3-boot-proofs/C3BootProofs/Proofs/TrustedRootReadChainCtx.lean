import C3BootProofs.Proofs.TrustedRootReadChainAt
import C3BootProofs.Proofs.TrustedRootReadChainModel
import C3BootProofs.Proofs.TrustedRootDecode
import C3BootProofs.Proofs.Arr32Eq
import C3BootProofs.Proofs.SliceEq
import C3BootProofs.Proofs.MemcpyAny
import C3BootProofs.Proofs.Fs384Main

/-!
# The frame of `trusted_root::read_chain`

`read_chain`'s frame is 0x180 bytes at `F`, with `ra` and `s0`–`s11` saved
in its top 0x34 bytes. `p384::from_sec1_bytes` reaches deepest below it,
0x5C0 bytes, so the stack region is the 0x740 bytes at `G = F - 0x5C0`.
Besides the stack, `read_chain` writes only the scratch slice at `fr`, the
scratch buffer that the slice holds, and its result at `out`.

`RcCtx` collects the facts about the entry that every block of the proof
uses, `RcRegs` the registers that the body keeps, and `RcMemInv` the
memory between the prologue and the epilogue. `RcCtx.call` is the call of
any callee whose stack is below `F` and whose writes stay in the stack
region, the scratch slice, and the buffer.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

abbrev TRC : Word := BitVec.ofNat 32 trustedRootReadChainAddress
abbrev RJE : Word := BitVec.ofNat 32 jsonElementsAddress
abbrev RSW : Word := BitVec.ofNat 32 jsonSkipWsAddress
abbrev RJN : Word := BitVec.ofNat 32 jsonNextElementAddress
abbrev RDE : Word := BitVec.ofNat 32 derElementAddress
abbrev RDN : Word := BitVec.ofNat 32 derNestedAddress
abbrev RDS : Word := BitVec.ofNat 32 derSequenceAddress
abbrev RDB : Word := BitVec.ofNat 32 derBitStringAddress
abbrev RDO : Word := BitVec.ofNat 32 derOptionalAddress
abbrev RDA : Word := BitVec.ofNat 32 derAlgorithmAddress
abbrev ROI : Word := BitVec.ofNat 32 derOidAddress
abbrev RSE : Word := BitVec.ofNat 32 sliceEqAddress
abbrev RES : Word := BitVec.ofNat 32 equalSameLengthAddress
abbrev RMC : Word := BitVec.ofNat 32 memcmpAddress
abbrev RSN : Word := BitVec.ofNat 32 sliceNeAddress

/-- The address of the key `validFor`. -/
abbrev rcValidForKey : Word := BitVec.ofNat 32 (img% b64AlphabetAddress + 0x48)
/-- The address of the key `certChain`. -/
abbrev rcCertChainKey : Word := BitVec.ofNat 32 (img% svOidPrime256v1Address + 0x3D)
/-- The address of the key `certificates`. -/
abbrev rcCertsKey : Word := BitVec.ofNat 32 (img% svOidPrime256v1Address + 0x46)
/-- The address of the key `rawBytes`. -/
abbrev rcRawKey : Word := BitVec.ofNat 32 (img% u2MaxAddress + 0x8)
/-- The address of the contents of the OID `secp384r1`. -/
abbrev rcCurveKey : Word := BitVec.ofNat 32 (img% b64AlphabetAddress + 0x40)
/-- The address of the contents of the OID `id-ecPublicKey`. -/
abbrev rcEcKey : Word := BitVec.ofNat 32 (img% svOidEcPublicKeyAddress)

/-- `read_chain`, the functions it calls, and the read-only data they
read. -/
structure RcCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M TRC trustedRootReadChainCode
  tvf : TvfCode M
  dec : TrDecCode M
  je : CodeIn M RJE jsonElementsCode
  sw : CodeIn M RSW jsonSkipWsCode
  jn : CodeIn M RJN jsonNextElementCode
  ri : RiCode M (RJN + 0xFFFFF7E0)
  del : CodeIn M RDE derElementCode
  tlv : CodeIn M TLV derTlvCode
  nst : CodeIn M RDN derNestedCode
  dsq : CodeIn M RDS derSequenceCode
  dbs : CodeIn M RDB derBitStringCode
  dop : CodeIn M RDO derOptionalCode
  dal : CodeIn M RDA derAlgorithmCode
  oid : CodeIn M ROI derOidCode
  xrt : CodeIn M XRT x509ReadTimeCode
  gnt : CodeIn M GNT generalizedTimeCode
  seq : CodeIn M RSE sliceEqCode
  esl : CodeIn M RES equalSameLengthCode
  mcm : CodeIn M RMC memcmpCode
  sne : CodeIn M RSN sliceNeCode
  fs : Fs.FsCode M
  p3 : P3.P3Data M
  kv : memBytes M rcValidForKey 8 = ascii!"validFor"
  kc : memBytes M rcCertChainKey 9 = ascii!"certChain"
  kl : memBytes M rcCertsKey 12 = ascii!"certificates"
  kr : memBytes M rcRawKey 8 = ascii!"rawBytes"
  ks : memBytes M tvfStartKey 5 = ascii!"start"
  ke : memBytes M tvfEndKey 3 = ascii!"end"
  kp : memBytes M rcCurveKey 5 = oidSecp384r1
  ko : memBytes M rcEcKey 7 = oidEcPublicKey

/-- A range apart from the read-only window is apart from any range in
it. -/
theorem rc_roSub {s a : Word} {k l : Nat} (hro : Sep s k TVF_RO 0x1400)
    (h : roWindowAddress ≤ a.toNat ∧ a.toNat + l ≤ roWindowAddress + 0x1400) : Sep s k a l := by
  have := hro.subR (c := a.toNat - roWindowAddress) (l := l) (by omega)
  rwa [show TVF_RO + BitVec.ofNat 32 (a.toNat - roWindowAddress) = a from by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := a.isLt
    rw [show roWindowAddress = 0x3fcc4000 from rfl] at h ⊢
    omega] at this

theorem RcCode.out {M M' : Word → BitVec 8} {s : Word} {k : Nat} (C : RcCode M) (hO : Out M M' s k)
    (hw : s.toNat + k ≤ 0x40000000) (hro : Sep s k TVF_RO 0x1400) : RcCode M' :=
  { self := hO.codeIn C.self (lowSep hw (by decide) (by decide))
    tvf := C.tvf.out hO hw hro
    dec := C.dec.hi (tvf_hiOut hO hw)
    je := hO.codeIn C.je (lowSep hw (by decide) (by decide))
    sw := hO.codeIn C.sw (lowSep hw (by decide) (by decide))
    jn := hO.codeIn C.jn (lowSep hw (by decide) (by decide))
    ri := C.ri.out hO
      ⟨lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide),
        lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide),
        lowSep hw (by decide) (by decide), rc_roSub hro (by decide), rc_roSub hro (by decide)⟩
    del := hO.codeIn C.del (lowSep hw (by decide) (by decide))
    tlv := hO.codeIn C.tlv (lowSep hw (by decide) (by decide))
    nst := hO.codeIn C.nst (lowSep hw (by decide) (by decide))
    dsq := hO.codeIn C.dsq (lowSep hw (by decide) (by decide))
    dbs := hO.codeIn C.dbs (lowSep hw (by decide) (by decide))
    dop := hO.codeIn C.dop (lowSep hw (by decide) (by decide))
    dal := hO.codeIn C.dal (lowSep hw (by decide) (by decide))
    oid := hO.codeIn C.oid (lowSep hw (by decide) (by decide))
    xrt := hO.codeIn C.xrt (lowSep hw (by decide) (by decide))
    gnt := hO.codeIn C.gnt (lowSep hw (by decide) (by decide))
    seq := hO.codeIn C.seq (lowSep hw (by decide) (by decide))
    esl := hO.codeIn C.esl (lowSep hw (by decide) (by decide))
    mcm := hO.codeIn C.mcm (lowSep hw (by decide) (by decide))
    sne := hO.codeIn C.sne (lowSep hw (by decide) (by decide))
    fs := C.fs.hi (tvf_hiOut hO hw)
    p3 := ⟨hO.codeIn C.p3.params (rc_roSub hro (by decide)), hO.codeIn C.p3.ca (rc_roSub hro (by decide)),
      hO.codeIn C.p3.cb (rc_roSub hro (by decide))⟩
    kv := (hO.bytes (rc_roSub hro (by decide))).trans C.kv
    kc := (hO.bytes (rc_roSub hro (by decide))).trans C.kc
    kl := (hO.bytes (rc_roSub hro (by decide))).trans C.kl
    kr := (hO.bytes (rc_roSub hro (by decide))).trans C.kr
    ks := (hO.bytes (rc_roSub hro (by decide))).trans C.ks
    ke := (hO.bytes (rc_roSub hro (by decide))).trans C.ke
    kp := (hO.bytes (rc_roSub hro (by decide))).trans C.kp
    ko := (hO.bytes (rc_roSub hro (by decide))).trans C.ko }

theorem rc_sep_of_nlt {x b : Word} {k : Nat} (h : ¬ (x - b).toNat < k) : Sep b k x 1 := by
  intro i hi j hj e
  have hj0 : j = 0 := by omega
  subst hj0
  rw [add_ofNat_zero] at e
  apply h
  rw [← e, BitVec.add_comm b, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hi

theorem rc_nlt_of_sep {x b : Word} {k : Nat} (h : Sep x 1 b k) : ¬ (x - b).toNat < k := fun hlt => by
  have e := sub_eq_ofNat (k := (x - b).toNat) (x - b).isLt rfl
  have := h 0 (by decide) (x - b).toNat hlt
  rw [add_ofNat_zero] at this
  exact this e

/-- A memory that agrees with `M0` outside a range and where `Q` holds
is `M0` changed in the range, then changed where `Q` fails. -/
theorem rc_split {M0 M : Word → BitVec 8} {a : Word} {k : Nat} {Q : Word → Prop}
    (h : ∀ x, Sep a k x 1 → Q x → M x = M0 x) :
    ∃ M1, Out M0 M1 a k ∧ ∀ x, Q x → M x = M1 x := by
  refine ⟨fun x => if (x - a).toNat < k then M x else M0 x, fun x hx => ?_, fun x hx => ?_⟩
  · exact ite_eq_right_of_eq_false _ _ (eq_false (rc_nlt_of_sep hx))
  · by_cases hlt : (x - a).toNat < k
    · exact (ite_eq_left_of_eq_true _ _ (eq_true hlt)).symm
    · show M x = if (x - a).toNat < k then M x else M0 x
      rw [ite_eq_right_of_eq_false _ _ (eq_false hlt)]
      exact h x (rc_sep_of_nlt hlt) hx

/-- `RcCode` holds in a memory that agrees with one where it holds outside
three ranges below `0x40000000` and apart from the read-only window. -/
theorem RcCode.out3 {M0 M : Word → BitVec 8} {a b c : Word} {ka kb kc : Nat} (C : RcCode M0)
    (h : ∀ x, Sep a ka x 1 → Sep b kb x 1 → Sep c kc x 1 → M x = M0 x)
    (ha : a.toNat + ka ≤ 0x40000000) (hb : b.toNat + kb ≤ 0x40000000) (hc : c.toNat + kc ≤ 0x40000000)
    (ra : Sep a ka TVF_RO 0x1400) (rb : Sep b kb TVF_RO 0x1400) (rc : Sep c kc TVF_RO 0x1400) : RcCode M := by
  obtain ⟨M1, h1, h1'⟩ := rc_split (M0 := M0) (M := M) (Q := fun x => Sep b kb x 1 ∧ Sep c kc x 1)
    (fun x xa xbc => h x xa xbc.1 xbc.2)
  obtain ⟨M2, h2, h2'⟩ := rc_split (M0 := M1) (M := M) (Q := fun x => Sep c kc x 1)
    (fun x xb xc => h1' x ⟨xb, xc⟩)
  exact ((C.out h1 ha ra).out h2 hb rb).out (fun x hx => h2' x hx.symm) hc rc

/-- The facts about `read_chain`'s entry that every block of its proof
uses. `G` is the bottom of the stack region, `F` the frame, `out` the
result, `fr` the scratch slice, which holds the `fl` bytes at `fp`, `p` and
`n` the entry's bytes, and `g0` the registers at entry. -/
structure RcCtx (M0 : Word → BitVec 8) (G F out fr fp : Word) (fl : Nat) (p : Word) (n : Nat)
    (g0 : Fin 32 → Word) : Prop where
  code : RcCode M0
  fg : G + BitVec.ofNat 32 0x5C0 = F
  ga : G.toNat % 16 = 0
  gw : G.toNat + 0x740 ≤ 0x40000000
  f384 : P3.Fr (G + BitVec.ofNat 32 0x1A0) 0x420
  ro : Sep G 0x740 TVF_RO 0x1400
  oa : out.toNat % 4 = 0
  ow : out.toNat + 0x40 ≤ 0x40000000
  og : Sep out 0x40 G 0x740
  ofr : Sep out 0x40 fr 8
  ofp : Sep out 0x40 fp fl
  fa : fr.toNat % 4 = 0
  fw : fr.toNat + 8 ≤ 0x40000000
  frg : Sep fr 8 G 0x740
  frro : Sep fr 8 TVF_RO 0x1400
  frp : Sep fr 8 fp fl
  bw : fp.toNat + fl + 14 ≤ 0x40000000
  b0 : fp.toNat ≠ 0
  bg : Sep fp (fl + 14) G 0x740
  bro : Sep fp fl TVF_RO 0x1400
  hfp : memLoad32 M0 fr = fp
  hfl : memLoad32 M0 (fr + 4) = BitVec.ofNat 32 fl
  pw : p.toNat + n + 4 ≤ 0x40000000
  p0 : p.toNat ≠ 0
  pg : Sep p (n + 4) G 0x740
  pfr : Sep p n fr 8
  pb : Sep p n fp fl
  sp0 : g0 sp = F + BitVec.ofNat 32 0x180
  ret : g0 ra &&& ~~~1 = g0 ra

/-- The registers that `read_chain` keeps from its prologue to its
epilogue. -/
def RcRegs (F out fr : Word) (g0 f : Fin 32 → Word) : Prop :=
  f 0 = 0 ∧ f sp = F ∧ f 26 = out ∧ f 25 = fr ∧ f 3 = g0 3 ∧ f 4 = g0 4

/-- The memory between the prologue and the epilogue: changed only in the
stack region, the scratch slice, and the buffer, with the saved
registers in the frame. -/
def RcMemInv (M0 : Word → BitVec 8) (G F fr fp : Word) (fl : Nat) (g0 : Fin 32 → Word)
    (M : Word → BitVec 8) : Prop :=
  (∀ x, Sep G 0x740 x 1 → Sep fr 8 x 1 → Sep fp fl x 1 → M x = M0 x) ∧
    memLoad32 M (F + 0x17C) = g0 ra ∧ memLoad32 M (F + 0x178) = g0 8 ∧ memLoad32 M (F + 0x174) = g0 9 ∧
    memLoad32 M (F + 0x170) = g0 18 ∧ memLoad32 M (F + 0x16C) = g0 19 ∧ memLoad32 M (F + 0x168) = g0 20 ∧
    memLoad32 M (F + 0x164) = g0 21 ∧ memLoad32 M (F + 0x160) = g0 22 ∧ memLoad32 M (F + 0x15C) = g0 23 ∧
    memLoad32 M (F + 0x158) = g0 24 ∧ memLoad32 M (F + 0x154) = g0 25 ∧ memLoad32 M (F + 0x150) = g0 26 ∧
    memLoad32 M (F + 0x14C) = g0 27

/-- The memory part of `read_chain`'s postcondition: `r` at `out` and in
the scratch slice, and no change outside the stack region, the result,
the scratch slice, and the buffer. -/
def rcMem (M0 : Word → BitVec 8) (G out fr fp : Word) (fl : Nat) (r : Except (Option Nat) (RcCert × RcSt))
    (M : Word → BitVec 8) : Prop :=
  RcOut M out fr fp fl r ∧
    ∀ x, Sep G 0x740 x 1 → Sep out 0x40 x 1 → Sep fr 8 x 1 → Sep fp fl x 1 → M x = M0 x

theorem rc_kept_ne : ∀ q rd : Fin 32, q.val ∈ [2, 3, 4, 25, 26] →
    rd.val ∉ [0, 2, 3, 4, 25, 26] → q.val ≠ 0 ∧ q ≠ rd := by decide

/-- A write to a register that `read_chain` doesn't keep. -/
theorem RcRegs.set {F out fr : Word} {g0 f : Fin 32 → Word} {rd : Fin 32} {v : Word}
    (h : RcRegs F out fr g0 f) (hr : rd.val ∉ [0, 2, 3, 4, 25, 26]) : RcRegs F out fr g0 (upd f rd v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [upd_app, ite_eq_right (rc_kept_ne sp rd (by decide) hr).1, ite_eq_right (rc_kept_ne sp rd (by decide) hr).2, h1]
  · rw [upd_app, ite_eq_right (rc_kept_ne 26 rd (by decide) hr).1, ite_eq_right (rc_kept_ne 26 rd (by decide) hr).2, h2]
  · rw [upd_app, ite_eq_right (rc_kept_ne 25 rd (by decide) hr).1, ite_eq_right (rc_kept_ne 25 rd (by decide) hr).2, h3]
  · rw [upd_app, ite_eq_right (rc_kept_ne 3 rd (by decide) hr).1, ite_eq_right (rc_kept_ne 3 rd (by decide) hr).2, h4]
  · rw [upd_app, ite_eq_right (rc_kept_ne 4 rd (by decide) hr).1, ite_eq_right (rc_kept_ne 4 rd (by decide) hr).2, h5]

/-- The registers after a call that keeps everything outside `jClob`. -/
theorem RcRegs.clob {F out fr : Word} {g0 f : Fin 32 → Word} {m : Machine} {v : Word}
    (h : RcRegs F out fr g0 f) : RcRegs F out fr g0 (clob (upd f ra v) m jClob) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h.set (rd := ra) (v := v) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [clob_app, ite_eq_right (by decide), h0]
  · rw [clob_app, ite_eq_right (by decide), h1]
  · rw [clob_app, ite_eq_right (by decide), h2]
  · rw [clob_app, ite_eq_right (by decide), h3]
  · rw [clob_app, ite_eq_right (by decide), h4]
  · rw [clob_app, ite_eq_right (by decide), h5]

/-- Proves `RcRegs` of a register file that `upd` builds from one that
`hR` covers. -/
macro "rc_regs " h:term : tactic => `(tactic| (
  repeat (refine RcRegs.set ?_ (by decide))
  first | exact $h | exact RcRegs.clob $h))

theorem rc_saved_cases : ∀ q : Fin 32, q.val ∈ trSaved →
    q = ra ∨ q = 8 ∨ q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 20 ∨ q = 21 ∨ q = 22 ∨ q = 23 ∨ q = 24 ∨ q = 25 ∨
      q = 26 ∨ q = 27 ∨ q = 3 ∨ q = 4 := by decide

section
variable {f g0 : Fin 32 → Word} {F : Word}

/-- The epilogue at 0x48C: restores `ra` and `s0`–`s11` from the frame at
`F` and returns. -/
theorem rc_epi {R : (Word → BitVec 8) → Prop} {Mf : Word → BitVec 8} (hsp : f sp = F)
    (hI : memLoad32 Mf (F + 0x17C) = g0 ra ∧ memLoad32 Mf (F + 0x178) = g0 8 ∧ memLoad32 Mf (F + 0x174) = g0 9 ∧
      memLoad32 Mf (F + 0x170) = g0 18 ∧ memLoad32 Mf (F + 0x16C) = g0 19 ∧ memLoad32 Mf (F + 0x168) = g0 20 ∧
      memLoad32 Mf (F + 0x164) = g0 21 ∧ memLoad32 Mf (F + 0x160) = g0 22 ∧ memLoad32 Mf (F + 0x15C) = g0 23 ∧
      memLoad32 Mf (F + 0x158) = g0 24 ∧ memLoad32 Mf (F + 0x154) = g0 25 ∧ memLoad32 Mf (F + 0x150) = g0 26 ∧
      memLoad32 Mf (F + 0x14C) = g0 27)
    (hsp0 : g0 sp = F + BitVec.ofNat 32 0x180) (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0)
    (h3 : f 3 = g0 3) (h4 : f 4 = g0 4) (hR : R Mf) :
    WP trustedRootReadChainCode TRC (trPost R g0) Mf 0x48C f := by
  obtain ⟨e1, e8, e9, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27⟩ := hI
  have ea : ∀ c : Nat, F + BitVec.ofNat 32 0x100 + BitVec.ofNat 32 c = F + BitVec.ofNat 32 (0x100 + c) :=
    fun c => add_ofNat_assoc F 0x100 c
  have al : ∀ c : Nat, c % 4 = 0 → (F + BitVec.ofNat 32 0x100 + BitVec.ofNat 32 c).toNat % 4 = 0 :=
    fun c hc => by rw [ea]; exact aligned_add hal (by omega)
  refine WP.aluImm trc_at_48c ?_; wn
  rw [hsp, ev_add]
  refine WP.lw trc_at_48e (by trsimp; exact al 0x7C (by decide)) ?_; wn
  refine WP.lw trc_at_492 (by trsimp; exact al 0x78 (by decide)) ?_; wn
  refine WP.lw trc_at_494 (by trsimp; exact al 0x74 (by decide)) ?_; wn
  refine WP.lw trc_at_496 (by trsimp; exact al 0x70 (by decide)) ?_; wn
  refine WP.lw trc_at_49a (by trsimp; exact al 0x6C (by decide)) ?_; wn
  refine WP.lw trc_at_49e (by trsimp; exact al 0x68 (by decide)) ?_; wn
  refine WP.lw trc_at_4a2 (by trsimp; exact al 0x64 (by decide)) ?_; wn
  refine WP.lw trc_at_4a6 (by trsimp; exact al 0x60 (by decide)) ?_; wn
  refine WP.lw trc_at_4aa (by trsimp; exact al 0x5C (by decide)) ?_; wn
  refine WP.lw trc_at_4ae (by trsimp; exact al 0x58 (by decide)) ?_; wn
  refine WP.lw trc_at_4b2 (by trsimp; exact al 0x54 (by decide)) ?_; wn
  refine WP.lw trc_at_4b6 (by trsimp; exact al 0x50 (by decide)) ?_; wn
  refine WP.lw trc_at_4ba (by trsimp; exact al 0x4C (by decide)) ?_; wn
  refine WP.aluImm trc_at_4be ?_; wn
  refine WP.ret trc_at_4c0 ⟨?_, ?_, fun q hq => ?_, hR⟩
  · trsimp; rw [BitVec.add_assoc, add_lit_zero]; exact (congrArg (· &&& ~~~1) e1).trans hret
  · trsimp; rw [hsp0, hsp]; rfl
  · rcases rc_saved_cases q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · trsimp; rw [BitVec.add_assoc]; exact e1
    · trsimp; rw [BitVec.add_assoc]; exact e8
    · trsimp; rw [BitVec.add_assoc]; exact e9
    · trsimp; rw [BitVec.add_assoc]; exact e18
    · trsimp; rw [BitVec.add_assoc]; exact e19
    · trsimp; rw [BitVec.add_assoc]; exact e20
    · trsimp; rw [BitVec.add_assoc]; exact e21
    · trsimp; rw [BitVec.add_assoc]; exact e22
    · trsimp; rw [BitVec.add_assoc]; exact e23
    · trsimp; rw [BitVec.add_assoc]; exact e24
    · trsimp; rw [BitVec.add_assoc]; exact e25
    · trsimp; rw [BitVec.add_assoc]; exact e26
    · trsimp; rw [BitVec.add_assoc]; exact e27
    · trsimp; exact h3
    · trsimp; exact h4

end

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

theorem RcCtx.fG (X : RcCtx M0 G F out fr fp fl p n g0) (c : Nat) :
    F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x5C0 + c) := by
  rw [← X.fg, add_ofNat_assoc]

theorem RcCtx.gc (X : RcCtx M0 G F out fr fp fl p n g0) {c : Nat} (hc : c ≤ 0x740) :
    (G + BitVec.ofNat 32 c).toNat = G.toNat + c := by
  have := X.gw; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem RcCtx.fn (X : RcCtx M0 G F out fr fp fl p n g0) : F.toNat = G.toNat + 0x5C0 := by
  rw [← X.fg]; exact X.gc (by decide)

theorem RcCtx.f16 (X : RcCtx M0 G F out fr fp fl p n g0) : F.toNat % 16 = 0 := by
  have := X.fn; have := X.ga; omega

theorem RcCtx.fa4 (X : RcCtx M0 G F out fr fp fl p n g0) : F.toNat % 4 = 0 := by
  have := X.f16; omega

/-- A range of the frame or below it, inside the stack region, is below
`0x40000000` and apart from the code at `b`. -/
theorem RcCtx.glo (X : RcCtx M0 G F out fr fp fl p n g0) {c k l : Nat} {b : Word} (h : c + k ≤ 0x740)
    (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + l ≤ 2 ^ 32) : Sep (G + BitVec.ofNat 32 c) k b l :=
  tr_lowAt (by have := X.gw; omega) hb hbl

/-- The two parts of the stack region. -/
theorem RcCtx.gsep (_X : RcCtx M0 G F out fr fp fl p n g0) {c k d l : Nat} (h : c + k ≤ d ∨ d + l ≤ c)
    (hc : c + k ≤ 0x740) (hd : d + l ≤ 0x740) : Sep (G + BitVec.ofNat 32 c) k (G + BitVec.ofNat 32 d) l :=
  sep_offsets G h (by omega) (by omega)

theorem RcMemInv.slots {M0 : Word → BitVec 8} {G F fr fp : Word} {fl : Nat} {g0 : Fin 32 → Word}
    {M M' : Word → BitVec 8} (I : RcMemInv M0 G F fr fp fl g0 M)
    (h : ∀ d : Nat, 0x14C ≤ d → d + 4 ≤ 0x180 → d % 4 = 0 →
      memLoad32 M' (F + BitVec.ofNat 32 d) = memLoad32 M (F + BitVec.ofNat 32 d))
    (hx : ∀ x, Sep G 0x740 x 1 → Sep fr 8 x 1 → Sep fp fl x 1 → M' x = M x) :
    RcMemInv M0 G F fr fp fl g0 M' :=
  ⟨fun x a b c => (hx x a b c).trans (I.1 x a b c),
    (h 0x17C (by decide) (by decide) (by decide)).trans I.2.1,
    (h 0x178 (by decide) (by decide) (by decide)).trans I.2.2.1,
    (h 0x174 (by decide) (by decide) (by decide)).trans I.2.2.2.1,
    (h 0x170 (by decide) (by decide) (by decide)).trans I.2.2.2.2.1,
    (h 0x16C (by decide) (by decide) (by decide)).trans I.2.2.2.2.2.1,
    (h 0x168 (by decide) (by decide) (by decide)).trans I.2.2.2.2.2.2.1,
    (h 0x164 (by decide) (by decide) (by decide)).trans I.2.2.2.2.2.2.2.1,
    (h 0x160 (by decide) (by decide) (by decide)).trans I.2.2.2.2.2.2.2.2.1,
    (h 0x15C (by decide) (by decide) (by decide)).trans I.2.2.2.2.2.2.2.2.2.1,
    (h 0x158 (by decide) (by decide) (by decide)).trans I.2.2.2.2.2.2.2.2.2.2.1,
    (h 0x154 (by decide) (by decide) (by decide)).trans I.2.2.2.2.2.2.2.2.2.2.2.1,
    (h 0x150 (by decide) (by decide) (by decide)).trans I.2.2.2.2.2.2.2.2.2.2.2.2.1,
    (h 0x14C (by decide) (by decide) (by decide)).trans I.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- A change in the stack region below the saved registers, the scratch
slice, and the buffer keeps the invariant. -/
theorem RcMemInv.step (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {c l : Nat}
    (I : RcMemInv M0 G F fr fp fl g0 M) (hcl : c + l ≤ 0x70C)
    (h : ∀ x, Sep (G + BitVec.ofNat 32 c) l x 1 → Sep fr 8 x 1 → Sep fp fl x 1 → M' x = M x) :
    RcMemInv M0 G F fr fp fl g0 M' := by
  refine I.slots (fun d hd1 hd2 _ => memLoad32_congr fun j hj => ?_) (fun x a b c' => h x (sep_in a.symm (by omega : c + l ≤ 0x740)).symm b c')
  have sG : Sep (G + BitVec.ofNat 32 c) l (F + BitVec.ofNat 32 d) 4 := by
    rw [X.fG]; exact X.gsep (Or.inl (by omega)) (by omega) (by omega)
  have sF : Sep fr 8 (F + BitVec.ofNat 32 d) 4 := by rw [X.fG]; exact X.frg.subR (by omega)
  have sB : Sep fp fl (F + BitVec.ofNat 32 d) 4 := by rw [X.fG]; exact (trSepR X.bg.symm (by omega)).symm.subR (by omega)
  exact h _ (sG.symm.shift hj).symm (sF.symm.shift hj).symm (sB.symm.shift hj).symm

/-- `RcCode` in the memory between the prologue and the epilogue. -/
theorem RcCtx.codeAt (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8}
    (I : RcMemInv M0 G F fr fp fl g0 M) : RcCode M :=
  X.code.out3 I.1 X.gw X.fw (by have := X.bw; omega) X.ro X.frro X.bro

/-- The code above `0x40000000` in the memory between the prologue and the
epilogue. -/
theorem RcCtx.hiAt (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8}
    (I : RcMemInv M0 G F fr fp fl g0 M) : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x :=
  fun x hx => I.1 x (lowSep X.gw hx (by have := x.isLt; omega)) (lowSep X.fw hx (by have := x.isLt; omega))
    (lowSep (by have := X.bw; omega) hx (by have := x.isLt; omega))

/-- The call of any callee whose writes stay in the stack region below the
saved registers, the scratch slice, and the buffer, and that keeps `sp`
and `trSaved`. -/
theorem RcCtx.call (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word} {Q : Post}
    {off c l : Nat} {hi lo tb : Word} {P : Machine → Prop}
    (h1 : fetchRel trustedRootReadChainCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootReadChainCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TRC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = tb)
    (hI : RcMemInv M0 G F fr fp fl g0 M) (hcl : c + l ≤ 0x70C)
    (hcallee : ∀ m1 : Machine, m1.pc = tb → m1.mem = M →
      (∀ x, reg m1 x = upd f ra (TRC + BitVec.ofNat 32 (off + 8)) x) →
      ∃ m2, Steps m1 m2 ∧ m2.pc = TRC + BitVec.ofNat 32 (off + 8) ∧ P m2 ∧ reg m2 sp = reg m1 sp ∧
        ∀ q : Fin 32, q.val ∈ trSaved → reg m2 q = reg m1 q)
    (hfoot : ∀ m2, P m2 → ∀ x, Sep (G + BitVec.ofNat 32 c) l x 1 → Sep fr 8 x 1 → Sep fp fl x 1 → m2.mem x = M x)
    (k : ∀ m2 : Machine, P m2 → RcMemInv M0 G F fr fp fl g0 m2.mem →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f := by
  refine WP.trCallSaved (P := P) h1 h2 htgt (fun m1 hpc hmem hreg _ => hcallee m1 hpc hmem hreg)
    (fun m2 hP hc => ?_) (fun m2 hP => k m2 hP (hI.step X hcl (hfoot m2 hP)))
  have hgc : (G + BitVec.ofNat 32 c).toNat = G.toNat + c := X.gc (by omega)
  exact hc.hi (fun x hx => hfoot m2 hP x (lowSep (by rw [hgc]; have := X.gw; omega) hx (by have := x.isLt; omega))
    (lowSep X.fw hx (by have := x.isLt; omega)) (lowSep (by have := X.bw; omega) hx (by have := x.isLt; omega)))
    (by decide) (by decide)

/-- The return through the epilogue, after `out` holds the result. -/
theorem RcCtx.exit (X : RcCtx M0 G F out fr fp fl p n g0) {M Mf : Word → BitVec 8} {f : Fin 32 → Word}
    {r : Except (Option Nat) (RcCert × RcSt)} (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hO : Out M Mf out 0x40) (hr : RcOut Mf out fr fp fl r) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) Mf 0x48C f := by
  obtain ⟨-, r1, -, -, r3, r4⟩ := hR
  have so : ∀ d : Nat, 0x14C ≤ d → d + 4 ≤ 0x180 →
      memLoad32 Mf (F + BitVec.ofNat 32 d) = memLoad32 M (F + BitVec.ofNat 32 d) := fun d _ hd =>
    hO.load32 (by rw [X.fG]; exact X.og.subR (by omega))
  obtain ⟨hI1, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ := hI
  exact rc_epi r1 ⟨(so 0x17C (by decide) (by decide)).trans e1, (so 0x178 (by decide) (by decide)).trans e2,
    (so 0x174 (by decide) (by decide)).trans e3, (so 0x170 (by decide) (by decide)).trans e4,
    (so 0x16C (by decide) (by decide)).trans e5, (so 0x168 (by decide) (by decide)).trans e6,
    (so 0x164 (by decide) (by decide)).trans e7, (so 0x160 (by decide) (by decide)).trans e8,
    (so 0x15C (by decide) (by decide)).trans e9, (so 0x158 (by decide) (by decide)).trans e10,
    (so 0x154 (by decide) (by decide)).trans e11, (so 0x150 (by decide) (by decide)).trans e12,
    (so 0x14C (by decide) (by decide)).trans e13⟩
    X.sp0 X.ret X.fa4 r3 r4
    ⟨hr, fun x sG sO sF sB => (hO x sO.symm).trans (hI1 x sG sF sB)⟩

/-- The two stores of an `Err` at `out`. -/
theorem rc_errMem (M : Word → BitVec 8) (out : Word) (b : BitVec 8) :
    Out M (memStore8 (memStore32 M out 0) (out + 4) b) out 0x40 ∧
      memLoad32 (memStore8 (memStore32 M out 0) (out + 4) b) out = 0 ∧
      memStore8 (memStore32 M out 0) (out + 4) b (out + 4) = b := by
  have h04 : Sep (out + 4) 1 out 4 := by
    have := sep_offsets out (c := 4) (n := 1) (d := 0) (k := 4) (Or.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  refine ⟨((out_store32 _ _ _).mono (by decide)).trans (Out.upK (c := 4) rfl (out_store8 _ _ _) (by decide)),
    ?_, memStore8_same _ _ _⟩
  rw [memLoad32_store8_sep h04, memLoad32_store32_same]

/-- The `Err` writer at `pc`, which stores the error byte from the register
`rb`: a `sw` of zero then a `sb` at `out + 4`, then a jump or fall to the
epilogue. -/
theorem RcCtx.errW (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {e : Option Nat} {r : Except (Option Nat) (RcCert × RcSt)} {pc : Nat} {rb : Fin 32}
    (h1 : fetchRel trustedRootReadChainCode pc = some (.store .sw (26 : Fin 32) x0 0x0, 4))
    (h2 : fetchRel trustedRootReadChainCode (pc + 4) = some (.store .sb (26 : Fin 32) rb 0x4, 4))
    (hnext : WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0)
        (memStore8 (memStore32 M out 0) (out + 4) ((f rb).extractLsb' 0 8)) 0x48C f →
      WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0)
        (memStore8 (memStore32 M out 0) (out + 4) ((f rb).extractLsb' 0 8)) (pc + 4 + 4) f)
    (hr : r = .error e) (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hb : ∀ b, e = some b → (f rb).extractLsb' 0 8 = BitVec.ofNat 8 b) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M pc f := by
  have r0 : f x0 = 0 := hR.1
  have r26 := hR.2.2.1
  have lo : ∀ c k : Nat, c + k ≤ 0x40 → Sep (out + BitVec.ofNat 32 c) k TRC trustedRootReadChainCode.length :=
    fun c k h => tr_lowAt (by have := X.ow; omega) (by decide) (by decide)
  refine WP.sw h1 (by rw [r26, add_lit_zero]; exact X.oa)
    (by rw [r26, add_lit_zero]; have := lo 0 4 (by decide); rwa [add_ofNat_zero] at this) ?_
  refine WP.sb h2 (by rw [r26]; exact lo 4 1 (by decide)) ?_
  rw [r26, r0, add_lit_zero]
  refine hnext ?_
  obtain ⟨hO, h0, h4⟩ := rc_errMem M out ((f rb).extractLsb' 0 8)
  refine X.exit hR hI hO ?_
  rw [hr]
  exact ⟨h0, fun b hb' => by rw [h4, hb b hb']⟩

end

end C3.RV32
