import C3BootProofs.Proofs.AcceptRead
import C3BootProofs.Proofs.AcceptImage
import C3BootProofs.Proofs.AcceptIndex
import C3BootProofs.Proofs.AcceptPinned
import C3BootProofs.Proofs.AcceptRoots
import C3BootProofs.Proofs.AcceptTargetsTop
import C3BootProofs.Proofs.AcceptExtractHead
import C3BootProofs.Proofs.AcceptBundle
import C3BootProofs.Proofs.AcceptFinish
import C3BootProofs.Proofs.BootMainContract

/-!
# `boot_main`'s first closure: composing the stages

The closure's result, the ways the closure ends, and the steps that the
stages share: an exit becomes the `None` return, and a stage's end at the
next offset hands over to the next stage.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.BootMainContract

/-- **A `Some` result** at `r`: `bmcAccept` accepts slot `slot`, the byte at
+0xC isn't 0xFF, and the security version, the image's flash address, and
the image's header are where `Closure0Contract` reads them. -/
def AcsGood (flash : Nat → BitVec 8) (pinned : Bytes) (policy : Policy) (level : Nat) (slot r : Word)
    (M : Word → BitVec 8) : Prop :=
  ∃ mf sv tm, bmcAccept flash pinned policy level slot = some (mf, sv, tm) ∧ M (r + 0xC) ≠ 0xFF ∧
    M (r + 0x128) = BitVec.ofNat 8 sv ∧
    memLoad32 M (r + 0x120) = BitVec.ofNat 32 (bmcBase slot + mf.image.offset) ∧ AccOk flash slot mf M r

/-- **The closure's return**: memory as it was at the call outside the frame
and the 0x1A0 bytes below it, `Buffers`, and the result, and the result is
`None` or a `Some` that `AcsGood` describes. -/
def AcsRes (flash : Nat → BitVec 8) (pinned : Bytes) (policy : Policy) (level : Nat) (slot B Bf r : Word)
    (M0 M : Word → BitVec 8) : Prop :=
  (∀ x, Sep x 1 (B + 0xFFFFFE60) 0x5C10 → Sep x 1 Bf acBufLen → Sep x 1 r 0x12C → M x = M0 x) ∧
  (M (r + 0xC) = 0xFF ∨ AcsGood flash pinned policy level slot r M)

/-- What the closure was called with: the flash and the ROM, the pinned root
and the policy, the frame `B` (the stack pointer at the call less 0x5A70),
`Buffers` at `Bf`, the result at `r`, the slot and the level, the saved
registers `v`, and memory `M0` at the call. -/
structure AcsCtx where
  flash : Nat → BitVec 8
  R : Nat
  romStack : Nat
  romBase : Word
  romCode : List Nat
  pinned : Bytes
  policy : Policy
  B : Word
  Bf : Word
  g : Word
  t : Word
  r : Word
  slot : Word
  level : Word
  v : Nat → Word
  M0 : Word → BitVec 8

/-- From `n`, the closure panics or returns with `AcsRes`. -/
def AcsCtx.End (X : AcsCtx) (n : Machine) : Prop :=
  Panics n ∨
    AcRet X.B X.v n (AcsRes X.flash X.pinned X.policy X.level.toNat X.slot X.B X.Bf X.r X.M0)

theorem acs_end_pre {X : AcsCtx} {n0 n1 : Machine} (h : Steps n0 n1)
    (h3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32)) (h4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32))
    (e : X.End n1) : X.End n0 := by
  rcases e with e | e
  · exact .inl (Panics.of_steps h e)
  · exact .inr (e.pre h h3 h4)

/-- A stage that keeps `AcInv` ends the closure as its two ways on do. -/
theorem acs_stage {X : AcsCtx} {n0 : Machine} {o : Nat} {Q : Machine → Prop}
    (I0 : AcInv X.B X.Bf X.g X.t X.v X.M0 n0) (h : AcStage X.B X.Bf X.g X.t X.r X.v X.M0 n0 o Q)
    (hf : ∀ n, AcInv X.B X.Bf X.g X.t X.v X.M0 n → AcFail X.B X.r n → X.End n)
    (hk : ∀ n, AcInv X.B X.Bf X.g X.t X.v X.M0 n → n.pc = AC + BitVec.ofNat 32 o → Q n → X.End n) :
    X.End n0 := by
  obtain ⟨n1, s1, h⟩ := h
  rcases h with h | ⟨I1, h | ⟨hp, hq⟩⟩
  · exact .inl ⟨n1, s1, h⟩
  · exact acs_end_pre s1 (by rw [I1.gp, I0.gp]) (by rw [I1.tp, I0.tp]) (hf n1 I1 h)
  · exact acs_end_pre s1 (by rw [I1.gp, I0.gp]) (by rw [I1.tp, I0.tp]) (hk n1 I1 hp hq)

/-! ## Addresses -/

theorem acs_wide_toNat {B : Word} (F : Fr B 0x5A70) : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := by
  have := F.lo; have := B.isLt
  rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]; omega

/-- Outside the frame and the 0x1A0 bytes below it is outside the frame. -/
theorem acs_wide_sep {B x : Word} (_ : Fr B 0x5A70) (h : Sep x 1 (B + 0xFFFFFE60) 0x5C10) :
    Sep x 1 B 0x5A70 :=
  acw_frame h

theorem acs_wb (B : Word) : B + 0xFFFFFE60 + BitVec.ofNat 32 0x1A0 = B := by
  rw [BitVec.add_assoc]
  exact (congrArg (B + ·) (by decide : (0xFFFFFE60 : Word) + BitVec.ofNat 32 0x1A0 = 0)).trans (BitVec.add_zero B)

/-- Outside the result is outside its byte at +0xC. -/
theorem acs_res_c {r x : Word} (h : Sep x 1 r 0x12C) : Sep x 1 (r + 0xC) 1 :=
  (h.symm.sub (c := 0xC) (l := 1) (by decide)).symm

/-- `x` is outside the memory from 0x3FCC8000 to 0x40000000, where the
closure's stack, `Buffers`, and result are. -/
def AcsOutRam (x : Word) : Prop := x.toNat < 0x3FCC8000 ∨ 0x40000000 ≤ x.toNat

theorem acs_ram_sep {a x : Word} {n : Nat} (h1 : 0x3FCC8000 ≤ a.toNat) (h2 : a.toNat + n ≤ 0x40000000)
    (hx : AcsOutRam x) : Sep x 1 a n := by
  rcases hx with hx | hx
  · exact sep_of_le (by omega) (by omega)
  · exact (sep_of_le (by omega) (by have := x.isLt; omega)).symm

/-! ## The callees' code and data -/

/-- The policy slices of a trust root at `a` in `S`, as `SvRootAt` reads
them. -/
structure AcsPolicyAt (Bs : Word) (S : Word → BitVec 8) (a : Word) (policy : Policy) : Prop where
  issuer : Sv.SvRoBytesAt Bs S (memLoad32 S a) (memLoad32 S (a + 0x4)) policy.issuer
  buildSignerUri : Sv.SvRoBytesAt Bs S (memLoad32 S (a + 0x8)) (memLoad32 S (a + 0xC)) policy.buildSignerUri
  repositoryId : Sv.SvRoBytesAt Bs S (memLoad32 S (a + 0x10)) (memLoad32 S (a + 0x14)) policy.repositoryId
  ownerId : Sv.SvRoBytesAt Bs S (memLoad32 S (a + 0x18)) (memLoad32 S (a + 0x1C)) policy.ownerId
  trigger : Sv.SvRoBytesAt Bs S (memLoad32 S (a + 0x20)) (memLoad32 S (a + 0x24)) policy.trigger

/-- The callees' code and data that every stage reads, and the policy and
pinned root that `bootMainClosure0` holds, in memory `M`. `pol` says that a
trust root whose first 0x28 bytes are the ones the closure writes (the
issuer's pointer, the issuer's length, then the policy's other bytes) holds
`policy` for `sigstore::verify` on a frame at `B`, in memory that keeps `M`
outside RAM. -/
structure AcsEnvs (romBase : Word) (romCode : List Nat) (pinned : Bytes) (policy : Policy)
    (M : Word → BitVec 8) : Prop where
  ac : CodeIn M AC bootMainClosure0Code
  rd : AcReadEnv M
  img : AcImageEnv M
  idx : AcIndexEnv romBase romCode M
  pin : AcPinnedEnv pinned M
  rtRd : CodeIn M TRD tufReadDocCode
  rtIx : CodeIn M (TRD + 0xB388) tufIndexDocCode
  rtFp : CodeIn M (TRD + 0x16DA4) flashPartReadCode
  rtPr : PrCode M
  rtRm : RmCode M
  rtTex : TexCode M
  rtRoot : memBytes M acoRootName 4 = ascii!"root"
  rtTgts : memBytes M acoTargetsName 7 = ascii!"targets"
  tgt : AcTargetsEnv romBase romCode M
  ext : AcExtractEnv M
  bun : AcBundleEnv M
  fin : AcFinishEnv M
  pol : ∀ (B a : Word) (S : Word → BitVec 8), 0x3FCC81A0 ≤ B.toNat → B.toNat + 0x5A70 ≤ 0x3FCE0000 →
    (∀ x, AcsOutRam x → S x = M x) → memLoad32 S a = 0x3FCC6621 → S (a + 4) = 0x2B →
    memBytes S (a + 5) 0x23 = memBytes M (img% acPolicyAddress) 0x23 → AcsPolicyAt (B + 0x13F0) S a policy

/-- What `Closure0Contract`'s caller provides, for `X`. -/
structure AcsCtx.Ok (X : AcsCtx) : Prop where
  rom : RomRead X.flash X.R X.romBase X.romCode
  log : RomFn X.romBase X.romCode 0x40000040 X.romStack fun _ => True
  hrs : X.romStack ≤ 0x3A50
  hR : X.R ≤ 0x3A50 - 0x180
  hR4 : X.R % 4 = 0
  rb : 0x40000000 ≤ X.romBase.toNat
  rl : X.romBase.toNat + X.romCode.length ≤ 2 ^ 32
  F : Fr X.B 0x5A70
  blo : 0x3FCC81A0 ≤ X.B.toNat
  bfa : X.Bf.toNat % 4 = 0
  bflo : 0x3FCC8000 ≤ X.Bf.toNat
  bfhi : X.Bf.toNat + acBufLen + 14 ≤ 0x40000000
  sBf : Sep (X.B + 0xFFFFFE60) 0x5C10 X.Bf (acBufLen + 14)
  ra : X.r.toNat % 4 = 0
  rlo : 0x3FCC8000 ≤ X.r.toNat
  rhi : X.r.toNat + 0x12C ≤ 0x40000000
  rS : Sep X.r 0x12C (X.B + 0xFFFFFE60) 0x5C10
  rB : Sep X.r 0x12C X.Bf acBufLen
  sl : X.slot.toNat < 2
  lev : X.level.toNat < 256
  ret : X.v 0 &&& ~~~1 = X.v 0
  env : ∀ M, (∀ x, AcsOutRam x → M x = X.M0 x) → AcsEnvs X.romBase X.romCode X.pinned X.policy M

namespace AcsCtx.Ok

variable {X : AcsCtx} (ok : X.Ok)
include ok

theorem bhi : X.B.toNat + 0x5A70 ≤ 0x3FCE0000 := ok.F.hi

theorem sB : Sep X.B 0x5A70 X.Bf acBufLen := by
  have h := (ok.sBf.sub (c := 0x1A0) (l := 0x5A70) (by decide)).subR (c := 0) (l := acBufLen) (by decide)
  rwa [acs_wb, add_ofNat_zero] at h

theorem outRam {x : Word} (hx : AcsOutRam x) : Sep x 1 X.B 0x5A70 ∧ Sep x 1 X.Bf acBufLen :=
  ⟨acs_ram_sep (by have := ok.blo; omega) (by have := ok.bhi; omega) hx,
    acs_ram_sep ok.bflo (by have := ok.bfhi; omega) hx⟩

theorem bfhi' : X.Bf.toNat + acBufLen ≤ 0x40000000 := by have := ok.bfhi; omega

/-- `Buffers` is outside `sigstore::verify`'s stack. -/
theorem svBf : Sv.SvIn (X.B + 0x13F0) X.Bf acBufLen :=
  ⟨by
      rw [acf_svB]; have h := ok.sBf.symm.subR (c := 0) (l := 0x3BF0) (by decide)
      rwa [add_ofNat_zero] at h,
    by have := ok.bflo; omega, ok.bfhi⟩

/-- A byte of `Buffers` is outside the frame. -/
theorem inBf {y : Word} (h1 : X.Bf.toNat ≤ y.toNat) (h2 : y.toNat < X.Bf.toNat + acBufLen) :
    Sep y 1 X.B 0x5A70 := by
  have e : y = X.Bf + BitVec.ofNat 32 (y.toNat - X.Bf.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := ok.bfhi; have := y.isLt; omega
  rw [e]; exact ok.sB.symm.sub (by omega)

/-- The extract stage's layout. -/
theorem layout : AceLayout X.B X.Bf where
  fr := ok.F
  sep := ok.sB
  al := ok.bfa
  hi := ok.bfhi'
  polStack := sep_of_le (by simp only [BitVec.reduceToNat]; have := ok.blo; omega)
    (by have := ok.bhi; omega)
  polBuf := sep_of_le (by simp only [BitVec.reduceToNat]; have := ok.bflo; omega)
    (by have := ok.bfhi; omega)
  ro := (sep_of_le (by simp only [BitVec.toNat_ofNat, roWindowAddress, roWindowSize]; have := ok.blo; omega)
    (by have := ok.bhi; omega)).symm

/-- The frame and the 0x1A0 bytes below it are apart from the read-only window. -/
theorem wro : Sep (X.B + 0xFFFFFE60) 0x5C10 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize) :=
  (sep_of_le (by rw [acs_wide_toNat ok.F]; have := ok.blo; simp only [BitVec.toNat_ofNat]; omega)
    (by rw [acs_wide_toNat ok.F]; have := ok.bhi; omega)).symm

theorem svRo : Sv.SvRoSep (X.B + 0x13F0) := by
  unfold Sv.SvRoSep; rw [acf_svB]; exact ok.wro.sub (c := 0) (l := 0x3BF0) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h

/-- The callees' code and data, in memory that keeps `M0` outside the stack
and `Buffers`. -/
theorem envs {M : Word → BitVec 8} (h : ∀ x, Sep x 1 X.B 0x5A70 → Sep x 1 X.Bf acBufLen → M x = X.M0 x) :
    AcsEnvs X.romBase X.romCode X.pinned X.policy M :=
  ok.env M fun x hx => h x (ok.outRam hx).1 (ok.outRam hx).2

theorem envsAt {n : Machine} (I : AcInv X.B X.Bf X.g X.t X.v X.M0 n) :
    AcsEnvs X.romBase X.romCode X.pinned X.policy n.mem :=
  ok.envs I.out

theorem sRomB : Sep X.B 0x5A70 X.romBase X.romCode.length :=
  sep_of_le (by have := ok.bhi; have := ok.rb; omega) ok.rl

theorem sRomBf : Sep X.Bf acBufLen X.romBase X.romCode.length :=
  sep_of_le (by have := ok.bfhi; have := ok.rb; omega) ok.rl

theorem rc_toNat : (X.r + 0xC).toNat = X.r.toNat + 0xC := by
  have := ok.rhi; rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]; omega

set_option maxRecDepth 100000 in
theorem sRC : Sep (X.r + 0xC) 1 AC bootMainClosure0Code.length :=
  sep_of_le (by rw [ok.rc_toNat]; have := ok.rhi; show _ ≤ 0x403a00a6; omega) (by decide)

theorem sRS : Sep (X.r + 0xC) 1 X.B 0x5A70 :=
  acs_wide_sep ok.F (ok.rS.sub (c := 0xC) (l := 1) (by decide))

/-- **An exit returns `None`.** -/
theorem fail {n : Machine} (I : AcInv X.B X.Bf X.g X.t X.v X.M0 n) (h : AcFail X.B X.r n) : X.End n := by
  have E := ok.envsAt I
  refine .inr ((ac_exit ok.log ok.hrs E.ac E.idx.rom E.idx.tbl ok.sRomB ok.F ok.ret ok.sRC ok.sRS I h).mono
    fun M hM => ⟨fun x h1 h2 h3 => ?_, .inl hM.1⟩)
  have hs := acs_wide_sep ok.F h1
  rw [hM.2 x hs (acs_res_c h3), I.out x hs h2]

theorem envsW {n : Machine} (I : AcInvW X.B X.Bf X.g X.t X.v X.M0 n) :
    AcsEnvs X.romBase X.romCode X.pinned X.policy n.mem :=
  ok.env n.mem fun x hx => I.out x (acs_ram_sep (by rw [acs_wide_toNat ok.F]; have := ok.blo; omega)
    (by rw [acs_wide_toNat ok.F]; have := ok.bhi; omega) hx) (ok.outRam hx).2

/-- **An exit after `sigstore::verify` returns `None`.** -/
theorem failW {n : Machine} (I : AcInvW X.B X.Bf X.g X.t X.v X.M0 n) (h : AcFail X.B X.r n) : X.End n := by
  have E := ok.envsW I
  exact .inr ((ac_exit_wide ok.log ok.hrs E.ac E.idx.rom E.idx.tbl ok.sRomB ok.F ok.ret ok.sRC ok.sRS I h).mono
    fun _ hM => ⟨fun x h1 h2 h3 => hM.2 x h1 h2 (acs_res_c h3), .inl hM.1⟩)

end AcsCtx.Ok

/-! ## The specification's steps -/

/-- **`bmcAccept` accepts the slot** when each of `acceptTufSlot`'s steps
succeeds on the slot's parts. -/
theorem acs_accept {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {level : Nat} {slot : Word}
    {mf : Manifest} {header : ImageHeader} {parts : TufParts} {ver ex : Nat} {root : SigstoreRoot}
    {b : Bundle} {vv : Verified}
    (hm : decodeManifest (flashBytes flash (acBase slot) 32) = some mf)
    (hh : decodeImageHeader (flashBytes flash (acBase slot + mf.image.offset) mf.image.length)
      mf.image.length = some header)
    (hl : level ≤ header.securityVersion)
    (hp : decodeTufParts (flashBytes flash (acBase slot + mf.tuf.offset) mf.tuf.length) = some parts)
    (hv : verifyTuf pinned parts = some (ver, ex))
    (hx : extractTrustedRoot parts.trustedRoot policy = some root)
    (hb : decodeBundle (flashBytes flash (acBase slot + mf.bundle.offset) mf.bundle.length) = some b)
    (hs : sigstoreVerify b root (sha256 (flashBytes flash (acBase slot + mf.image.offset) mf.image.length)) =
      some vv)
    (ht : vv.signedTime ≤ ex) :
    bmcAccept flash pinned policy level slot = some (mf, header.securityVersion, vv.signedTime) := by
  have hlen : (flashBytes flash (acBase slot + mf.image.offset) mf.image.length).length = mf.image.length :=
    bmc_flash_len flash _ _
  have hacc : acceptTufSlot (flashBytes flash (acBase slot + mf.image.offset) mf.image.length)
      (flashBytes flash (acBase slot + mf.bundle.offset) mf.bundle.length)
      (flashBytes flash (acBase slot + mf.tuf.offset) mf.tuf.length) pinned policy level =
      some (header.securityVersion, vv.signedTime) := by
    unfold acceptTufSlot
    rw [hlen, hh]
    simp only [Option.bind_eq_bind, Option.bind_some, require, hl, decide_true, ite_true, hp, hv, hx, hb, hs,
      ht, Option.pure_def]
  unfold bmcAccept
  show (do
    let mf ← decodeManifest (flashBytes flash (acBase slot) 32)
    let r ← acceptTufSlot (flashBytes flash (acBase slot + mf.image.offset) mf.image.length)
      (flashBytes flash (acBase slot + mf.bundle.offset) mf.bundle.length)
      (flashBytes flash (acBase slot + mf.tuf.offset) mf.tuf.length) pinned policy level
    pure (mf, r)) = _
  rw [hm]
  simp only [Option.bind_eq_bind, Option.bind_some, hacc, Option.pure_def]

/-! ## The header in the result -/

theorem acs_kind : ∀ k : BitVec 8, (3 : BitVec 8).ult k = false → bmcKind (kindOf k) = k := by decide

theorem acs_ze (c : BitVec 8) : c.zeroExtend 32 = BitVec.ofNat 32 c.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- **`HdrAt` from `image::parse`'s result**: bytes at `r` that are the
first 0x10C bytes of a result that `OutOk` describes hold the header that
the result names. -/
theorem acs_hdr {M Mh : Word → BitVec 8} {r out : Word} {sv : BitVec 8} {entry : Word} {cnt : BitVec 8}
    {ilen : Word} {segs : List SegW} (hO : OutOk Mh out sv entry cnt ilen segs)
    (hl : segs.length = cnt.toNat) (hl16 : segs.length ≤ 16)
    (hk : ∀ s ∈ segs, (3 : BitVec 8).ult s.kind = false)
    (hb : ∀ i, i < 0x10C → M (r + BitVec.ofNat 32 i) = Mh (out + BitVec.ofNat 32 i)) :
    HdrAt M r (toHdr ilen (sv, entry, cnt, segs)) := by
  have hw : ∀ c, c + 4 ≤ 0x10C → memLoad32 M (r + BitVec.ofNat 32 c) = memLoad32 Mh (out + BitVec.ofNat 32 c) :=
    fun c hc => memLoad32_congr2 fun j hj => by
      rw [add_ofNat_assoc, add_ofNat_assoc]; exact hb (c + j) (by omega)
  obtain ⟨hs, -, he, -, hc, -⟩ := hO
  refine ⟨(hw 0x100 (by decide)).trans (he.trans (acf_ofNatToNat entry).symm),
    (hw 0x108 (by decide)).trans (hc.trans ?_), fun j hj => ?_⟩
  · simp only [toHdr, List.length_map, hl]; exact acs_ze cnt
  · simp only [toHdr, List.length_map] at hj
    have hj16 : 16 * j + 16 ≤ 0x100 := by omega
    obtain ⟨ea, eo, el, ek⟩ := hs j hj
    simp only [toHdr, List.getElem_map, toSeg]
    refine ⟨(hw _ (by omega)).trans (ea.trans (acf_ofNatToNat _).symm),
      (hw _ (by omega)).trans (eo.trans (acf_ofNatToNat _).symm),
      (hw _ (by omega)).trans (el.trans (acf_ofNatToNat _).symm), ?_⟩
    rw [hb _ (by omega), ek, acs_kind _ (hk _ (List.getElem_mem hj))]

end C3.RV32.Ac
