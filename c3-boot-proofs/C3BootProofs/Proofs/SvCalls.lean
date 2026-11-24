import C3BootProofs.Proofs.SvLib
import C3BootProofs.Proofs.DerNested
import C3BootProofs.Proofs.DerElement
import C3BootProofs.Proofs.Fs256Main

/-!
# `sigstore::verify`: its calls

The functions `sigstore::verify` calls, at their addresses in the image, and
one lemma for each kind of call: from the call instruction in
`sigstore::verify`, with the arguments in the frame, to the instruction
after it, with what the callee left in memory.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- The functions `sigstore::verify` calls, at their addresses in the image. -/
structure SvCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M SV sigstoreVerifyCode
  seq : CodeIn M (BitVec.ofNat 32 derSequenceAddress) derSequenceCode
  nest : CodeIn M (BitVec.ofNat 32 derNestedAddress) derNestedCode
  elem : CodeIn M (BitVec.ofNat 32 derElementAddress) derElementCode
  tlv : CodeIn M (BitVec.ofNat 32 derTlvAddress) derTlvCode
  K : P3Code M
  gs : C3.RV32.Gs.GsCode M
  derBitString : CodeIn M (BitVec.ofNat 32 derBitStringAddress) derBitStringCode
  derPositiveInteger : CodeIn M (BitVec.ofNat 32 derPositiveIntegerAddress) derPositiveIntegerCode
  derInteger : CodeIn M (BitVec.ofNat 32 derIntegerAddress) derIntegerCode
  derOptional : CodeIn M (BitVec.ofNat 32 derOptionalAddress) derOptionalCode
  derIntegerIs : CodeIn M (BitVec.ofNat 32 derIntegerIsAddress) derIntegerIsCode
  sliceEq : CodeIn M (BitVec.ofNat 32 sliceEqAddress) sliceEqCode
  equalSameLength : CodeIn M (BitVec.ofNat 32 equalSameLengthAddress) equalSameLengthCode
  memcmp : CodeIn M (BitVec.ofNat 32 memcmpAddress) memcmpCode
  derAlgorithm : CodeIn M (BitVec.ofNat 32 derAlgorithmAddress) derAlgorithmCode
  derOid : CodeIn M (BitVec.ofNat 32 derOidAddress) derOidCode
  sliceNe : CodeIn M (BitVec.ofNat 32 sliceNeAddress) sliceNeCode
  x509ReadTime : CodeIn M (BitVec.ofNat 32 x509ReadTimeAddress) x509ReadTimeCode
  generalizedTime : CodeIn M (BitVec.ofNat 32 generalizedTimeAddress) generalizedTimeCode
  dateTime : CodeIn M (BitVec.ofNat 32 dateTimeAddress) dateTimeCode
  timeDigits2 : CodeIn M (BitVec.ofNat 32 timeDigits2Address) timeDigits2Code
  timeDigits4 : CodeIn M (BitVec.ofNat 32 timeDigits4Address) timeDigits4Code
  allAsciiDigit : CodeIn M (BitVec.ofNat 32 allAsciiDigitAddress) allAsciiDigitCode
  derBooleanTrue : CodeIn M (BitVec.ofNat 32 derBooleanTrueAddress) derBooleanTrueCode
  derOctetString : CodeIn M (BitVec.ofNat 32 derOctetStringAddress) derOctetStringCode
  listsOid : CodeIn M (BitVec.ofNat 32 listsOidAddress) listsOidCode
  derSet : CodeIn M (BitVec.ofNat 32 derSetAddress) derSetCode
  ecdsaSignature48 : CodeIn M (BitVec.ofNat 32 ecdsaSignature48Address) ecdsaSignature48Code
  derScalar48 : CodeIn M (BitVec.ofNat 32 derScalar48Address) derScalar48Code
  derScalar32 : CodeIn M (BitVec.ofNat 32 derScalar32Address) derScalar32Code
  zipSkipNext : CodeIn M (BitVec.ofNat 32 zipSkipNextAddress) zipSkipNextCode
  isSha256 : CodeIn M (BitVec.ofNat 32 isSha256Address) isSha256Code
  arr32Eq : CodeIn M (BitVec.ofNat 32 arr32EqAddress) arr32EqCode
  arr32Ne : CodeIn M (BitVec.ofNat 32 arr32NeAddress) arr32NeCode

set_option maxRecDepth 100000 in
theorem SvCode.hi {M M' : Word → BitVec 8} (C : SvCode M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    SvCode M' :=
  ⟨codeHi C.self (by decide) (by decide) h, codeHi C.seq (by decide) (by decide) h,
    codeHi C.nest (by decide) (by decide) h, codeHi C.elem (by decide) (by decide) h,
    codeHi C.tlv (by decide) (by decide) h, C.K.hi h, C.gs.hi h,
    codeHi C.derBitString (by decide) (by decide) h,
    codeHi C.derPositiveInteger (by decide) (by decide) h,
    codeHi C.derInteger (by decide) (by decide) h,
    codeHi C.derOptional (by decide) (by decide) h,
    codeHi C.derIntegerIs (by decide) (by decide) h,
    codeHi C.sliceEq (by decide) (by decide) h,
    codeHi C.equalSameLength (by decide) (by decide) h,
    codeHi C.memcmp (by decide) (by decide) h,
    codeHi C.derAlgorithm (by decide) (by decide) h,
    codeHi C.derOid (by decide) (by decide) h,
    codeHi C.sliceNe (by decide) (by decide) h,
    codeHi C.x509ReadTime (by decide) (by decide) h,
    codeHi C.generalizedTime (by decide) (by decide) h,
    codeHi C.dateTime (by decide) (by decide) h,
    codeHi C.timeDigits2 (by decide) (by decide) h,
    codeHi C.timeDigits4 (by decide) (by decide) h,
    codeHi C.allAsciiDigit (by decide) (by decide) h,
    codeHi C.derBooleanTrue (by decide) (by decide) h,
    codeHi C.derOctetString (by decide) (by decide) h,
    codeHi C.listsOid (by decide) (by decide) h,
    codeHi C.derSet (by decide) (by decide) h,
    codeHi C.ecdsaSignature48 (by decide) (by decide) h,
    codeHi C.derScalar48 (by decide) (by decide) h,
    codeHi C.derScalar32 (by decide) (by decide) h,
    codeHi C.zipSkipNext (by decide) (by decide) h,
    codeHi C.isSha256 (by decide) (by decide) h,
    codeHi C.arr32Eq (by decide) (by decide) h,
    codeHi C.arr32Ne (by decide) (by decide) h⟩

/-- Bytes that `sigstore::verify` reads but no step writes: outside the
stack, and not wrapping around. -/
structure SvIn (B rp : Word) (rl : Nat) : Prop where
  sep14 : Sep rp (rl + 14) (B + 0xFFFFEA70) 0x3BF0
  pos : 0 < rp.toNat
  lo : rp.toNat + rl + 14 ≤ 0x40000000

theorem SvIn.sep {B rp : Word} {rl : Nat} (h : SvIn B rp rl) : Sep rp rl (B + 0xFFFFEA70) 0x3BF0 := by
  have := h.sep14.sub (c := 0) (l := rl) (by omega); rwa [add_ofNat_zero] at this

theorem SvIn.fit {B rp : Word} {rl : Nat} (h : SvIn B rp rl) : rp.toNat + rl < 2 ^ 32 := by
  have := h.lo; omega

theorem SvIn.sepLo {B rp : Word} {rl : Nat} (h : SvIn B rp rl) {c n : Nat} (hc : c + n ≤ 0x2660) :
    Sep rp rl (B + BitVec.ofNat 32 c) n := by
  have := h.sep.symm.sub (c := 0x1590 + c) (l := n) (by omega)
  rw [show B + 0xFFFFEA70 + BitVec.ofNat 32 (0x1590 + c) = B + BitVec.ofNat 32 c by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega] at this
  exact this.symm

theorem sv_sp20 (B : Word) : B + 0x21A0 + 0xFFFFFFE0 = B + BitVec.ofNat 32 0x2180 := by
  rw [BitVec.add_assoc]; rfl

theorem sv_off8 (B : Word) (c : Nat) (hc : c + 8 < 2 ^ 32) :
    B + BitVec.ofNat 32 c + 8 = B + BitVec.ofNat 32 (c + 8) := frame_lit _ (by simpa using hc)

theorem sv_off12 (B : Word) (c : Nat) (hc : c + 12 < 2 ^ 32) :
    B + BitVec.ofNat 32 c + 0xC = B + BitVec.ofNat 32 (c + 12) := frame_lit _ (by simpa using hc)

set_option maxHeartbeats 4000000 in
/-- **A call to `Der::sequence`** with the result at `B + oc` and the
reader at `B + dc`, whose unread bytes are `rl` bytes at `rp`. -/
theorem sv_seqB {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {oc dc : Nat}
    (F : Fr B 0x2660) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derSequenceAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + BitVec.ofNat 32 oc) (ha1 : reg n a1 = B + BitVec.ofNat 32 dc)
    (ho1 : 0x21A0 ≤ oc) (ho2 : oc + 16 ≤ 0x2660) (ho3 : oc % 4 = 0)
    (hd1 : 0x21A0 ≤ dc) (hd2 : dc + 16 ≤ 0x2660) (hd3 : dc % 4 = 0)
    (hrp : memLoad32 M (B + BitVec.ofNat 32 (dc + 8)) = rp) (hrl : memLoad32 M (B + BitVec.ofNat 32 (dc + 12)) = rl)
    (hin : SvIn B rp rl.toNat) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q, oidKeep q = true → q ≠ ra → reg n' q = reg n q) ∧
      ∀ x, Sep (B + BitVec.ofNat 32 0x2180) 0x20 x 1 →
        n'.mem x = derNestedMem (derAdvance M (B + BitVec.ofNat 32 dc) rp rl
          (derElement 0x30 (memBytes M rp rl.toNat))) (B + BitVec.ofNat 32 oc) rp
          (derElement 0x30 (memBytes M rp rl.toNat)) x := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have e8 := sv_off8 B dc (by omega)
  have e12 := sv_off12 B dc (by omega)
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have env : NestEnv M (BitVec.ofNat 32 derSequenceAddress + 0x278) (B + 0x21A0) (B + BitVec.ofNat 32 oc)
      (B + BitVec.ofNat 32 dc) := by
    rw [show BitVec.ofNat 32 derSequenceAddress + 0x278 = BitVec.ofNat 32 derNestedAddress from rfl]
    refine ⟨by decide, C.nest, C.elem, C.tlv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hS]; omega
    · rw [hS]; omega
    · rw [F.at _ (by omega)]; omega
    · rw [F.at _ (by omega)]; omega
    · rw [sv_sp20]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [sv_sp20]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [sv_sp20]; exact F.sepHi (by decide) (by decide) (by decide)
    · exact F.sepHi (by omega) (by decide) (by decide)
    · rw [e8]; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [e8]; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [sv_sp20]; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp20, e8]; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp20, e8, e12, hrp, hrl]; exact hin.sepLo (by decide)
    · rw [e8, hrp]; exact hin.pos
    · rw [e8, e12, hrp, hrl]; exact hin.fit
  obtain ⟨n2, c2, pc2, sp2, k2, f2⟩ := derSequence_correct n1 (by decide) (by rw [mem1]; exact C.seq)
    (by rw [mem1]; exact env) pc1 (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0])
    (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [mem1, e8, e12, hrp, hrl, sv_sp20] at f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hk hr => by rw [k2 q hk, r1 q hr], f2⟩

theorem sv_base' (B : Word) (c : Nat) : B + BitVec.ofNat 32 (0x21A0 + c) = B + 0x21A0 + BitVec.ofNat 32 c :=
  (add_ofNat_assoc B 0x21A0 c).symm

/-- **A call to `Der::sequence`**, with the result and the reader at
offsets `oc` and `dc` of the frame. -/
theorem sv_seq {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {oc dc : Nat}
    (F : Fr B 0x2660) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derSequenceAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (ho2 : oc + 16 ≤ 0x4C0) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x4C0) (hd3 : dc % 4 = 0)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl)
    (hin : SvIn B rp rl.toNat) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q, oidKeep q = true → q ≠ ra → reg n' q = reg n q) ∧
      ∀ x, Sep (B + BitVec.ofNat 32 0x2180) 0x20 x 1 →
        n'.mem x = derNestedMem (derAdvance M (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl
          (derElement 0x30 (memBytes M rp rl.toNat))) (B + 0x21A0 + BitVec.ofNat 32 oc) rp
          (derElement 0x30 (memBytes M rp rl.toNat)) x := by
  have := sv_seqB (oc := 0x21A0 + oc) (dc := 0x21A0 + dc) F C s h1 h2 hb hev rsp
    (by rw [ha0, sv_base']) (by rw [ha1, sv_base']) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [show 0x21A0 + dc + 8 = 0x21A0 + (dc + 8) by omega, sv_base', hrp])
    (by rw [show 0x21A0 + dc + 12 = 0x21A0 + (dc + 12) by omega, sv_base', hrl]) hin
  simpa only [sv_base'] using this

end C3.RV32.Sv
