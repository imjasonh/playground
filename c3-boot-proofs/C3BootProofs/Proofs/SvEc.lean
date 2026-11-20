import C3BootProofs.Proofs.SvOk
import C3BootProofs.Proofs.ScalarIsZero256
import C3BootProofs.Proofs.CondSelect
import C3BootProofs.Proofs.NonZero384
import C3BootProofs.Proofs.Bytes2Scalar256
import C3BootProofs.Proofs.ScalarFromSlice256
import C3BootProofs.Proofs.Norm8
import C3BootProofs.Proofs.ByteCompare

/-!
# `sigstore::verify`: the inlined P-256 ECDSA check

`sigstore::verify` checks the image signature with P-256 ECDSA, inlined into
its own code from offset 0xFBA to 0x2034. The wrappers here run its calls
from `sigstore::verify`'s frame.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

/-- The code the inlined P-256 check calls, beyond `SvCode`. -/
structure SvEcCode (M : Word → BitVec 8) : Prop where
  sz : CodeIn M (BitVec.ofNat 32 scalarIsZero256Address) scalarIsZero256Code
  ms : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  lce : CodeIn M (BitVec.ofNat 32 limbCtEqAddress) limbCtEqCode
  uiz : CodeIn M (BitVec.ofNat 32 uintRefIsZeroAddress) uintRefIsZeroCode
  unz : CodeIn M (BitVec.ofNat 32 uintRefIsNonzeroAddress) uintRefIsNonzeroCode
  bb : CodeIn M (BitVec.ofNat 32 blackBoxU8Address) blackBoxU8Code
  cs2 : CodeIn M (BitVec.ofNat 32 condSelect256Address) condSelect256Code
  nz2 : CodeIn M (BitVec.ofNat 32 nonZero256Address) nonZero256Code
  psc : CodeIn M (BitVec.ofNat 32 p256ScalarCtEqAddress) p256ScalarCtEqCode
  uce8 : CodeIn M (BitVec.ofNat 32 uint8CtEqAddress) uint8CtEqCode
  spl8 : CodeIn M (BitVec.ofNat 32 splitAt8Address) splitAt8Code
  cn : CodeIn M (BitVec.ofNat 32 choiceNotAddress) choiceNotCode
  cu2 : CodeIn M (BitVec.ofNat 32 ctUnwrap256Address) ctUnwrap256Code
  unz8 : CodeIn M (BitVec.ofNat 32 uint8IsNonzeroAddress) uint8IsNonzeroCode
  isr : CodeIn M (BitVec.ofNat 32 inScalarRangeAddress) inScalarRangeCode

theorem SvEcCode.sv {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3830) (D : SvEcCode M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : SvEcCode M := by
  have hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))
  exact ⟨codeHi D.sz (by decide) (by decide) hx, codeHi D.ms (by decide) (by decide) hx,
    codeHi D.lce (by decide) (by decide) hx, codeHi D.uiz (by decide) (by decide) hx,
    codeHi D.unz (by decide) (by decide) hx, codeHi D.bb (by decide) (by decide) hx,
    codeHi D.cs2 (by decide) (by decide) hx, codeHi D.nz2 (by decide) (by decide) hx,
    codeHi D.psc (by decide) (by decide) hx, codeHi D.uce8 (by decide) (by decide) hx,
    codeHi D.spl8 (by decide) (by decide) hx, codeHi D.cn (by decide) (by decide) hx,
    codeHi D.cu2 (by decide) (by decide) hx, codeHi D.unz8 (by decide) (by decide) hx,
    codeHi D.isr (by decide) (by decide) hx⟩

set_option maxHeartbeats 8000000 in
/-- **A call to `ScalarValue::<NistP256>::is_zero`** on the scalar at offset
`oc`. -/
theorem sv_szF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {oc : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (EC : SvEcCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 scalarIsZero256Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ho : oc + 32 ≤ 0x1690) (ho4 : oc % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      reg n' a0 = (if ∀ i : Nat, i < 8 →
        memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 oc + BitVec.ofNat 32 (4 * i)) = 0 then 1 else 0) ∧
      SvKeepL B M n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have env : SYEnv n1.mem (BitVec.ofNat 32 scalarIsZero256Address) (B + 0x21A0)
      (B + 0x21A0 + BitVec.ofNat 32 oc) := by
    rw [mem1]
    exact ⟨by decide, EC.sz,
      by rw [show BitVec.ofNat 32 scalarIsZero256Address + 0x11A20 = BitVec.ofNat 32 memsetAddress by decide]; exact EC.ms,
      by rw [show BitVec.ofNat 32 scalarIsZero256Address + 0xA884 = BitVec.ofNat 32 limbCtEqAddress by decide]; exact EC.lce,
      by rw [show BitVec.ofNat 32 scalarIsZero256Address + 0xFFFFFE8C = BitVec.ofNat 32 uintRefIsZeroAddress by decide]
         exact EC.uiz,
      by rw [show BitVec.ofNat 32 scalarIsZero256Address + 0xFFFFFE8C + 0x1A = BitVec.ofNat 32 uintRefIsNonzeroAddress by
           decide]; exact EC.unz,
      by rw [show BitVec.ofNat 32 scalarIsZero256Address + 0xA97E = BitVec.ofNat 32 blackBoxU8Address by decide]; exact EC.bb,
      by rw [hS]; omega, by rw [hS]; omega, sv_al F (by omega) ho4, by rw [sv_at F _ (by omega)]; omega,
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowN (k := 0x44) (by decide) (by decide) ho⟩
  obtain ⟨n2, c2, pc2, sp2, a02, k2, f2⟩ := scalarIsZero256_correct n1 env pc1
    (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  have e1 : B + 0x21A0 + 0xFFFFFFBC = B + BitVec.ofNat 32 0x215C := sv_spX B 0x44 (by decide)
  rw [mem1, e1] at f2
  rw [mem1] at a02
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], a02,
    fun e he _ => ?_, fun x hx => f2 x (svR_spX hx (by decide) (by decide) (by decide))⟩
  exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))

set_option maxHeartbeats 8000000 in
/-- **A call to the P-256 field's `conditional_select`** with the result at
offset `co`, `a` at offset `ca`, `b` among the image's constants, and the
choice `c`. -/
theorem sv_cs2F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o b c : Word} {co ca : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (EC : SvEcCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 condSelect256Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 ca) (ha2 : reg n a2 = b) (ha3 : reg n a3 = c)
    (hc : c = 0 ∨ c = 1) (hco : co + 32 ≤ 0x1690) (hca : ca + 32 ≤ 0x1690)
    (hb1 : 0x3FCC4200 ≤ b.toNat) (hb2 : b.toNat + 32 ≤ 0x3FCC4E60) (hb4 : b.toNat % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      (∀ i, i < 8 → memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 co + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 M (b + BitVec.ofNat 32 (4 * i))
        else memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 ca + BitVec.ofNat 32 (4 * i))) ∧
      SvKeepL B M n'.mem [(co, 32)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have env : CS2Env n1.mem (BitVec.ofNat 32 condSelect256Address) (B + 0x21A0)
      (B + 0x21A0 + BitVec.ofNat 32 co) (B + 0x21A0 + BitVec.ofNat 32 ca) b := by
    rw [mem1]
    exact ⟨by decide, EC.cs2,
      by rw [show BitVec.ofNat 32 condSelect256Address + 0x323E = MCS by decide]; exact C.K.stub,
      by rw [show BitVec.ofNat 32 condSelect256Address + 0x323E + 8 = MCS + 8 by decide]; exact C.K.body,
      by rw [show BitVec.ofNat 32 condSelect256Address + 0xFFFFC076 = BitVec.ofNat 32 sliceCtAssignAddress by decide]
         exact C.K.sca,
      by rw [hS]; omega, by rw [hS]; omega, hb4, by rw [sv_at F _ (by omega)]; omega,
      by rw [sv_at F _ (by omega)]; omega,
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide),
      FS.lowN (k := 0x50) (by decide) (by decide) hco, FS.lowN (k := 0x50) (by decide) (by decide) hca,
      by rw [show B + 0x21A0 + (0xFFFFFFB0 : Word) = B + BitVec.ofNat 32 0x2150 from sv_spX B 0x50 (by decide)]
         exact (F.bufData (c := 0x2150) (n := 0x50) (by decide) hb1 hb2).symm⟩
  obtain ⟨n2, c2, pc2, sp2, W2, k2, f2⟩ := condSelect256_correct n1 env pc1
    (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [r1 a2 (by decide), ha2]) (by rw [r1 a3 (by decide), ha3]) hc
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  have e1 : B + 0x21A0 + 0xFFFFFFB0 = B + BitVec.ofNat 32 0x2150 := sv_spX B 0x50 (by decide)
  rw [mem1, e1] at f2
  rw [mem1] at W2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], W2,
    fun e he hL => ?_, fun x hx => f2 x (svR_spX hx (by decide) (by decide) (by decide)) (svR_hi hx hco)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

set_option maxHeartbeats 8000000 in
/-- **A call to `NonZeroScalar::<NistP256>::new`** on the scalar at offset
`cx`, with the result at offset `co`. -/
theorem sv_nz2F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {co cx : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (EC : SvEcCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 nonZero256Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cx)
    (hco : co + 0x21 ≤ 0x1690) (hcx : cx + 32 ≤ 0x1690) (hcx4 : cx % 4 = 0) (hs : co + 32 ≤ cx ∨ cx + 32 ≤ co) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      (∀ i, i < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 co + BitVec.ofNat 32 i) =
        M (B + 0x21A0 + BitVec.ofNat 32 cx + BitVec.ofNat 32 i)) ∧
      n'.mem (B + 0x21A0 + BitVec.ofNat 32 co + 0x20) =
        (if ∀ i : Nat, i < 8 → memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 cx + BitVec.ofNat 32 (4 * i)) = 0
          then 0 else 1) ∧
      SvKeepL B M n'.mem [(co, 0x21)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have env : NZ2Env n1.mem (BitVec.ofNat 32 nonZero256Address) (B + 0x21A0)
      (B + 0x21A0 + BitVec.ofNat 32 co) (B + 0x21A0 + BitVec.ofNat 32 cx) := by
    rw [mem1]
    exact ⟨by decide, EC.nz2,
      by rw [show BitVec.ofNat 32 nonZero256Address + 0x2700 = MSET by decide]; exact C.K.mset,
      by rw [show BitVec.ofNat 32 nonZero256Address + 0xFFFFFD20 = BitVec.ofNat 32 p256ScalarCtEqAddress by decide]
         exact EC.psc,
      by rw [show BitVec.ofNat 32 nonZero256Address + 0xFFFFFD20 + 0xFFFFFB5E = BitVec.ofNat 32 uint8CtEqAddress by
           decide]; exact EC.uce8,
      by rw [show BitVec.ofNat 32 nonZero256Address + 0xFFFFFD20 + 0xFFFFFB5E + 0x80 = BitVec.ofNat 32 splitAt8Address by
           decide]; exact EC.spl8,
      by rw [show BitVec.ofNat 32 nonZero256Address + 0xFFFFFD20 + 0xFFFFFB5E + 0xFFFFBCE6 =
           BitVec.ofNat 32 limbCtEqAddress by decide]; exact C.K.lce,
      by rw [show BitVec.ofNat 32 nonZero256Address + 0xFFFFFD20 + 0xFFFFFB5E + 0xFFFF12EE =
           BitVec.ofNat 32 uintRefIsZeroAddress by decide]; exact C.K.uiz,
      by rw [show BitVec.ofNat 32 nonZero256Address + 0xFFFFFD20 + 0xFFFFFB5E + 0xFFFF12EE + 0x1A =
           BitVec.ofNat 32 uintRefIsNonzeroAddress by decide]; exact C.K.refnz,
      by rw [show BitVec.ofNat 32 nonZero256Address + 0xFFFFFD20 + 0xFFFFB93E = BitVec.ofNat 32 blackBoxU8Address by
           decide]; exact C.K.bb,
      by rw [show BitVec.ofNat 32 nonZero256Address + 0xFFFFF870 = BitVec.ofNat 32 choiceNotAddress by decide]
         exact EC.cn,
      by rw [show BitVec.ofNat 32 nonZero256Address + 0xFFFFF870 + 0xFFFFBDEE = BitVec.ofNat 32 blackBoxU8Address by
           decide]; exact C.K.bb,
      by rw [show BitVec.ofNat 32 nonZero256Address + 0x2768 = MCS by decide]; exact C.K.stub,
      by rw [show BitVec.ofNat 32 nonZero256Address + 0x2768 + 8 = MCS + 8 by decide]; exact C.K.body,
      by rw [hS]; omega, by rw [hS]; omega, sv_al F (by omega) hcx4, by rw [sv_at F _ (by omega)]; omega,
      by rw [sv_at F _ (by omega)]; omega,
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowN (k := 0x84) (by decide) (by decide) hcx, FS.lowN (k := 0x84) (by decide) (by decide) hco,
      FS.sepHi hco (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide),
      sepS (B + 0x21A0) hs (by omega) (by omega)⟩
  obtain ⟨n2, c2, pc2, sp2, W2, Z2, k2, f2⟩ := nonZero256_correct n1 env pc1
    (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  have e1 : B + 0x21A0 + 0xFFFFFF7C = B + BitVec.ofNat 32 0x211C := sv_spX B 0x84 (by decide)
  rw [mem1, e1] at f2
  rw [mem1] at W2 Z2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], W2, Z2,
    fun e he hL => ?_, fun x hx => f2 x (svR_spX hx (by decide) (by decide) (by decide)) (svR_hi hx hco)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

/-- **A call to `CtOption::<NonZeroScalar<NistP256>>::unwrap`** on the
option at offset `cs`, whose choice byte is 1, into offset `co`: a copy of
the 32 bytes. -/
theorem sv_cu2 {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cs : Nat} (F : Fr B 0x3830)
    (E : SvCode m.mem) (EC : SvEcCode m.mem) (s : St m.mem SV m off (reg m))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 ctUnwrap256Address)
    (he8 : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x21A0) (ha0 : reg m a0 = B + 0x21A0 + BitVec.ofNat 32 co)
    (ha1 : reg m a1 = B + 0x21A0 + BitVec.ofNat 32 cs) (hco : co + 32 ≤ 0x1690) (hcs : cs + 33 ≤ 0x1690)
    (hs : co + 32 ≤ cs ∨ cs + 32 ≤ co) (hch : m.mem (B + 0x21A0 + BitVec.ofNat 32 (cs + 0x20)) = 1) :
    ∃ m', SvPost B m m' (off + 8) ∧ SvKeep B m.mem m'.mem co 32 ∧
      ∀ j, j < 32 → m'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + j)) = m.mem (B + 0x21A0 + BitVec.ofNat 32 (cs + j)) := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  have hb16 : (B + 0x21A0 + 0xFFFFFFF0).toNat = (B + 0x21A0).toNat - 16 := FS.below 16 (by decide) (by decide)
  obtain ⟨fA, fW, hFC⟩ := FS.mc
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [r1 sp (by decide)]; exact hsp
  have R := (ctUnwrap256_correct n1 (out := B + 0x21A0 + BitVec.ofNat 32 co) (s := B + 0x21A0 + BitVec.ofNat 32 cs)
    (by rw [mem1]; exact E.K.panic) (by rw [mem1]; exact EC.cu2) (by rw [mem1]; exact E.K.stub) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8) (by rw [sp1]; exact FS.room (by decide))).1
    (by rw [mem1]; have := hch; rwa [← add_ofNat_assoc] at this)
    (by rw [mem1, sp1]; exact ⟨E.K.body, FS.sepHi (by omega) (by decide) (by decide), hFC, FS.mcN (by omega),
      FS.mcN (by omega), sepS (B + 0x21A0) hs (by omega) (by omega), fA, fW, by rw [FS.at _ (by omega)]; omega,
      by rw [FS.at _ (by omega)]; omega⟩)
  obtain ⟨n2, c2, pc2, sp2, k2, fr2⟩ := R
  rw [sp1, mem1] at fr2
  have lo16 : ∀ x, SvR B x → Sep (B + 0x21A0 + 0xFFFFFFF0) 16 x 1 := fun x hx => svR_lo (k := 16) hx (by decide) (by decide)
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => ?_, fun q hq => ?_⟩,
    fun e he1 he2 => ?_, fun j hj => ?_⟩
  · rw [fr2 x (lo16 x hx), copyBytes_sep (svR_hi (c := co) (l := 32) hx hco) (Nat.le_refl _)]
  · by_cases h : q = sp
    · subst h; rw [sp2, sp1, hsp]
    · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · rw [fr2 _ (FS.lowB hb16 (by decide) (by omega)),
      copyBytes_sep (sepS (B + 0x21A0) (c := co) (n := 32) (d := e) (k := 1) (by omega) (by omega) (by omega))
        (Nat.le_refl _)]
  · rw [fr2 _ (FS.lowB hb16 (by decide) (by omega)), ← add_ofNat_assoc (B + 0x21A0) co j,
      C3.RV32.Dq.cp_at hj (by omega), add_ofNat_assoc]

theorem _root_.C3.RV32.FCEnv.hi {M M' : Word → BitVec 8} (E : FCEnv M)
    (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) : FCEnv M' :=
  ⟨codeHi E.cod (by decide) (by decide) h, codeHi E.ms (by decide) (by decide) h, codeHi E.fl (by decide) (by decide) h,
    codeHi E.cs (by decide) (by decide) h, codeHi E.cb (by decide) (by decide) h⟩

/-- A word in the image's constants survives a change to memory outside the
stack. -/
theorem ld_dataR {M M0 : Word → BitVec 8} {B q : Word} (F : Fr B 0x3830) (fR : ∀ x, SvR B x → M x = M0 x)
    (h1 : 0x3FCC4200 ≤ q.toNat) (h2 : q.toNat + 4 ≤ 0x3FCC4E60) : memLoad32 M q = memLoad32 M0 q :=
  (memLoad32_congr fun j hj => (fR _ (dataR F h1 h2 j hj)).symm).symm

theorem accV_dataR {M M0 : Word → BitVec 8} {B q : Word} {k : Nat} (F : Fr B 0x3830)
    (fR : ∀ x, SvR B x → M x = M0 x) (h1 : 0x3FCC4200 ≤ q.toNat) (h2 : q.toNat + 4 * k ≤ 0x3FCC4E60) :
    accV M q k = accV M0 q k :=
  accV_congr k fun i hi => by
    have e : (q + BitVec.ofNat 32 (4 * i)).toNat = q.toNat + 4 * i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := q.isLt; omega
    exact ld_dataR F fR (by omega) (by omega)

theorem lzLimbs_congr {M M0 : Word → BitVec 8} {q : Word} :
    ∀ k, (∀ i, i < k → memLoad32 M (q + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (q + BitVec.ofNat 32 (4 * i))) →
      lzLimbs M q k = lzLimbs M0 q k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [lzLimbs]
    rw [h k (by omega), lzLimbs_congr k fun i hi => h i (by omega)]

theorem _root_.C3.RV32.BYEnv.sv {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3830) (D : BYEnv M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : BYEnv M := by
  have hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))
  refine ⟨codeHi D.cod (by decide) (by decide) hx, codeHi D.lz (by decide) (by decide) hx, D.pan.hi' hx,
    codeHi D.exu (by decide) (by decide) hx, D.fc.hi hx, codeHi D.bsb (by decide) (by decide) hx,
    codeHi D.bb (by decide) (by decide) hx, codeHi D.cn (by decide) (by decide) hx,
    codeHi D.sca (by decide) (by decide) hx, ?_, ?_⟩
  · rw [accV_dataR F fR (by decide) (by decide)]; exact D.ord
  · rw [lzLimbs_congr 8 fun i hi => by
      have e : (BYO + BitVec.ofNat 32 (4 * i)).toNat = 0x3FCC4268 + 4 * i := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [b2sOrder256Address, BitVec.toNat_ofNat]; omega
      exact ld_dataR F fR (by omega) (by omega)]
    exact D.ordLz

theorem _root_.C3.RV32.BGEnv.sv {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3830) (D : BGEnv M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : BGEnv M := by
  have hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))
  refine ⟨codeHi D.cod (by decide) (by decide) hx, D.fb.hi hx, codeHi D.bsb (by decide) (by decide) hx,
    codeHi D.nz (by decide) (by decide) hx, codeHi D.bb (by decide) (by decide) hx, ?_⟩
  rw [accV_dataR F fR (by decide) (by decide)]; exact D.ord

set_option maxHeartbeats 8000000 in
/-- **A call to `bytes2scalar` for P-256** on the 32 bytes at `b` outside
the stack, with the scalar at offset `co`. -/
theorem sv_by2F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o b : Word} {co : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (BE : BYEnv M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BY)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (ha1 : reg n a1 = b)
    (hco : co + 32 ≤ 0x1690) (hco4 : co % 4 = 0) (hin : SvIn B b 32) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 = beNat (memBytes M b 32) % C3.p256.n ∧
      SvKeepL B M n'.mem [(co, 32)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have e1 : B + 0x21A0 + 0xFFFFFF20 = B + BitVec.ofNat 32 0x20C0 := sv_spX B 0xE0 (by decide)
  have hbl := hin.lo
  obtain ⟨n2, c2, pc2, sp2, k2, A2, f2⟩ := bytes2scalar256_correct n1 (sp0 := B + 0x21A0)
    (out := B + 0x21A0 + BitVec.ofNat 32 co) (b := b) (by rw [mem1]; exact BE) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [r1 sp (by decide), rsp])
    (by rw [hS]; omega) (by rw [hS]; omega) (by rw [hS]; unfold dramEnd; omega)
    (by rw [sv_at F _ (by omega)]; unfold dramEnd; omega) (sv_al F (by omega) hco4) (by omega)
    (by rw [e1]; exact hin.sepLo (by decide))
    (by rw [e1, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (by rw [e1]; exact F.bufData (by decide) (by decide) (by decide))
  rw [mem1, e1] at f2
  rw [mem1] at A2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], A2,
    fun e he hL => ?_, fun x hx => f2 x (svR_spX hx (by decide) (by decide) (by decide)) (svR_hi hx hco)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

set_option maxHeartbeats 8000000 in
/-- **A call to `ScalarValue::<NistP256>::from_slice`** on the 32 bytes at
offset `cb`, with the result at offset `co`: a word that is 0 with the
scalar after it when the bytes are below the order, and 1 otherwise. -/
theorem sv_sf2F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {co cb : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (BG : BGEnv M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BV)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cb)
    (hco : co + 36 ≤ 0x1690) (hco4 : co % 4 = 0) (hcb : cb + 32 ≤ 0x1690) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      (beNat (memBytes M (B + 0x21A0 + BitVec.ofNat 32 cb) 32) < C3.p256.n →
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) = 0 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co + 4) 8 = beNat (memBytes M (B + 0x21A0 + BitVec.ofNat 32 cb) 32)) ∧
      (C3.p256.n ≤ beNat (memBytes M (B + 0x21A0 + BitVec.ofNat 32 cb) 32) →
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) = 1) ∧
      SvKeepL B M n'.mem [(co, 36)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have e1 : B + 0x21A0 + 0xFFFFFF40 = B + BitVec.ofNat 32 0x20E0 := sv_spX B 0xC0 (by decide)
  obtain ⟨n2, c2, pc2, sp2, k2, L2, G2, f2⟩ := scalarFromSlice256_correct n1 (sp0 := B + 0x21A0)
    (out := B + 0x21A0 + BitVec.ofNat 32 co) (b := B + 0x21A0 + BitVec.ofNat 32 cb) (by rw [mem1]; exact BG) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [r1 sp (by decide), rsp])
    (by rw [hS]; omega) (by rw [hS]; omega) (by rw [hS]; omega)
    (by rw [sv_at F _ (by omega)]; omega) (sv_al F (by omega) hco4)
    (by rw [e1, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (by rw [e1, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (by rw [e1]; exact F.bufData (by decide) (by decide) (by decide))
  rw [mem1, e1] at f2
  rw [mem1] at L2 G2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], L2, G2,
    fun e he hL => ?_, fun x hx => f2 x (svR_spX hx (by decide) (by decide) (by decide)) (svR_hi hx hco)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

set_option maxHeartbeats 8000000 in
/-- **A call to `Uint<8>::is_nonzero`** on the limbs at offset `cx`. -/
theorem sv_unz8F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {cx : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (EC : SvEcCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 uint8IsNonzeroAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 cx)
    (hcx : cx + 32 ≤ 0x1690) (hcx4 : cx % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      reg n' a0 = (if ∀ i : Nat, i < 8 →
        memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 cx + BitVec.ofNat 32 (4 * i)) = 0 then 0 else 1) ∧
      SvKeepL B M n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [r1 sp (by decide), rsp]
  have eU : BitVec.ofNat 32 uint8IsNonzeroAddress + 0xFFFF120E = BitVec.ofNat 32 uintRefIsNonzeroAddress := by decide
  obtain ⟨n2, c2, pc2, a02, k2, f2⟩ := uint8IsNonzero_correct n1 (base := BitVec.ofNat 32 uint8IsNonzeroAddress)
    (by decide) (by rw [mem1]; exact EC.unz8) (by rw [mem1, eU]; exact C.K.refnz) pc1
    (by rw [r1 a0 (by decide), ha0]) (sv_al F (by omega) hcx4) (by rw [sp1, hS]; omega)
    (by rw [sp1, sv_sp4, eU]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [sp1, sv_sp4] at f2
  rw [mem1] at a02
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [k2 sp (by decide) (by decide) (by decide)
    (by decide) (by decide), sp1], fun r hr => ?_, a02, fun e he _ => ?_, fun x hx => ?_⟩
  · have hr' : r ≠ a0 ∧ r ≠ a1 ∧ r ≠ a2 ∧ r ≠ a3 ∧ r ≠ t1 ∧ r ≠ ra := by revert hr; revert r; decide
    obtain ⟨q10, q11, q12, q13, q6, q1⟩ := hr'
    rw [k2 r q10 q11 q12 q13 q6, r1 r q1]
  · rw [f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega)), mem1]
  · rw [f2 x (svR_sp4 hx), mem1]

/-- **A call to `ecdsa::in_scalar_range`** on the 32 bytes at offset `cx`
and the 32 bytes of the order at `y`. -/
theorem sv_isrF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o y : Word} {cx : Nat}
    (C : SvCode M) (EC : SvEcCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 inScalarRangeAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 cx) (ha1 : reg n a1 = BitVec.ofNat 32 0x20)
    (ha2 : reg n a2 = y) (ha3 : reg n a3 = BitVec.ofNat 32 0x20) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      reg n' a0 = (if inScalarRange (memBytes M (B + 0x21A0 + BitVec.ofNat 32 cx) 32) (memBytes M y 32) then 1 else 0) ∧
      n'.mem = M := by
  obtain ⟨n', c', s', a0', k'⟩ := c_isr (k := 32) (k' := 32) s C.self EC.isr h1 h2 hb hev ha0 ha1 ha2 ha3
    (by decide) (by decide)
  exact ⟨n', c', ⟨s'.pc, rfl, fun _ => rfl⟩, fun q hq => k' q (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), a0',
    s'.mem⟩

/-- **The error exit at 0x24A4**: the image signature failed the P-256
check, `Err(0x10)`. -/
theorem sv_fail_24a4 {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem)
    (s : St n.mem SV n 0x24A4 (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) : SvErrRet B out v n0 := by
  have hz := s.zero
  have sOC := hO.code
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x24A8) [.lui a0 0x1000, .aluImm .add a0 a0 0x1] E.self (by decide)
    ⟨trivial, trivial, trivial⟩
  have a01 : reg n1 a0 = 0x1001 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte, aluEval]
  have r1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs]; simp only [runBlock, BInstr.run]; rw [updz (by rfl) hq, updz hz hq]
  have M1 : n1.mem = n.mem := u1.mem
  have s1 : St n.mem SV n1 0x24A8 (reg n1) := ⟨u1.pc, M1, fun _ => rfl⟩
  obtain ⟨n2, d2, u2⟩ := s1.jump E.self sv_at_24a8 (off' := 0x2A88) (by decide) (by rw [s1.pc]; decide)
  have s2 : St n.mem SV n2 0x2A88 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have e0 : reg n2 (18 : Fin 32) + 0 = out := by rw [u2.regs, r1 _ (by decide), hout]; exact BitVec.add_zero _
  obtain ⟨n3, d3, u3⟩ := s2.sh E.self sv_at_2a88 (off' := 0x2A8C) (by decide) (by rw [e0]; exact hO.al)
  rw [e0, u2.regs, a01] at u3
  have M3 : n3.mem = memStore8 (memStore8 n.mem out 1) (out + 1) 0x10 := by rw [u3.mem]; rfl
  have C3 : CodeIn n3.mem SV sigstoreVerifyCode := by
    rw [M3]; exact (E.self.store8 (by have := sOC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this)).store8
      (sOC.sub (c := 1) (l := 1) (by decide))
  have s3 : St n3.mem SV n3 0x2A8C (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  obtain ⟨n4, d4, u4⟩ := s3.jump C3 sv_at_2a8c (off' := 0x970) (by decide) (by rw [s3.pc]; decide)
  have s4 : St n3.mem SV n4 0x970 (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
  refine sv_ret_err (n := n4) (M := n3.mem) F C3 s4
    (t.trans (c1.trans ((Steps.single d2).trans ((Steps.single d3).trans (.single d4)))))
    (by rw [M3]; exact saves_out2 hO V) hret
    (by rw [u4.regs, u3.regs, u2.regs, r1 sp (by decide), rsp]) (by rw [u4.regs, u3.regs, u2.regs, r1 3 (by decide), r3])
    (by rw [u4.regs, u3.regs, u2.regs, r1 4 (by decide), r4]) ?_ ?_
  · rw [M3, memStore8_ne (out_ne1 out), memStore8_same]
  · intro x hx h0 h1; rw [M3, memStore8_ne h1, memStore8_ne h0, fR x hx]

theorem mb_dataR {M M0 : Word → BitVec 8} {B q : Word} {k : Nat} (F : Fr B 0x3830)
    (fR : ∀ x, SvR B x → M x = M0 x) (h1 : 0x3FCC4200 ≤ q.toNat) (h2 : q.toNat + k ≤ 0x3FCC4E60) :
    memBytes M q k = memBytes M0 q k :=
  memBytes_congr fun i hi => fR _ (dataR F h1 h2 i hi)

theorem zext_eq4 : ∀ b : BitVec 8, b.zeroExtend 32 = BitVec.ofNat 32 0x4 ↔ b = 4 := by decide

/-- The limbs of a region an `SvKeep` keeps. -/
theorem SvKeep.acc {B : Word} {M M' : Word → BitVec 8} {c w d n : Nat} (K : SvKeep B M M' c w)
    (hd : d + 4 * n ≤ 0x1690) (h : d + 4 * n ≤ c ∨ c + w ≤ d) :
    accV M' (B + 0x21A0 + BitVec.ofNat 32 d) n = accV M (B + 0x21A0 + BitVec.ofNat 32 d) n :=
  accV_S n fun q hq => K.range hd h q hq

/-- The limbs of a region an `SvKeepL` keeps. -/
theorem SvKeepL.acc {B : Word} {M M' : Word → BitVec 8} {L : List (Nat × Nat)} {d n : Nat} (K : SvKeepL B M M' L)
    (hd : d + 4 * n ≤ 0x1690) (h : ∀ p ∈ L, d + 4 * n ≤ p.1 ∨ p.1 + p.2 ≤ d) :
    accV M' (B + 0x21A0 + BitVec.ofNat 32 d) n = accV M (B + 0x21A0 + BitVec.ofNat 32 d) n :=
  accV_S n fun q hq => K.range hd h q hq

set_option maxHeartbeats 8000000 in
/-- **A call to `VerifyingKey::from_sec1_bytes`** on the 65 bytes at `inp`,
with the result at offset `oc`, including the accepted point's coordinates. -/
theorem sv_gsFull {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o inp : Word} {oc : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (D : P2Data M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 p256FromSec1Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc) (ha1 : reg n a1 = inp)
    (ho2 : oc + 0x48 ≤ 0x1690) (ho3 : oc % 4 = 0) (hin : SvIn B inp 0x41) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 0x48)] ∧
      (GsOk M inp → memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) = 0 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 (oc + 4)) 8 = gsVal M inp 1 * 2 ^ 256 % p256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 (oc + 0x24)) 8 = gsVal M inp 0x21 * 2 ^ 256 % p256 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 (oc + 0x44)) = 0) ∧
      (¬ GsOk M inp → memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) = 1) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have FS : Fr (B + BitVec.ofNat 32 0x1ED0) 0x2D0 := F.sub (by decide) (by decide)
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have eo : B + 0x21A0 + BitVec.ofNat 32 oc = B + BitVec.ofNat 32 (0x21A0 + oc) := (sv_base' B oc).symm
  have eS : B + BitVec.ofNat 32 0x1ED0 + 0xFFFFFE60 = B + BitVec.ofNat 32 0x1D30 := by
    rw [BitVec.add_assoc]; rfl
  obtain ⟨n2, c2, R, Ok, Er⟩ := p256FromSec1_correct n1 (S := B + BitVec.ofNat 32 0x1ED0) (inp := inp)
    (out := B + 0x21A0 + BitVec.ofNat 32 oc) (by rw [mem1]; exact C.gs) (by rw [mem1]; exact D) FS pc1
    (by rw [r1 sp (by decide), rsp, sv_sp2d0]) (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]; exact even_clear _ hev)
    (by rw [eS]; exact hin.sepLo (by decide))
    (by have := hin.lo; omega) (sv_al F (by omega) ho3) (by rw [sv_at F _ (by omega)]; omega)
    (by rw [eS, eo]; exact sepS B (by omega) (by omega) (by omega))
  obtain ⟨pc2, sp2, sv2, k2, f2⟩ := R
  rw [mem1] at f2 Ok Er
  have hfS : ∀ x, SvR B x → Sep (B + BitVec.ofNat 32 0x1D30) 0x470 x 1 := fun x hx => by
    have := svR_lo (k := 0x470) hx (by decide) (by decide)
    rwa [sv_lo B 0x470 (by decide)] at this
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2, regs1]; simp +decide [upd], rfl, fun _ => rfl⟩,
    by rw [sp2, ← sv_sp2d0], fun q hq => ?_, fun e he hL => ?_, fun h => ?_, Er,
    fun x hx => f2 x (by rw [eS]; exact hfS x hx) (svR_hi hx ho2)⟩
  · have hq' : q.val ∈ [3, 4, 26, 27] ∨ ∃ k, k < 11 ∧ savedReg k = q := by
      revert hq; revert q; decide
    rcases hq' with hq' | ⟨k, hk, rfl⟩
    · rw [k2 q hq', r1 q (by revert hq'; revert q; decide)]
    · rw [sv2 k hk, r1 _ (fun e => by rw [e] at hq; revert hq; decide)]
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact f2 _ (by rw [eS, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (by rw [eo, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
  · obtain ⟨o1, o2, o3, o4⟩ := Ok h
    refine ⟨o1, ?_, ?_, ?_⟩
    · rw [← add_ofNat_assoc]; exact o2
    · rw [← add_ofNat_assoc]; exact o3
    · rw [← add_ofNat_assoc]; exact o4

theorem accV_zero_iff {M : Word → BitVec 8} {b : Word} :
    ∀ n, accV M b n = 0 ↔ ∀ i, i < n → memLoad32 M (b + BitVec.ofNat 32 (4 * i)) = 0
  | 0 => by simp [accV]
  | n + 1 => by
    simp only [accV]
    rw [Nat.add_eq_zero_iff, accV_zero_iff n]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h1 i hi
      · have hp : 0 < 2 ^ (32 * i) := Nat.pow_pos (by decide)
        have : (memLoad32 M (b + BitVec.ofNat 32 (4 * i))).toNat = 0 := by
          rcases Nat.mul_eq_zero.mp h2 with h | h
          · exact h
          · omega
        exact BitVec.eq_of_toNat_eq this
    · intro h
      refine ⟨fun i hi => h i (by omega), ?_⟩
      rw [h n (by omega), show (0 : Word).toNat = 0 from rfl, Nat.zero_mul]

/-- The limbs at `b` are all zero exactly when the value they hold is. -/
theorem limbs0_iff {M : Word → BitVec 8} {b : Word} {v : Nat} (h : accV M b 8 = v) :
    (∀ i, i < 8 → memLoad32 M (b + BitVec.ofNat 32 (4 * i)) = 0) ↔ v = 0 := by
  rw [← h, accV_zero_iff]

theorem gsVal_sv {M M0 : Word → BitVec 8} {B inp : Word} {o : Nat} (fR : ∀ x, SvR B x → M x = M0 x)
    (hin : SvIn B inp 0x41) (ho : o + 32 ≤ 0x41) : gsVal M inp o = gsVal M0 inp o := by
  unfold gsVal
  have e : memBytes M (inp + BitVec.ofNat 32 o) 32 = memBytes M0 (inp + BitVec.ofNat 32 o) 32 :=
    memBytes_congr fun i hi => by rw [add_ofNat_assoc]; exact fR _ (hin.r (by omega))
  rw [e]

end C3.RV32.Sv
