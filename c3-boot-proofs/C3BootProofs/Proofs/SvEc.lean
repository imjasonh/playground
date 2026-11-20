import C3BootProofs.Proofs.SvOk
import C3BootProofs.Proofs.ScalarIsZero256
import C3BootProofs.Proofs.CondSelect
import C3BootProofs.Proofs.NonZero384

/-!
# `sigstore::verify`: the inlined P-256 ECDSA check

`sigstore::verify` checks the image signature with P-256 ECDSA, inlined into
its own code from offset 0xFBA to 0x2034. The wrappers here run its calls
from `sigstore::verify`'s frame.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

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
    codeHi D.spl8 (by decide) (by decide) hx, codeHi D.cn (by decide) (by decide) hx⟩

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

end C3.RV32.Sv
