import C3BootProofs.Proofs.SvTs1
import C3BootProofs.Proofs.DerReaders
import C3BootProofs.Proofs.IsSha256

/-!
# `sigstore::verify`: wrappers for the timestamp's DER

`Der::set` and `Der::nested`, as the generated stages track them.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- `Der::nested`'s environment for a result at offset `oc` and a reader at
offset `dc` of the frame. -/
theorem sv_nestEnv {M : Word → BitVec 8} {B : Word} {rp rl : Word} {oc dc : Nat} (F : Fr B 0x3830) (C : SvCode M)
    (ho2 : oc + 16 ≤ 0x1690) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl) (hin : SvIn B rp rl.toNat) :
    NestEnv M (BitVec.ofNat 32 derNestedAddress) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 oc)
      (B + 0x21A0 + BitVec.ofNat 32 dc) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have eO : B + 0x21A0 + BitVec.ofNat 32 oc = B + BitVec.ofNat 32 (0x21A0 + oc) := (sv_base' B oc).symm
  have eD : B + 0x21A0 + BitVec.ofNat 32 dc + 8 = B + BitVec.ofNat 32 (0x21A0 + (dc + 8)) := by
    rw [d8]; exact (sv_base' B (dc + 8)).symm
  refine ⟨by decide, C.nest, C.elem, C.tlv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hS]; omega
  · rw [hS]; omega
  · exact sv_al F (by omega) ho3
  · exact sv_al F (by omega) hd3
  · rw [sv_sp20]; exact F.sepHi (by decide) (by decide) (by decide)
  · rw [sv_sp20]; exact F.sepHi (by decide) (by decide) (by decide)
  · rw [sv_sp20]; exact F.sepHi (by decide) (by decide) (by decide)
  · rw [eO]; exact F.sepHi (by omega) (by decide) (by decide)
  · rw [eD]; exact F.sepHi (by omega) (by decide) (by decide)
  · rw [eD]; exact F.sepHi (by omega) (by decide) (by decide)
  · rw [eO, sv_sp20]; exact sepS B (by omega) (by omega) (by omega)
  · rw [eD, sv_sp20]; exact sepS B (by omega) (by omega) (by omega)
  · rw [d8, d12, hrp, hrl, sv_sp20]; exact hin.sepLo (by decide)
  · rw [d8, hrp]; exact hin.pos
  · rw [d8, d12, hrp, hrl]; exact hin.fit

set_option maxHeartbeats 8000000 in
/-- **A call to `Der::set`**, as the generated stages track it. -/
theorem sv_setF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {oc dc : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derSetAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (ho2 : oc + 16 ≤ 0x1690) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0)
    (hs : oc + 16 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl)
    (hin : SvIn B rp rl.toNat) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q, oidKeep q = true → q ≠ ra → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 16), (dc + 8, 8)] ∧
      (∀ t, derElement 0x31 (memBytes M rp rl.toNat) = .ok t → DerOkW n'.mem B oc dc rp rl t) ∧
      (∀ e, derElement 0x31 (memBytes M rp rl.toNat) = .error e → DerErrW n'.mem B oc e) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have env := sv_nestEnv F C ho2 ho3 hd2 hd3 hrp hrl hin
  obtain ⟨n2, c2, pc2, sp2, k2, f2⟩ := derSet_correct n1 (by decide) (by rw [mem1]; exact C.derSet)
    (by rw [mem1, show BitVec.ofNat 32 derSetAddress + 0xFFFFF940 = BitVec.ofNat 32 derNestedAddress from rfl]; exact env)
    pc1 (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0])
    (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [mem1, d8, d12, hrp, hrl, sv_sp20] at f2
  obtain ⟨K, Ok, Er, fr⟩ := dnm_facts _ ho2 ho3 hd2 hd3 hs f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hk hr => by rw [k2 q hk, r1 q hr], K, Ok, Er, fr⟩

set_option maxHeartbeats 8000000 in
/-- **A call to `Der::nested`** with tag `tag`, as the generated stages track it. -/
theorem sv_nestF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {oc dc tag : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derNestedAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 dc) (ha2 : reg n a2 = BitVec.ofNat 32 tag) (htag : tag < 256)
    (ho2 : oc + 16 ≤ 0x1690) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0)
    (hs : oc + 16 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl)
    (hin : SvIn B rp rl.toNat) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q, oidKeep q = true → q ≠ ra → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 16), (dc + 8, 8)] ∧
      (∀ t, derElement tag (memBytes M rp rl.toNat) = .ok t → DerOkW n'.mem B oc dc rp rl t) ∧
      (∀ e, derElement tag (memBytes M rp rl.toNat) = .error e → DerErrW n'.mem B oc e) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have env := sv_nestEnv F C ho2 ho3 hd2 hd3 hrp hrl hin
  obtain ⟨n2, c2, pc2, sp2, k2, f2⟩ := derNested_correct n1 (tag := tag) (by rw [mem1]; exact env)
    pc1 (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0])
    (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2]) htag (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev)
  rw [mem1, d8, d12, hrp, hrl, sv_sp20] at f2
  obtain ⟨K, Ok, Er, fr⟩ := dnm_facts _ ho2 ho3 hd2 hd3 hs f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hk hr => by rw [k2 q hk, r1 q hr], K, Ok, Er, fr⟩

theorem sv_spA0 (B : Word) : B + 0x21A0 + 0xFFFFFF60 = B + BitVec.ofNat 32 0x2100 := by
  rw [BitVec.add_assoc]; rfl

set_option maxRecDepth 100000 in
/-- The SHA-256 OID that `tsa::is_sha256` compares against is the image's. -/
theorem sv_isOid {M : Word → BitVec 8} (D : SvData M) : memBytes M isOid 9 = sha256OidData := by
  rw [show isOid = SVK + BitVec.ofNat 32 0x68 from rfl, D.mb (by decide)]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **A call to `tsa::is_sha256`** on the reader at offset `dc`. -/
theorem sv_isShaF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {dc : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (D : SvData M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 isSha256Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl)
    (hin : SvIn B rp rl.toNat) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(dc + 8, 8)] ∧
      (∀ t, derElement 0x30 (memBytes M rp rl.toNat) = .ok t → DerAdvW n'.mem B dc rp rl t) ∧
      (match isSha256Of M rp rl.toNat with
        | .error b => reg n' a0 = 1 ∧ reg n' a1 = b.zeroExtend 32
        | .ok v => reg n' a0 = 0 ∧ reg n' a1 = if v then 1 else 0) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have eD : B + 0x21A0 + BitVec.ofNat 32 dc + 8 = B + BitVec.ofNat 32 (0x21A0 + (dc + 8)) := by
    rw [d8]; exact (sv_base' B (dc + 8)).symm
  have ro : ∀ {c k : Nat}, c + k ≤ 0x3830 → Sep isOid 9 (B + BitVec.ofNat 32 c) k := fun hc =>
    (SvRo.sep F (.inr ⟨by decide, by decide⟩) hc).symm
  have env : ISEnv M (BitVec.ofNat 32 isSha256Address) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl.toNat := by
    refine ⟨by decide, C.isSha256, C.derAlgorithm, C.seq, C.nest, C.elem, C.tlv, C.derOid, C.K.stub, C.K.body,
      C.sliceEq, C.equalSameLength, C.memcmp, sv_isOid D, ?_, ?_, ?_, by rw [d8, hrp], by rw [d12, hrl, ofNat_toNat_self],
      hin.pos, hin.fit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · rw [hS]; omega
    · rw [hS]; omega
    · exact sv_al F (by omega) hd3
    iterate 12 (· rw [sv_spA0]; exact F.sepHi (by decide) (by decide) (by decide))
    iterate 11 (· rw [eD]; exact F.sepHi (by omega) (by decide) (by decide))
    · rw [eD, sv_spA0]; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_spA0]; exact hin.sepLo (by decide)
    · rw [eD]; exact hin.sepLo (by omega)
    · rw [sv_spA0]; exact ro (by decide)
    · rw [eD]; exact ro (by omega)
  obtain ⟨n2, c2, pc2, sp2, k2, f2, R2⟩ := isSha256_correct n1 (by rw [mem1]; exact env) pc1
    (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0]) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev)
  rw [mem1] at f2 R2
  rw [sv_spA0, ofNat_toNat_self] at f2
  obtain ⟨K, A, fr⟩ := dad_facts (kf := 0xA0) _ (by decide) (by decide) hd2 hd3 f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], K, A, R2, fr⟩

end C3.RV32.Sv
