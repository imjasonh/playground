import C3BootProofs.Proofs.SvP256
import C3BootProofs.Proofs.ListsOid

/-!
# `sigstore::verify`: the readers the extensions loop calls

`Der::oid`, `Der::octet_string`, `Der::integer`, `Der::boolean_true`,
`Der::tlv`, and `der::lists_oid`, from the frame of `sigstore::verify`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

theorem derOidMem_eq (M : Word → BitVec 8) (out rp : Word) (r : Except DerError DerTlv) :
    derOidMem M out rp r = derSliceMem M out (derContent rp r) := by
  cases r <;> rfl

/-- The callee environment of a reader with a 0x20-byte frame, called from
the frame with its result at `oc` and the reader at `dc`. -/
theorem sv_dce {M : Word → BitVec 8} {B rp rl : Word} {code : List Nat} {P e : Word} {oc dc ol : Nat}
    (F : Fr B 0x3830) (hP : P.toNat % 2 = 0) (hE : (P + e).toNat % 2 = 0) (hc : CodeIn M P code)
    (hel : CodeIn M (P + e) derElementCode) (htl : CodeIn M (P + e + 0x26) derTlvCode)
    (hP1 : 0x40000000 ≤ P.toNat) (hP2 : P.toNat + code.length ≤ 2 ^ 32)
    (hE1 : 0x40000000 ≤ (P + e).toNat) (hE2 : (P + e).toNat + derElementCode.length ≤ 2 ^ 32)
    (hT1 : 0x40000000 ≤ (P + e + 0x26).toNat) (hT2 : (P + e + 0x26).toNat + derTlvCode.length ≤ 2 ^ 32)
    (ho2 : oc + ol ≤ 0x1690) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl) (hin : SvIn B rp rl.toNat) :
    DerCallEnv M code P e (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 oc) (B + 0x21A0 + BitVec.ofNat 32 dc) ol := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  refine ⟨hP, hE, hc, hel, htl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hS]; omega
  · rw [hS]; omega
  · exact sv_al F (by omega) ho3
  · exact sv_al F (by omega) hd3
  · rw [sv_sp20]; exact F.sepHi (by decide) hP1 hP2
  · rw [sv_sp20]; exact F.sepHi (by decide) hE1 hE2
  · rw [sv_sp20]; exact F.sepHi (by decide) hT1 hT2
  · rw [← sv_base']; exact F.sepHi (by omega) hP1 hP2
  · rw [d8, ← sv_base']; exact F.sepHi (by omega) hP1 hP2
  · rw [d8, ← sv_base']; exact F.sepHi (by omega) hT1 hT2
  · rw [sv_sp20, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
  · rw [sv_sp20, d8, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
  · rw [sv_sp20, d8, d12, hrp, hrl]; exact hin.sepLo (by decide)
  · rw [d8, hrp]; exact hin.pos
  · rw [d8, d12, hrp, hrl]; exact hin.fit

set_option maxHeartbeats 8000000 in
/-- **A call to `Der::octet_string`** with the result at offset `oc` and the
reader at offset `dc`. -/
theorem sv_octF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {oc dc : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derOctetStringAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (ho2 : oc + 8 ≤ 0x1690) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0)
    (hs : oc + 8 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl)
    (hin : SvIn B rp rl.toNat) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q, oidKeep q = true → q ≠ ra → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 8), (dc + 8, 8)] ∧
      (∀ t, derElement 4 (memBytes M rp rl.toNat) = .ok t → DerAdvW n'.mem B dc rp rl t) ∧
      (∀ p l, derContent rp (derElement 4 (memBytes M rp rl.toNat)) = .ok (p, l) → SliceW n'.mem B oc p l) ∧
      (∀ e, derContent rp (derElement 4 (memBytes M rp rl.toNat)) = .error e → DerErrW n'.mem B oc e) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have env := sv_dce (code := derOctetStringCode) (P := BitVec.ofNat 32 derOctetStringAddress) (e := 0xFFFFF792)
    (ol := 8) F (by decide) (by decide) C.derOctetString C.elem C.tlv (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ho2 ho3 hd2 hd3 hrp hrl hin
  obtain ⟨n2, c2, pc2, sp2, k2, f2⟩ := derOctetString_correct n1 (by rw [mem1]; exact env)
    pc1 (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0])
    (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [mem1, d8, d12, hrp, hrl, sv_sp20] at f2
  obtain ⟨K, A, Ok, Er, fr⟩ := dsm_facts (kf := 0x20) _ _ (by decide) (by decide) ho2 ho3 hd2 hd3 hs f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hk hr => by rw [k2 q hk, r1 q hr],
    K, A, Ok, Er, fr⟩

set_option maxHeartbeats 8000000 in
/-- **A call to `Der::integer`** with the result at offset `oc` and the
reader at offset `dc`. -/
theorem sv_intF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {oc dc : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derIntegerAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (ho2 : oc + 8 ≤ 0x1690) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0)
    (hs : oc + 8 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl)
    (hin : SvIn B rp rl.toNat) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q, oidKeep q = true → q ≠ ra → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 8), (dc + 8, 8)] ∧
      (∀ t, derElement 2 (memBytes M rp rl.toNat) = .ok t → DerAdvW n'.mem B dc rp rl t) ∧
      (∀ p l, derIntOf (memBytes M rp rl.toNat) rp (derElement 2 (memBytes M rp rl.toNat)) = .ok (p, l) →
        SliceW n'.mem B oc p l) ∧
      (∀ e, derIntOf (memBytes M rp rl.toNat) rp (derElement 2 (memBytes M rp rl.toNat)) = .error e →
        DerErrW n'.mem B oc e) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have env := sv_dce (code := derIntegerCode) (P := BitVec.ofNat 32 derIntegerAddress) (e := 0x5E)
    (ol := 8) F (by decide) (by decide) C.derInteger C.elem C.tlv (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ho2 ho3 hd2 hd3 hrp hrl hin
  obtain ⟨n2, c2, pc2, sp2, k2, f2⟩ := derInteger_correct n1 (by rw [mem1]; exact env)
    (by rw [mem1, d8, d12, hrp, hrl, ← sv_base']; exact (hin.sepLo (by omega)).symm)
    pc1 (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0])
    (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [mem1, d8, d12, hrp, hrl, sv_sp20] at f2
  obtain ⟨K, A, Ok, Er, fr⟩ := dsm_facts (kf := 0x20) _ _ (by decide) (by decide) ho2 ho3 hd2 hd3 hs f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hk hr => by rw [k2 q hk, r1 q hr],
    K, A, Ok, Er, fr⟩

set_option maxHeartbeats 8000000 in
/-- **A call to `Der::boolean_true`** on the reader at offset `dc`. -/
theorem sv_boolF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {dc : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derBooleanTrueAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl)
    (hin : SvIn B rp rl.toNat) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q, oidKeep q = true → q ≠ ra → reg n' q = reg n q) ∧
      reg n' a0 = derUnitWord (derBoolOf (memBytes M rp rl.toNat) (derElement 1 (memBytes M rp rl.toNat))) ∧
      SvKeepL B M n'.mem [(dc + 8, 8)] ∧
      (∀ t, derElement 1 (memBytes M rp rl.toNat) = .ok t → DerAdvW n'.mem B dc rp rl t) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have env := sv_dce (code := derBooleanTrueCode) (P := BitVec.ofNat 32 derBooleanTrueAddress) (e := 0xFFFFF4F2)
    (oc := dc) (ol := 0) F (by decide) (by decide) C.derBooleanTrue C.elem C.tlv (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by omega) hd3 hd2 hd3 hrp hrl hin
  obtain ⟨n2, c2, pc2, sp2, k2, a02, f2⟩ := derBooleanTrue_correct n1 (by rw [mem1]; exact env)
    (by rw [mem1, d8, d12, hrp, hrl, ← sv_base']; exact (hin.sepLo (by omega)).symm)
    pc1 (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [mem1, d8, d12, hrp, hrl, sv_sp20] at f2
  rw [mem1, d8, d12, hrp, hrl] at a02
  obtain ⟨K, A, fr⟩ := dad_facts (kf := 0x20) _ (by decide) (by decide) hd2 hd3 f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hk hr => by rw [k2 q hk, r1 q hr],
    a02, K, A, fr⟩

set_option maxHeartbeats 8000000 in
/-- **A call to `Der::oid`** with the result at offset `oc` and the reader
at offset `dc`. -/
theorem sv_oidF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {oc dc : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derOidAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (ho2 : oc + 8 ≤ 0x1690) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0)
    (hs : oc + 8 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl)
    (hin : SvIn B rp rl.toNat) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q, oidKeep q = true → q ≠ ra → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 8), (dc + 8, 8)] ∧
      (∀ t, derElement 6 (memBytes M rp rl.toNat) = .ok t → DerAdvW n'.mem B dc rp rl t) ∧
      (∀ p l, derContent rp (derOid (memBytes M rp rl.toNat)) = .ok (p, l) → SliceW n'.mem B oc p l) ∧
      (∀ e, derContent rp (derOid (memBytes M rp rl.toNat)) = .error e → DerErrW n'.mem B oc e) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have env : OidEnv M (BitVec.ofNat 32 derOidAddress) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 oc)
      (B + 0x21A0 + BitVec.ofNat 32 dc) := by
    refine ⟨by decide, C.derOid, C.elem, C.tlv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hS]; omega
    · rw [hS]; omega
    · exact sv_al F (by omega) ho3
    · exact sv_al F (by omega) hd3
    · rw [sv_sp20]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [sv_sp20]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [sv_sp20]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [d8, ← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [d8, ← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [sv_sp20, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp20, d8, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp20, d8, d12, hrp, hrl]; exact hin.sepLo (by decide)
    · rw [d8, d12, hrp, hrl, ← sv_base']; exact hin.sepLo (by omega)
    · rw [d8, hrp]; exact hin.pos
    · rw [d8, d12, hrp, hrl]; exact hin.fit
  obtain ⟨n2, c2, pc2, sp2, k2, f2⟩ := derOid_correct n1 (by rw [mem1]; exact env)
    pc1 (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0])
    (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [mem1, d8, d12, hrp, hrl, sv_sp20] at f2
  simp only [derOidMem_eq] at f2
  obtain ⟨K, A, Ok, Er, fr⟩ := dsm_facts (kf := 0x20) _ _ (by decide) (by decide) ho2 ho3 hd2 hd3 hs f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hk hr => by rw [k2 q hk, r1 q hr],
    K, A, Ok, Er, fr⟩

set_option maxHeartbeats 8000000 in
/-- **A call to `Der::tlv`** with the result at offset `oc` and the reader
at offset `dc`. -/
theorem sv_tlvF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {oc dc : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derTlvAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (ho2 : oc + 20 ≤ 0x1690) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x1690) (hd3 : dc % 4 = 0)
    (hs : oc + 20 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧
      (∀ q, tlvClob q = false → q ≠ ra → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 17), (dc + 8, 8)] ∧
      (∀ t, derTlv (memBytes M rp rl.toNat) = .ok t → DerTlvW n'.mem B oc dc rp rl t) ∧
      (∀ e, derTlv (memBytes M rp rl.toNat) = .error e → DerErrW n'.mem B oc e) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  obtain ⟨n2, c2, pc2, mem2, k2⟩ := derTlv_correct n1 (out := B + 0x21A0 + BitVec.ofNat 32 oc)
    (d := B + 0x21A0 + BitVec.ofNat 32 dc) (by decide) (by rw [mem1]; exact C.tlv) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev) (sv_al F (by omega) ho3) (sv_al F (by omega) hd3)
    (by rw [← sv_base']; exact F.sepHi (by omega) (by decide) (by decide))
    (by rw [d8, ← sv_base']; exact F.sepHi (by omega) (by decide) (by decide))
  rw [mem1, d8, d12, hrp, hrl] at mem2
  obtain ⟨K, Ok, Er, fr⟩ := dtm_facts (rp := rp) (rl := rl) (M := M) (derTlv (memBytes M rp rl.toNat)) ho2 ho3 hd2 hd3 hs
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun q hk hr => by rw [k2 q hk, r1 q hr],
    by rw [mem2]; exact K, fun t ht => by rw [mem2]; exact Ok t ht, fun e he => by rw [mem2]; exact Er e he,
    fun x hx => by rw [mem2]; exact fr x hx⟩

/-- `lists_oid` reads only the `n` bytes at `p`. -/
theorem listsOidLoop_congr {M M0 : Word → BitVec 8} {oid : Bytes} :
    ∀ (k : Nat) (p : Word) (n : Nat), (∀ i, i < n → M (p + BitVec.ofNat 32 i) = M0 (p + BitVec.ofNat 32 i)) →
      listsOidLoop M oid k p n = listsOidLoop M0 oid k p n
  | 0, _, _, _ => rfl
  | k + 1, p, n, h => by
    unfold listsOidLoop
    by_cases hn : n = 0
    · rw [ite_eq_left hn, ite_eq_left hn]
    · rw [ite_eq_right hn, ite_eq_right hn, memBytes_congr h]
      cases ht : derElement 0x30 (memBytes M0 p n) with
      | error e => rfl
      | ok t =>
        have hb := derElement_bound ht; rw [memBytes_length] at hb
        simp only
        rw [mb_sub h (c := t.header) (l := t.len) (by omega)]
        cases ho : derOid (memBytes M0 (p + BitVec.ofNat 32 t.header) t.len) with
        | error e => rfl
        | ok o =>
          have hob := derElement_bound (derOid_ok_elem ho); rw [memBytes_length] at hob
          simp only
          rw [add_ofNat_assoc, mb_sub h (c := t.header + o.header) (l := o.len) (by omega)]
          by_cases he : memBytes M0 (p + BitVec.ofNat 32 (t.header + o.header)) o.len = oid
          · rw [ite_eq_left he, ite_eq_left he]
          · rw [ite_eq_right he, ite_eq_right he]
            exact listsOidLoop_congr k _ _ fun i hi => by
              rw [add_ofNat_assoc]; exact h _ (by omega)

theorem sv_sp80 (B : Word) : B + 0x21A0 + 0xFFFFFF80 = B + BitVec.ofNat 32 0x2120 := by
  rw [BitVec.add_assoc]; rfl

set_option maxHeartbeats 8000000 in
/-- **A call to `der::lists_oid`**: whether the `n` bytes of extensions at
`p` list the `ql`-byte OID at `q`. -/
theorem sv_loF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o p q : Word} {nl ql : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 listsOidAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = p) (ha1 : reg n a1 = BitVec.ofNat 32 nl)
    (ha2 : reg n a2 = q) (ha3 : reg n a3 = BitVec.ofNat 32 ql) (hp : SvIn B p nl) (hq : SvIn B q ql) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ r : Fin 32, r.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' r = reg n r) ∧
      (match listsOidOf M p nl (memBytes M q ql) with
        | .error b => reg n' a0 = 1 ∧ reg n' a1 = b.zeroExtend 32
        | .ok v => reg n' a0 = 0 ∧ reg n' a1 = if v then 1 else 0) ∧
      SvKeepL B M n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have env : LOEnv M (BitVec.ofNat 32 listsOidAddress) (B + 0x21A0) p q nl ql := by
    refine ⟨by decide, C.listsOid, C.seq, C.nest, C.elem, C.tlv, C.derOid, C.sliceEq, C.equalSameLength,
      C.memcmp, C.K.stub, C.K.body, ?_, ?_, hp.pos, hp.fit, by have := hq.fit; omega, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hS]; omega
    · rw [hS]; omega
    iterate 11 (· rw [sv_sp80]; exact F.sepHi (by decide) (by decide) (by decide))
    · rw [sv_sp80]; exact hp.sepLo (by decide)
    · rw [sv_sp80]; exact hq.sepLo (by decide)
  obtain ⟨n2, c2, pc2, sp2, k2, f2, R⟩ := listsOid_correct n1 (by rw [mem1]; exact env)
    pc1 (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [r1 a2 (by decide), ha2]) (by rw [r1 a3 (by decide), ha3]) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev)
  rw [mem1, sv_sp80] at f2
  rw [mem1] at R
  have hfS : ∀ x, SvR B x → Sep (B + BitVec.ofNat 32 0x2120) 0x80 x 1 := fun x hx => by
    have := svR_lo (k := 0x80) hx (by decide) (by decide)
    rwa [sv_lo B 0x80 (by decide)] at this
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun r hr => by rw [k2 r (by revert hr; revert r; decide), r1 r (by revert hr; revert r; decide)], R,
    fun e he _ => ?_, fun x hx => f2 x (hfS x hx)⟩
  exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))

end C3.RV32.Sv
