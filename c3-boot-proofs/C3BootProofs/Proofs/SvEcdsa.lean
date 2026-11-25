import C3BootProofs.Proofs.SvKu
import C3BootProofs.Proofs.EcdsaSig

/-!
# `sigstore::verify`: the leaf's signature

`der::ecdsa_signature::<48>` on the leaf's `signatureValue` bits, from the
frame of `sigstore::verify`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- `ecdsaSigOf` reads only the `n` bytes at `p`. -/
theorem ecdsaSigOf_congr {N : Nat} {M M0 : Word → BitVec 8} {p : Word} {n : Nat}
    (h : ∀ i, i < n → M (p + BitVec.ofNat 32 i) = M0 (p + BitVec.ofNat 32 i)) :
    ecdsaSigOf N M p n = ecdsaSigOf N M0 p n := by
  unfold ecdsaSigOf
  rw [memBytes_congr h]
  cases ht : derElement 0x30 (memBytes M0 p n) with
  | error e => rfl
  | ok t =>
    have hb := derElement_bound ht; rw [memBytes_length] at hb
    simp only
    have e1 : memBytes M (p + BitVec.ofNat 32 t.header) t.len = memBytes M0 (p + BitVec.ofNat 32 t.header) t.len :=
      mb_sub h (by omega)
    rw [e1]
    have hu : derUsed (derElement 2 (memBytes M0 (p + BitVec.ofNat 32 t.header) t.len)) ≤ t.len := by
      cases h2 : derElement 2 (memBytes M0 (p + BitVec.ofNat 32 t.header) t.len) with
      | error _ => exact Nat.zero_le _
      | ok t2 =>
        have := derElement_bound h2; rw [memBytes_length] at this
        show t2.header + t2.len ≤ t.len; exact this
    have e2 : memBytes M (p + BitVec.ofNat 32 (t.header +
          derUsed (derElement 2 (memBytes M0 (p + BitVec.ofNat 32 t.header) t.len))))
          (t.len - derUsed (derElement 2 (memBytes M0 (p + BitVec.ofNat 32 t.header) t.len))) =
        memBytes M0 (p + BitVec.ofNat 32 (t.header +
          derUsed (derElement 2 (memBytes M0 (p + BitVec.ofNat 32 t.header) t.len))))
          (t.len - derUsed (derElement 2 (memBytes M0 (p + BitVec.ofNat 32 t.header) t.len))) :=
      mb_sub h (by omega)
    rw [e2]

theorem sv_sp170 (B : Word) : B + 0x21A0 + 0xFFFFFE90 = B + BitVec.ofNat 32 0x2030 := by
  rw [BitVec.add_assoc]; rfl

set_option maxHeartbeats 8000000 in
/-- **A call to `der::ecdsa_signature::<48>`** on the `n` bytes at `p`, with
the result at offset `oc`. -/
theorem sv_esF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o p : Word} {oc nl : Nat}
    (F : Fr B 0x2660) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 ecdsaSignature48Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc) (ha1 : reg n a1 = p)
    (ha2 : reg n a2 = BitVec.ofNat 32 nl) (ho2 : oc + 97 ≤ 0x4C0) (hin : SvIn B p nl) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 97)] ∧
      (match ecdsaSigOf 48 M p nl with
        | .ok (r, s) => n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) = 0 ∧
            (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (oc + 1 + j)) = BitVec.ofNat 8 (r.getD j 0)) ∧
            ∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (oc + 49 + j)) = BitVec.ofNat 8 (s.getD j 0)
        | .error b => n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) = 1 ∧
            n'.mem (B + 0x21A0 + BitVec.ofNat 32 (oc + 1)) = b) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have env : ESEnv M (BitVec.ofNat 32 ecdsaSignature48Address) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 oc) p nl := by
    refine ⟨by decide, C.ecdsaSignature48, C.seq, C.nest, C.elem, C.tlv, C.derPositiveInteger, C.derInteger,
      C.zipSkipNext, C.derScalar48, C.K.mset, C.K.stub, C.K.body, ?_, ?_, ?_, hin.pos, hin.fit,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hS]; omega
    · rw [hS]; omega
    · rw [sv_at F _ (by omega)]; omega
    iterate 12 (· rw [sv_sp170]; exact F.sepHi (by decide) (by decide) (by decide))
    iterate 3 (· rw [← sv_base']; exact F.sepHi (by omega) (by decide) (by decide))
    · rw [sv_sp170, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp170]; exact hin.sepLo (by decide)
  obtain ⟨n2, c2, pc2, sp2, k2, f2, R⟩ := ecdsaSignature48_correct n1 (by rw [mem1]; exact env)
    pc1 (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [r1 a2 (by decide), ha2]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [mem1, sv_sp170] at f2
  rw [mem1] at R
  have hfS : ∀ x, SvR B x → Sep (B + BitVec.ofNat 32 0x2030) 0x170 x 1 := fun x hx => by
    have := svR_lo (k := 0x170) hx (by decide) (by decide)
    rwa [sv_lo B 0x170 (by decide)] at this
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)],
    fun e he hL => ?_, ?_, fun x hx => f2 x (hfS x hx) (svR_hi hx ho2)⟩
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))
  · revert R
    cases ecdsaSigOf 48 M p nl with
    | error b =>
      intro R
      exact ⟨R.1, by rw [← lb1 (B + 0x21A0) oc (by omega)]; exact R.2⟩
    | ok rs =>
      obtain ⟨r, s'⟩ := rs
      intro R
      refine ⟨R.1, fun j hj => ?_, fun j hj => ?_⟩
      · rw [show oc + 1 + j = oc + (1 + j) by omega, ← add_ofNat_assoc]; exact R.2.1 j hj
      · rw [show oc + 49 + j = oc + (49 + j) by omega, ← add_ofNat_assoc]; exact R.2.2 j hj

end C3.RV32.Sv
