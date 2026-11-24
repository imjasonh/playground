import C3BootProofs.Proofs.SvIvLib
import C3BootProofs.Proofs.SvMs0
import C3BootProofs.Proofs.SvEcW3
import C3BootProofs.Proofs.SvEcMl3

/-!
# `sigstore::verify`: wrappers for the inversion of `Z`

The calls that the inlined P-256 check's inversion of the sum's `Z` makes
and the earlier stages don't: `update_de` and `SignedInt::norm` with the
modulus in the frame.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

set_option maxHeartbeats 16000000 in
/-- **A call to `update_de::<8>`** with the modulus in the frame: `d` at
offset `ca` and `e` at `cb` times the rows of the matrix at `ct`, reduced
modulo the limbs at offset `cm` with `-m⁻¹ mod 2^64` in `a5:a4`, into `co`
and `co + 0x24`. -/
theorem sv_ude8Fs {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o mlo mhi : Word}
    {co ca cb ct cm s : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (UC : SvUpCode M) (st : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 updateDe8Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 ca)
    (ha2 : reg n a2 = B + 0x21A0 + BitVec.ofNat 32 cb) (ha3 : reg n a3 = B + 0x21A0 + BitVec.ofNat 32 cm) (ha4 : reg n a4 = mlo)
    (ha5 : reg n a5 = mhi) (ha6 : reg n a6 = B + 0x21A0 + BitVec.ofNat 32 ct)
    (ha7 : reg n (17 : Fin 32) = BitVec.ofNat 32 s) (hs1 : 1 ≤ s) (hs2 : s ≤ 63)
    (hco : co + 0x45 ≤ 0x1690) (hca : ca + 33 ≤ 0x1690) (hcb : cb + 33 ≤ 0x1690) (hct : ct + 32 ≤ 0x1690)
    (aco : co % 4 = 0) (aca : ca % 4 = 0) (acb : cb % 4 = 0) (act : ct % 4 = 0)
    (sa : ca + 33 ≤ co ∨ co + 0x45 ≤ ca) (sb : cb + 33 ≤ co ∨ co + 0x45 ≤ cb) (stt : ct + 32 ≤ co ∨ co + 0x45 ≤ ct)
    (hcm : cm + 32 ≤ 0x1690) (acm : cm % 4 = 0) (sm : cm + 32 ≤ co ∨ co + 0x45 ≤ cm)
    (hσa : (M (B + 0x21A0 + BitVec.ofNat 32 (ca + 0x20))).toNat ≤ 1)
    (hσb : (M (B + 0x21A0 + BitVec.ofNat 32 (cb + 0x20))).toNat ≤ 1) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      (∃ σ A, σ ≤ 1 ∧ sgnVal σ A = svI M B ca * svM M B ct + svI M B cb * svM M B (ct + 8) ∧
        (n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x20))).toNat =
          (lrsm8 σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV M (B + 0x21A0 + BitVec.ofNat 32 cm) 8)).1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 = (lrsm8 σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV M (B + 0x21A0 + BitVec.ofNat 32 cm) 8)).2) ∧
      (∃ σ A, σ ≤ 1 ∧ sgnVal σ A = svI M B ca * svM M B (ct + 0x10) + svI M B cb * svM M B (ct + 0x18) ∧
        (n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x24 + 0x20))).toNat =
          (lrsm8 σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV M (B + 0x21A0 + BitVec.ofNat 32 cm) 8)).1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x24)) 8 =
          (lrsm8 σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV M (B + 0x21A0 + BitVec.ofNat 32 cm) 8)).2) ∧
      SvKeepL B M n'.mem [(co, 0x45)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hG : (B + BitVec.ofNat 32 0x1ED0).toNat = B.toNat + 0x1ED0 := F.at 0x1ED0 (by decide)
  have gH : ∀ {b : Word} {len : Nat}, 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 →
      Sep (B + BitVec.ofNat 32 0x1ED0) 0x2D0 b len := fun h1 h2 => F.sepHi (by decide) h1 h2
  have gD : ∀ {b : Word} {len : Nat}, (img% dataWindowAddress) ≤ b.toNat → b.toNat + len ≤ (img% dataWindowAddress + dataWindowSize) →
      Sep (B + BitVec.ofNat 32 0x1ED0) 0x2D0 b len := fun h1 h2 => F.bufData (by decide) h1 h2
  have gF : ∀ {c l : Nat}, c + l ≤ 0x1690 → Sep (B + 0x21A0 + BitVec.ofNat 32 c) l (B + BitVec.ofNat 32 0x1ED0) 0x2D0 :=
    fun h => by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega)
  have oH : ∀ {b : Word} {len : Nat}, 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 →
      Sep (B + 0x21A0 + BitVec.ofNat 32 co) 0x45 b len := fun h1 h2 => FS.sepHi hco h1 h2
  have oD : ∀ {b : Word} {len : Nat}, (img% dataWindowAddress) ≤ b.toNat → b.toNat + len ≤ (img% dataWindowAddress + dataWindowSize) →
      Sep (B + 0x21A0 + BitVec.ofNat 32 co) 0x45 b len := fun h1 h2 => FS.bufData hco h1 h2
  have EN : UD8Env n1.mem (BitVec.ofNat 32 updateDe8Address) (B + BitVec.ofNat 32 0x1ED0)
      (B + 0x21A0 + BitVec.ofNat 32 co) (B + 0x21A0 + BitVec.ofNat 32 ca) (B + 0x21A0 + BitVec.ofNat 32 cb)
      (B + 0x21A0 + BitVec.ofNat 32 cm)
      (B + 0x21A0 + BitVec.ofNat 32 ct) := by
    rw [mem1]
    have elc : lm8Lc (ud8L (BitVec.ofNat 32 updateDe8Address)) = BitVec.ofNat 32 lincomb8Address := by decide
    have esh : lm8Shr (ud8L (BitVec.ofNat 32 updateDe8Address)) = BitVec.ofNat 32 shr8Address := by decide
    have elm : ud8L (BitVec.ofNat 32 updateDe8Address) = BitVec.ofNat 32 lincombShiftMod8Address := by decide
    refine ⟨by decide, by rw [elm]; exact UC.lmc, by rw [elc]; exact UC.lc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      UC.zero, UC.one, by rw [esh]; exact UC.shr, ?_, ?_, ?_, UC.max,
      UC.de, UC.de_fi,
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      gD (by decide) (by decide), gD (by decide) (by decide),
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      gD (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      oH (by decide) (by decide), oH (by decide) (by decide), oH (by decide) (by decide), oH (by decide) (by decide),
      oH (by decide) (by decide), oH (by decide) (by decide), oH (by decide) (by decide), oH (by decide) (by decide),
      oH (by decide) (by decide), oH (by decide) (by decide), oH (by decide) (by decide),
      oD (by decide) (by decide), oD (by decide) (by decide),
      oH (by decide) (by decide), oH (by decide) (by decide), oH (by decide) (by decide), oH (by decide) (by decide),
      oD (by decide) (by decide), oH (by decide) (by decide), oH (by decide) (by decide),
      by rw [hG]; omega, by rw [hG]; omega,
      sv_al F (by omega) aco, sv_al F (by omega) aca, sv_al F (by omega) acb, sv_al F (by omega) acm, sv_al F (by omega) act,
      by rw [sv_at F _ (by omega)]; omega, by rw [sv_at F _ (by omega)]; omega, by rw [sv_at F _ (by omega)]; omega,
      gF hco, gF hca, gF hcb, gF hcm, gF hct,
      sepS (B + 0x21A0) sa (by omega) (by omega), sepS (B + 0x21A0) sb (by omega) (by omega),
      sepS (B + 0x21A0) sm (by omega) (by omega), sepS (B + 0x21A0) stt (by omega) (by omega)⟩
    · rw [elc, show BitVec.ofNat 32 lincomb8Address + 0xFFFFC6EA = BitVec.ofNat 32 absSign2Address by decide]; exact UC.abs
    · rw [elc, show BitVec.ofNat 32 lincomb8Address + 0x398 = BitVec.ofNat 32 wideMul8x2Address by decide]; exact UC.wide
    · rw [elc, show BitVec.ofNat 32 lincomb8Address + 0x480 = BitVec.ofNat 32 condNeg8Address by decide]; exact UC.neg
    · rw [elc, show BitVec.ofNat 32 lincomb8Address + 0x3A44 = MSET by decide]; exact C.K.mset
    · rw [elc, show BitVec.ofNat 32 lincomb8Address + 0x3AAC = MCS by decide]; exact C.K.stub
    · rw [elc, show BitVec.ofNat 32 lincomb8Address + 0x3AB4 = MCS + 8 by decide]; exact C.K.body
    · rw [elc, show lcBsub8 (BitVec.ofNat 32 lincomb8Address) = BSUB by decide]; exact C.K.bsub
    · rw [elc, show BitVec.ofNat 32 lincomb8Address + 0x272E = BitVec.ofNat 32 uintSelect2Address by decide]; exact UC.sel2
    · rw [elc, show BitVec.ofNat 32 lincomb8Address + 0xFFFFFF2A = BitVec.ofNat 32 uintSelect8Address by decide]
      exact UC.sel8
    · rw [esh, show BitVec.ofNat 32 shr8Address + 0x1EE = BitVec.ofNat 32 leadMut8Address by decide]; exact UC.lm
    · rw [esh, show BitVec.ofNat 32 shr8Address + 0x1FE = BitVec.ofNat 32 trailing8Address by decide]; exact UC.tr
    · rw [elm, show BitVec.ofNat 32 lincombShiftMod8Address + 0xFFFFBFB6 = BitVec.ofNat 32 toUintResize2Address by decide]
      exact UC.tur
  obtain ⟨n2, c2, pc2, sp2, k2, ⟨σ1, A1, hσ1, e1, b1, v1⟩, ⟨σ2, A2, hσ2, e2, b2, v2⟩, fr2⟩ :=
    updateDe8_correct n1 (s := s) (mlo := mlo) (mhi := mhi) EN pc1 (by rw [r1 sp (by decide), rsp, BitVec.add_assoc]; rfl)
      (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
      (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3)
      (by rw [r1 a4 (by decide)]; exact ha4) (by rw [r1 a5 (by decide)]; exact ha5)
      (by rw [r1 a6 (by decide)]; exact ha6) (by rw [r1 17 (by decide)]; exact ha7)
      (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) hs1 hs2
      (by rw [mem1, add_lit20]; exact hσa) (by rw [mem1, add_lit20]; exact hσb)
  rw [mem1] at e1 e2 fr2 b1 b2 v1 v2
  rw [add_lit20, add_lit20, add_lit8] at e1
  rw [add_lit20, add_lit20, add_lit10, add_lit18] at e2
  rw [add_lit20] at b1
  rw [add_lit24, add_lit20] at b2
  rw [add_lit24] at v2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, BitVec.add_assoc]; rfl,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)],
    ⟨σ1, A1, hσ1, e1, b1, v1⟩, ⟨σ2, A2, hσ2, e2, b2, v2⟩, fun e he hL => ?_,
    fun x hx => fr2 x (svR_spX hx (by decide) (by decide) (by decide)) (svR_hi hx hco)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  exact fr2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

set_option maxHeartbeats 8000000 in
/-- **A call to `SignedInt<8>::norm`** of the value at offset `cx` with `f`'s
sign `fs` in `a2` and the modulus at frame offset `cm`, into offset `co`. -/
theorem sv_nrm8Fs {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o fs : Word} {co cx cm : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (UC : SvUpCode M) (EC : SvEcCode M)
    (hn8 : CodeIn M (BitVec.ofNat 32 norm8Address) norm8Code) (st : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 norm8Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cx)
    (ha2 : reg n a2 = fs) (hfs : fs = 0 ∨ fs = 1) (ha3 : reg n a3 = B + 0x21A0 + BitVec.ofNat 32 cm)
    (hco : co + 32 ≤ 0x1690) (hcx : cx + 33 ≤ 0x1690) (aco : co % 4 = 0) (acx : cx % 4 = 0)
    (hcm : cm + 32 ≤ 0x1690) (acm : cm % 4 = 0)
    (hσ : (M (B + 0x21A0 + BitVec.ofNat 32 (cx + 0x20))).toNat ≤ 1) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 =
        normVal8 (M (B + 0x21A0 + BitVec.ofNat 32 (cx + 0x20))).toNat fs.toNat
          (accV M (B + 0x21A0 + BitVec.ofNat 32 cx) 8) (accV M (B + 0x21A0 + BitVec.ofNat 32 cm) 8) ∧
      SvKeepL B M n'.mem [(co, 32)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have EN : Nm8Env n1.mem (BitVec.ofNat 32 norm8Address) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 co)
      (B + 0x21A0 + BitVec.ofNat 32 cx) (B + 0x21A0 + BitVec.ofNat 32 cm) := by
    rw [mem1]
    refine ⟨by decide, hn8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hS]; omega, by rw [hS]; omega,
      sv_al F (by omega) aco, sv_al F (by omega) acx, sv_al F (by omega) acm, by rw [sv_at F _ (by omega)]; omega,
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide),
      FS.lowN (k := 0x90) (by decide) (by decide) hco, FS.lowN (k := 0x90) (by decide) (by decide) hcx,
      by rw [show n8R (B + 0x21A0) = B + BitVec.ofNat 32 0x2110 from sv_spX B 0x90 (by decide)]
         rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega)⟩
    · rw [show BitVec.ofNat 32 norm8Address + 0xFFFFFEA4 = BitVec.ofNat 32 uint8IsNonzeroAddress by decide]; exact EC.unz8
    · rw [show BitVec.ofNat 32 norm8Address + 0xFFFF10B2 = BitVec.ofNat 32 uintRefIsNonzeroAddress by decide]
      exact C.K.refnz
    · rw [show BitVec.ofNat 32 norm8Address + 0x2C2C = MSET by decide]; exact C.K.mset
    · rw [show n8Bsub (BitVec.ofNat 32 norm8Address) = BSUB by decide]; exact C.K.bsub
    · rw [show BitVec.ofNat 32 norm8Address + 0xFFFFF112 = BitVec.ofNat 32 uintSelect8Address by decide]; exact UC.sel8
    · rw [show BitVec.ofNat 32 norm8Address + 0x2C94 = MCS by decide]; exact C.K.stub
    · rw [show BitVec.ofNat 32 norm8Address + 0x2C9C = MCS + 8 by decide]; exact C.K.body
  obtain ⟨n2, c2, pc2, sp2, k2, A2, f2⟩ := norm8_correct n1 EN pc1 (by rw [r1 sp (by decide), rsp])
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2]; exact hfs)
    (by rw [r1 a3 (by decide), ha3]) (by rw [mem1, add_lit20]; exact hσ)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [mem1, add_lit20, r1 a2 (by decide), ha2] at A2
  have e1 : n8R (B + 0x21A0) = B + BitVec.ofNat 32 0x2110 := sv_spX B 0x90 (by decide)
  rw [mem1, e1] at f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], A2,
    fun e he hL => ?_, fun x hx => f2 x (svR_spX hx (by decide) (by decide) (by decide)) (svR_hi hx hco)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

end C3.RV32.Sv
