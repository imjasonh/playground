import C3BootProofs.Proofs.SvEcDs
import C3BootProofs.Proofs.UpdateFg8
import C3BootProofs.Proofs.UpdateDe8
import C3BootProofs.Proofs.Norm8
import C3BootProofs.Proofs.UintEq

/-!
# `sigstore::verify`: the P-256 inversion's matrix updates

Wrappers for `update_fg::<8>` and `update_de::<8>`, which apply a batch's
matrix to `f` and `g` and to `d` and `e`, called from `sigstore::verify`'s
frame.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

/-- `update_fg::<8>` and `update_de::<8>` and their callees, at the offsets
their environments name. -/
structure SvUpCode (M : Word → BitVec 8) : Prop where
  fg : CodeIn M (BitVec.ofNat 32 updateFg8Address) updateFg8Code
  fg_fi : CodeIn M (BitVec.ofNat 32 updateFg8Address + 0x205C) fromI64Code
  ls : CodeIn M (BitVec.ofNat 32 updateFg8Address + 0xFFFFF076) lincombShift8Code
  lc : CodeIn M (BitVec.ofNat 32 lincomb8Address) lincomb8Code
  abs : CodeIn M (BitVec.ofNat 32 absSign2Address) absSign2Code
  wide : CodeIn M (BitVec.ofNat 32 wideMul8x2Address) wideMul8x2Code
  neg : CodeIn M (BitVec.ofNat 32 condNeg8Address) condNeg8Code
  sel2 : CodeIn M (BitVec.ofNat 32 uintSelect2Address) uintSelect2Code
  sel8 : CodeIn M (BitVec.ofNat 32 uintSelect8Address) uintSelect8Code
  shr : CodeIn M (BitVec.ofNat 32 shr8Address) shr8Code
  lm : CodeIn M (BitVec.ofNat 32 leadMut8Address) leadMut8Code
  tr : CodeIn M (BitVec.ofNat 32 trailing8Address) trailing8Code
  de : CodeIn M (BitVec.ofNat 32 updateDe8Address) updateDe8Code
  de_fi : CodeIn M (BitVec.ofNat 32 updateDe8Address + 0x1FD2) fromI64Code
  lmc : CodeIn M (BitVec.ofNat 32 lincombShiftMod8Address) lincombShiftMod8Code
  tur : CodeIn M (BitVec.ofNat 32 toUintResize2Address) toUintResize2Code
  zero : CodeIn M (BitVec.ofNat 32 u2ZeroAddress) u2ZeroData
  one : CodeIn M (BitVec.ofNat 32 u2OneAddress) u2OneData
  max : CodeIn M (BitVec.ofNat 32 u2MaxAddress) u2MaxData

theorem SvUpCode.sv {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3830) (D : SvUpCode M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : SvUpCode M := by
  have hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))
  exact ⟨codeHi D.fg (by decide) (by decide) hx, codeHi D.fg_fi (by decide) (by decide) hx,
    codeHi D.ls (by decide) (by decide) hx, codeHi D.lc (by decide) (by decide) hx,
    codeHi D.abs (by decide) (by decide) hx, codeHi D.wide (by decide) (by decide) hx,
    codeHi D.neg (by decide) (by decide) hx, codeHi D.sel2 (by decide) (by decide) hx,
    codeHi D.sel8 (by decide) (by decide) hx, codeHi D.shr (by decide) (by decide) hx,
    codeHi D.lm (by decide) (by decide) hx, codeHi D.tr (by decide) (by decide) hx,
    codeHi D.de (by decide) (by decide) hx, codeHi D.de_fi (by decide) (by decide) hx,
    codeHi D.lmc (by decide) (by decide) hx, codeHi D.tur (by decide) (by decide) hx,
    F.dataIn fR D.zero (by decide) (by decide), F.dataIn fR D.one (by decide) (by decide),
    F.dataIn fR D.max (by decide) (by decide)⟩

theorem add_lit20 (S : Word) (c : Nat) : S + BitVec.ofNat 32 c + 0x20 = S + BitVec.ofNat 32 (c + 0x20) :=
  add_ofNat_assoc S c 0x20
theorem add_lit24 (S : Word) (c : Nat) : S + BitVec.ofNat 32 c + 0x24 = S + BitVec.ofNat 32 (c + 0x24) :=
  add_ofNat_assoc S c 0x24
theorem add_lit18 (S : Word) (c : Nat) : S + BitVec.ofNat 32 c + 0x18 = S + BitVec.ofNat 32 (c + 0x18) :=
  add_ofNat_assoc S c 0x18

/-- `f` or `g` as an integer: 8 limbs at offset `c` with their sign byte at
`c + 0x20`. -/
abbrev svI (M : Word → BitVec 8) (B : Word) (c : Nat) : Int :=
  sgnVal (M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x20))).toNat (accV M (B + 0x21A0 + BitVec.ofNat 32 c) 8)

/-- A 64-bit matrix entry at offset `c`, as a signed integer. -/
abbrev svM (M : Word → BitVec 8) (B : Word) (c : Nat) : Int := i64Val (accV M (B + 0x21A0 + BitVec.ofNat 32 c) 2)

set_option maxHeartbeats 16000000 in
/-- **A call to `update_fg::<8>`**: `f` at offset `ca` and `g` at `cb` times
the rows of the matrix at `ct`, shifted right by `s`, into `co` and
`co + 0x24`. -/
theorem sv_ufg8F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {co ca cb ct s : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (UC : SvUpCode M) (st : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 updateFg8Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 ca)
    (ha2 : reg n a2 = B + 0x21A0 + BitVec.ofNat 32 cb) (ha3 : reg n a3 = B + 0x21A0 + BitVec.ofNat 32 ct)
    (ha4 : reg n a4 = BitVec.ofNat 32 s) (hs1 : 1 ≤ s) (hs2 : s ≤ 63)
    (hco : co + 0x45 ≤ 0x1690) (hca : ca + 33 ≤ 0x1690) (hcb : cb + 33 ≤ 0x1690) (hct : ct + 32 ≤ 0x1690)
    (aco : co % 4 = 0) (aca : ca % 4 = 0) (acb : cb % 4 = 0) (act : ct % 4 = 0)
    (sa : ca + 33 ≤ co ∨ co + 0x45 ≤ ca) (sb : cb + 33 ≤ co ∨ co + 0x45 ≤ cb) (stt : ct + 32 ≤ co ∨ co + 0x45 ≤ ct)
    (hσa : (M (B + 0x21A0 + BitVec.ofNat 32 (ca + 0x20))).toNat ≤ 1)
    (hσb : (M (B + 0x21A0 + BitVec.ofNat 32 (cb + 0x20))).toNat ≤ 1) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      (∃ σ A, σ ≤ 1 ∧ sgnVal σ A = svI M B ca * svM M B ct + svI M B cb * svM M B (ct + 8) ∧
        (n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x20))).toNat = σ ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 = A / 2 ^ s % 2 ^ 256) ∧
      (∃ σ A, σ ≤ 1 ∧ sgnVal σ A = svI M B ca * svM M B (ct + 0x10) + svI M B cb * svM M B (ct + 0x18) ∧
        (n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x24 + 0x20))).toNat = σ ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x24)) 8 = A / 2 ^ s % 2 ^ 256) ∧
      SvKeepL B M n'.mem [(co, 0x45)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hG : (B + BitVec.ofNat 32 0x1F70).toNat = B.toNat + 0x1F70 := F.at 0x1F70 (by decide)
  have gH : ∀ {b : Word} {len : Nat}, 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 →
      Sep (B + BitVec.ofNat 32 0x1F70) 0x230 b len := fun h1 h2 => F.sepHi (by decide) h1 h2
  have gD : ∀ {b : Word} {len : Nat}, 0x3FCC4200 ≤ b.toNat → b.toNat + len ≤ 0x3FCC4E60 →
      Sep (B + BitVec.ofNat 32 0x1F70) 0x230 b len := fun h1 h2 => F.bufData (by decide) h1 h2
  have gF : ∀ {c l : Nat}, c + l ≤ 0x1690 → Sep (B + 0x21A0 + BitVec.ofNat 32 c) l (B + BitVec.ofNat 32 0x1F70) 0x230 :=
    fun h => by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega)
  have EN : UFEnv8 n1.mem (BitVec.ofNat 32 updateFg8Address) (B + BitVec.ofNat 32 0x1F70)
      (B + 0x21A0 + BitVec.ofNat 32 co) (B + 0x21A0 + BitVec.ofNat 32 ca) (B + 0x21A0 + BitVec.ofNat 32 cb)
      (B + 0x21A0 + BitVec.ofNat 32 ct) := by
    rw [mem1]
    refine ⟨by decide, UC.fg, UC.fg_fi, UC.ls, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, UC.zero, UC.one, ?_, ?_, ?_,
      by rw [hG]; omega, by rw [hG]; omega,
      sv_al F (by omega) aco, sv_al F (by omega) aca, sv_al F (by omega) acb, sv_al F (by omega) act,
      by rw [sv_at F _ (by omega)]; omega, by rw [sv_at F _ (by omega)]; omega, by rw [sv_at F _ (by omega)]; omega,
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      gH (by decide) (by decide), gD (by decide) (by decide), gD (by decide) (by decide),
      gH (by decide) (by decide), gH (by decide) (by decide), gH (by decide) (by decide),
      FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide),
      FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide),
      FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide),
      FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide),
      FS.sepHi hco (by decide) (by decide),
      FS.bufData hco (by decide) (by decide), FS.bufData hco (by decide) (by decide),
      FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide),
      gF hco, gF hca, gF hcb, gF hct,
      sepS (B + 0x21A0) sa (by omega) (by omega), sepS (B + 0x21A0) sb (by omega) (by omega),
      sepS (B + 0x21A0) stt (by omega) (by omega)⟩
    · rw [show BitVec.ofNat 32 updateFg8Address + 0xFFFFF076 + 0x62 = BitVec.ofNat 32 lincomb8Address by decide]
      exact UC.lc
    · rw [show BitVec.ofNat 32 updateFg8Address + 0xFFFFF076 + 0x62 + 0xFFFFC6EA = BitVec.ofNat 32 absSign2Address by
        decide]; exact UC.abs
    · rw [show BitVec.ofNat 32 updateFg8Address + 0xFFFFF076 + 0x62 + 0x398 = BitVec.ofNat 32 wideMul8x2Address by
        decide]; exact UC.wide
    · rw [show BitVec.ofNat 32 updateFg8Address + 0xFFFFF076 + 0x62 + 0x480 = BitVec.ofNat 32 condNeg8Address by
        decide]; exact UC.neg
    · rw [show BitVec.ofNat 32 updateFg8Address + 0xFFFFF076 + 0x62 + 0x3A44 = MSET by decide]; exact C.K.mset
    · rw [show BitVec.ofNat 32 updateFg8Address + 0xFFFFF076 + 0x62 + 0x3AAC = MCS by decide]; exact C.K.stub
    · rw [show BitVec.ofNat 32 updateFg8Address + 0xFFFFF076 + 0x62 + 0x3AB4 = MCS + 8 by decide]; exact C.K.body
    · rw [show lcBsub8 (BitVec.ofNat 32 updateFg8Address + 0xFFFFF076 + 0x62) = BSUB by decide]; exact C.K.bsub
    · rw [show BitVec.ofNat 32 updateFg8Address + 0xFFFFF076 + 0x62 + 0x272E = BitVec.ofNat 32 uintSelect2Address by
        decide]; exact UC.sel2
    · rw [show BitVec.ofNat 32 updateFg8Address + 0xFFFFF076 + 0x62 + 0xFFFFFF2A = BitVec.ofNat 32 uintSelect8Address by
        decide]; exact UC.sel8
    · rw [show BitVec.ofNat 32 updateFg8Address + 0xFFFFF076 + 0x1E6 = BitVec.ofNat 32 shr8Address by decide]
      exact UC.shr
    · rw [show BitVec.ofNat 32 updateFg8Address + 0xFFFFF076 + 0x1E6 + 0x1EE = BitVec.ofNat 32 leadMut8Address by
        decide]; exact UC.lm
    · rw [show BitVec.ofNat 32 updateFg8Address + 0xFFFFF076 + 0x1E6 + 0x1FE = BitVec.ofNat 32 trailing8Address by
        decide]; exact UC.tr
  obtain ⟨n2, c2, pc2, sp2, k2, ⟨σ1, A1, hσ1, e1, b1, v1⟩, ⟨σ2, A2, hσ2, e2, b2, v2⟩, fr2⟩ :=
    updateFg8_correct n1 (s := s) EN pc1
      (by rw [r1 sp (by decide), rsp, BitVec.add_assoc]; rfl)
      (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
      (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3)
      (by rw [r1 a4 (by decide)]; exact ha4) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) hs1 hs2
      (by rw [mem1, add_lit20]; exact hσa) (by rw [mem1, add_lit20]; exact hσb)
  rw [mem1] at e1 e2 fr2
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

set_option maxHeartbeats 16000000 in
/-- **A call to `update_de::<8>`**: `d` at offset `ca` and `e` at `cb` times
the rows of the matrix at `ct`, reduced modulo the constant at `mp` with
`-mp⁻¹ mod 2^64` in `a5:a4`, into `co` and `co + 0x24`. -/
theorem sv_ude8F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o mp mlo mhi : Word}
    {co ca cb ct s : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (UC : SvUpCode M) (st : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 updateDe8Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 ca)
    (ha2 : reg n a2 = B + 0x21A0 + BitVec.ofNat 32 cb) (ha3 : reg n a3 = mp) (ha4 : reg n a4 = mlo)
    (ha5 : reg n a5 = mhi) (ha6 : reg n a6 = B + 0x21A0 + BitVec.ofNat 32 ct)
    (ha7 : reg n (17 : Fin 32) = BitVec.ofNat 32 s) (hs1 : 1 ≤ s) (hs2 : s ≤ 63)
    (hco : co + 0x45 ≤ 0x1690) (hca : ca + 33 ≤ 0x1690) (hcb : cb + 33 ≤ 0x1690) (hct : ct + 32 ≤ 0x1690)
    (aco : co % 4 = 0) (aca : ca % 4 = 0) (acb : cb % 4 = 0) (act : ct % 4 = 0)
    (sa : ca + 33 ≤ co ∨ co + 0x45 ≤ ca) (sb : cb + 33 ≤ co ∨ co + 0x45 ≤ cb) (stt : ct + 32 ≤ co ∨ co + 0x45 ≤ ct)
    (hm1 : 0x3FCC4200 ≤ mp.toNat) (hm2 : mp.toNat + 32 ≤ 0x3FCC4E60) (hm4 : mp.toNat % 4 = 0)
    (hσa : (M (B + 0x21A0 + BitVec.ofNat 32 (ca + 0x20))).toNat ≤ 1)
    (hσb : (M (B + 0x21A0 + BitVec.ofNat 32 (cb + 0x20))).toNat ≤ 1) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      (∃ σ A, σ ≤ 1 ∧ sgnVal σ A = svI M B ca * svM M B ct + svI M B cb * svM M B (ct + 8) ∧
        (n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x20))).toNat =
          (lrsm8 σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV M mp 8)).1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 = (lrsm8 σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV M mp 8)).2) ∧
      (∃ σ A, σ ≤ 1 ∧ sgnVal σ A = svI M B ca * svM M B (ct + 0x10) + svI M B cb * svM M B (ct + 0x18) ∧
        (n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x24 + 0x20))).toNat =
          (lrsm8 σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV M mp 8)).1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x24)) 8 =
          (lrsm8 σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV M mp 8)).2) ∧
      SvKeepL B M n'.mem [(co, 0x45)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hG : (B + BitVec.ofNat 32 0x1ED0).toNat = B.toNat + 0x1ED0 := F.at 0x1ED0 (by decide)
  have gH : ∀ {b : Word} {len : Nat}, 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 →
      Sep (B + BitVec.ofNat 32 0x1ED0) 0x2D0 b len := fun h1 h2 => F.sepHi (by decide) h1 h2
  have gD : ∀ {b : Word} {len : Nat}, 0x3FCC4200 ≤ b.toNat → b.toNat + len ≤ 0x3FCC4E60 →
      Sep (B + BitVec.ofNat 32 0x1ED0) 0x2D0 b len := fun h1 h2 => F.bufData (by decide) h1 h2
  have gF : ∀ {c l : Nat}, c + l ≤ 0x1690 → Sep (B + 0x21A0 + BitVec.ofNat 32 c) l (B + BitVec.ofNat 32 0x1ED0) 0x2D0 :=
    fun h => by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega)
  have oH : ∀ {b : Word} {len : Nat}, 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 →
      Sep (B + 0x21A0 + BitVec.ofNat 32 co) 0x45 b len := fun h1 h2 => FS.sepHi hco h1 h2
  have oD : ∀ {b : Word} {len : Nat}, 0x3FCC4200 ≤ b.toNat → b.toNat + len ≤ 0x3FCC4E60 →
      Sep (B + 0x21A0 + BitVec.ofNat 32 co) 0x45 b len := fun h1 h2 => FS.bufData hco h1 h2
  have EN : UD8Env n1.mem (BitVec.ofNat 32 updateDe8Address) (B + BitVec.ofNat 32 0x1ED0)
      (B + 0x21A0 + BitVec.ofNat 32 co) (B + 0x21A0 + BitVec.ofNat 32 ca) (B + 0x21A0 + BitVec.ofNat 32 cb) mp
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
      sv_al F (by omega) aco, sv_al F (by omega) aca, sv_al F (by omega) acb, hm4, sv_al F (by omega) act,
      by rw [sv_at F _ (by omega)]; omega, by rw [sv_at F _ (by omega)]; omega, by rw [sv_at F _ (by omega)]; omega,
      gF hco, gF hca, gF hcb, (gD hm1 hm2).symm, gF hct,
      sepS (B + 0x21A0) sa (by omega) (by omega), sepS (B + 0x21A0) sb (by omega) (by omega),
      (oD hm1 hm2).symm, sepS (B + 0x21A0) stt (by omega) (by omega)⟩
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

theorem acc2_frame {M : Word → BitVec 8} {B a b : Word} {c : Nat}
    (h0 : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 c) = a) (h1 : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (c + 4)) = b) :
    accV M (B + 0x21A0 + BitVec.ofNat 32 c) 2 = a.toNat + 2 ^ 32 * b.toNat := by
  simp only [accV]
  rw [show 4 * 0 = 0 from rfl, add_ofNat_zero, h0, show 4 * 1 = 4 from rfl, add_ofNat_assoc, h1]
  omega

theorem byte_of_toNat {b : BitVec 8} {σ : Nat} (h : b.toNat = σ) : b = BitVec.ofNat 8 σ := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, ← h]; exact (Nat.mod_eq_of_lt b.isLt).symm

/-- Two runs of limbs are equal limb by limb exactly when their values are. -/
theorem limbsEq_iff {M M' : Word → BitVec 8} {p q : Word} :
    ∀ n, (∀ i, i < n → memLoad32 M (p + BitVec.ofNat 32 (4 * i)) = memLoad32 M' (q + BitVec.ofNat 32 (4 * i))) ↔
      accV M p n = accV M' q n
  | 0 => ⟨fun _ => rfl, fun _ i hi => absurd hi (Nat.not_lt_zero _)⟩
  | n + 1 => by
    simp only [accV]
    have l1 := accV_lt M p n; have l2 := accV_lt M' q n
    have hp : 0 < 2 ^ (32 * n) := Nat.pow_pos (by decide)
    constructor
    · intro h
      rw [(limbsEq_iff n).mp fun i hi => h i (by omega), h n (by omega)]
    · intro h i hi
      have e1 : accV M p n = accV M' q n := by
        have := congrArg (· % 2 ^ (32 * n)) h
        simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at this
        exact this
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact (limbsEq_iff n).mpr e1 i hi
      · apply BitVec.eq_of_toNat_eq
        have := congrArg (· / 2 ^ (32 * i)) h
        rw [Nat.add_mul_div_right _ _ hp, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt l1,
          Nat.div_eq_of_lt l2] at this
        omega

set_option maxHeartbeats 8000000 in
/-- **A call to `Uint<8>::eq`** of the limbs at offset `cp` and the constant
at `q`. -/
theorem sv_ueq8F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o q : Word} {cp : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (hue : CodeIn M (BitVec.ofNat 32 uint8EqAddress) uint8EqCode)
    (st : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 uint8EqAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 cp) (ha1 : reg n a1 = q)
    (hcp : cp + 32 ≤ 0x1690) (acp : cp % 4 = 0) (hq4 : q.toNat % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      reg n' a0 = (if accV M (B + 0x21A0 + BitVec.ofNat 32 cp) 8 = accV M q 8 then 1 else 0) ∧
      SvKeepL B M n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [r1 sp (by decide), rsp]
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  obtain ⟨n2, c2, pc2, a02, k2, f2⟩ := uint8Eq_correct n1 (base := BitVec.ofNat 32 uint8EqAddress)
    (by rw [mem1]; exact hue) pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (sv_al F (by omega) acp) hq4 (by rw [sp1, hS]; omega)
    (by rw [sp1, sv_sp4]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [sp1, sv_sp4] at f2
  rw [mem1] at a02
  simp only [limbsEq_iff 8] at a02
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by
    rw [k2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp1], fun r hr => ?_, a02,
    fun e he _ => ?_, fun x hx => ?_⟩
  · have hr' : r ≠ a0 ∧ r ≠ a1 ∧ r ≠ a2 ∧ r ≠ a3 ∧ r ≠ a4 ∧ r ≠ a5 ∧ r ≠ ra := by revert hr; revert r; decide
    obtain ⟨q10, q11, q12, q13, q14, q15, q1⟩ := hr'
    rw [k2 r q10 q11 q12 q13 q14 q15, r1 r q1]
  · rw [f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega)), mem1]
  · rw [f2 x (svR_sp4 hx), mem1]

set_option maxHeartbeats 8000000 in
/-- **A call to `SignedInt<8>::norm`** of the value at offset `cx` with `f`'s
sign `fs` in `a2` and the modulus at `np`, into offset `co`. -/
theorem sv_nrm8F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o np fs : Word} {co cx : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (UC : SvUpCode M) (EC : SvEcCode M)
    (hn8 : CodeIn M (BitVec.ofNat 32 norm8Address) norm8Code) (st : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 norm8Address)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cx)
    (ha2 : reg n a2 = fs) (hfs : fs = 0 ∨ fs = 1) (ha3 : reg n a3 = np)
    (hco : co + 32 ≤ 0x1690) (hcx : cx + 33 ≤ 0x1690) (aco : co % 4 = 0) (acx : cx % 4 = 0)
    (hn1 : 0x3FCC4200 ≤ np.toNat) (hn2 : np.toNat + 32 ≤ 0x3FCC4E60) (hn4 : np.toNat % 4 = 0)
    (hσ : (M (B + 0x21A0 + BitVec.ofNat 32 (cx + 0x20))).toNat ≤ 1) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 =
        normVal8 (M (B + 0x21A0 + BitVec.ofNat 32 (cx + 0x20))).toNat fs.toNat
          (accV M (B + 0x21A0 + BitVec.ofNat 32 cx) 8) (accV M np 8) ∧
      SvKeepL B M n'.mem [(co, 32)] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have EN : Nm8Env n1.mem (BitVec.ofNat 32 norm8Address) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 co)
      (B + 0x21A0 + BitVec.ofNat 32 cx) np := by
    rw [mem1]
    refine ⟨by decide, hn8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hS]; omega, by rw [hS]; omega,
      sv_al F (by omega) aco, sv_al F (by omega) acx, hn4, by rw [sv_at F _ (by omega)]; omega,
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide),
      FS.lowN (k := 0x90) (by decide) (by decide) hco, FS.lowN (k := 0x90) (by decide) (by decide) hcx,
      by rw [show n8R (B + 0x21A0) = B + BitVec.ofNat 32 0x2110 from sv_spX B 0x90 (by decide)]
         exact (F.bufData (by decide) hn1 hn2).symm⟩
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

/-- **The panic at 0x1908**: `s` has no inverse, and `CtOption::unwrap`'s
assertion fails. -/
theorem sv_panic_1908 {B : Word} {n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem) (s : St n.mem SV n 0x1908 (reg n))
    (rsp : reg n sp = B + 0x21A0) : Panics n := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x1910) [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221] E.self
    (by decide) ⟨trivial, trivial, trivial⟩
  have s1 : St n.mem SV n1 0x1910 (reg n1) := ⟨u1.pc, u1.mem.trans (by simp only [runBlock, BInstr.run]), fun _ => rfl⟩
  have sp1 : reg n1 sp = B + 0x21A0 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; exact rsp
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := s1.callRa E.self sv_at_1910 sv_at_1914
    (cb := BitVec.ofNat 32 assertFailedU8Address) (by decide) (by decide)
  exact Panics.of_steps (c1.trans c2) (assertFailedU8_panics n2 (by rw [mem2]; exact E.K.panic) pc2
    (by rw [regs2, upd_ne (by decide) (by decide), sp1]; exact FS.room (by decide)))

theorem zext_01 {b : BitVec 8} (h : b.toNat ≤ 1) : b.zeroExtend 32 = 0 ∨ b.zeroExtend 32 = 1 := by
  have : b = 0 ∨ b = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h
    · exact .inl (BitVec.eq_of_toNat_eq h)
    · exact .inr (BitVec.eq_of_toNat_eq h)
  rcases this with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

theorem codeIn_sv {M M0 : Word → BitVec 8} {B b : Word} {c : List Nat} (F : Fr B 0x3830)
    (fR : ∀ x, SvR B x → M x = M0 x) (h : CodeIn M0 b c) (h1 : 0x40000000 ≤ b.toNat)
    (h2 : b.toNat + c.length ≤ 2 ^ 32) : CodeIn M b c :=
  codeHi h h1 h2 fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))

end C3.RV32.Sv
