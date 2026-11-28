import C3BootProofs.Proofs.P2vDs
import C3BootProofs.Proofs.UpdateFg8
import C3BootProofs.Proofs.UpdateDe8
import C3BootProofs.Proofs.Norm8
import C3BootProofs.Proofs.UintEq
import C3BootProofs.Proofs.Lowest
import C3BootProofs.Proofs.Prim
import C3BootProofs.Proofs.Pv384Lib2
import C3BootProofs.Proofs.Pv384CIt

/-!
# `p256VerifyPrehash`: the inversion's calls

Wrappers for the calls of the inversion of `s`: `u32::min`, `lowest` on 8
limbs, `update_fg::<8>` and `update_de::<8>`, which apply a batch's matrix to
`f` and `g` and to `d` and `e`, `Uint<8>::eq`, and `SignedInt<8>::norm`.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

theorem p2v_sp1 (B : Word) : B + 0x21A0 + 0xFFFFFFFF = B + BitVec.ofNat 32 0x219F := by
  rw [BitVec.add_assoc]; rfl

theorem p2vR_sp1 {B x : Word} (hx : P2vR B x) : Sep (B + BitVec.ofNat 32 0x219F) 1 x 1 := by
  have := p2vR_lo (k := 1) hx (by decide) (by decide)
  rwa [p2v_lo B 1 (by decide)] at this

/-- The inversion's code beyond `P2vEcCode`. -/
structure P2vIvCode (M : Word → BitVec 8) : Prop where
  umin : CodeIn M (BitVec.ofNat 32 u32MinAddress) u32MinCode
  low8 : CodeIn M (BitVec.ofNat 32 lowest8Address) lowest8Code
  sel64 : CodeIn M (BitVec.ofNat 32 selectI64Address) selectI64Code

theorem P2vIvCode.p2v {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3590) (D : P2vIvCode M0)
    (fR : ∀ x, P2vR B x → M x = M0 x) : P2vIvCode M := by
  have hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))
  exact ⟨codeHi D.umin (by decide) (by decide) hx, codeHi D.low8 (by decide) (by decide) hx,
    codeHi D.sel64 (by decide) (by decide) hx⟩

/-- **A call to `u32::min(a0, 62)`**. -/
theorem p2v_uminF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o a : Word}
    (F : Fr B 0x3590) (C : P2vCode M) (IC : P2vIvCode M) (s : St M P2V n off (reg n))
    (h1 : fetchRel p256VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P2V + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 u32MinAddress)
    (hev : (P2V + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = a) :
    ∃ n', Steps n n' ∧ St n'.mem P2V n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      reg n' a0 = (if a.toNat < 62 then a else 62) ∧
      P2vKeepL B M n'.mem [] ∧ (∀ x, P2vR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [r1 sp (by decide), rsp]
  obtain ⟨n2, c2, pc2, a02, k2, f2⟩ := u32Min_correct n1 (base := BitVec.ofNat 32 u32MinAddress)
    (by rw [mem1]; exact IC.umin) pc1 (by rw [r1 a0 (by decide), ha0])
    (by rw [sp1, p2v_sp1]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [sp1, p2v_sp1] at f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [k2 sp (by decide) (by decide) (by decide)
    (by decide), sp1], fun r hr => ?_, a02, fun e he _ => ?_, fun x hx => ?_⟩
  · have hr' : r ≠ a0 ∧ r ≠ a1 ∧ r ≠ a2 ∧ r ≠ a3 ∧ r ≠ ra := by revert hr; revert r; decide
    obtain ⟨q10, q11, q12, q13, q1⟩ := hr'
    rw [k2 r q10 q11 q12 q13, r1 r q1]
  · rw [f2 _ (by rw [← p2v_base']; exact sepS B (by omega) (by omega) (by omega)), mem1]
  · rw [f2 x (p2vR_sp1 hx), mem1]

/-- **A call to `lowest` on 8 limbs** at offset `oc`, whose sign byte is at
`oc + 0x20`. -/
theorem p2v_low8F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {oc : Nat}
    (F : Fr B 0x3590) (C : P2vCode M) (IC : P2vIvCode M) (s : St M P2V n off (reg n))
    (h1 : fetchRel p256VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P2V + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 lowest8Address)
    (hev : (P2V + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc) (ho : oc + 0x24 ≤ 0x13F0) (ho4 : oc % 4 = 0)
    (hσ : (M (B + 0x21A0 + BitVec.ofNat 32 (oc + 0x20))).toNat ≤ 1) :
    ∃ n', Steps n n' ∧ St n'.mem P2V n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      (reg n' a0).toNat + 2 ^ 32 * (reg n' a1).toNat =
        lowestVal (M (B + 0x21A0 + BitVec.ofNat 32 (oc + 0x20))).toNat (accV M (B + 0x21A0 + BitVec.ofNat 32 oc) 2) ∧
      P2vKeepL B M n'.mem [] ∧ (∀ x, P2vR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [r1 sp (by decide), rsp]
  have eS : BitVec.ofNat 32 lowest8Address + 0x22 = BitVec.ofNat 32 selectI64Address := by decide
  obtain ⟨n2, c2, pc2, sp2, k2, L2, f2⟩ := lowest8_correct n1 (P := BitVec.ofNat 32 lowest8Address)
    (by decide) (by rw [mem1]; exact IC.low8) (by rw [mem1, eS]; exact IC.sel64) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
    (p2v_al F (by omega) ho4) (by rw [mem1, show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, add_ofNat_assoc]; exact hσ)
    (by rw [sp1, p2v_sp1, eS]; exact F.sepHi (by decide) (by decide) (by decide))
  rw [mem1, show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, add_ofNat_assoc] at L2
  rw [sp1, p2v_sp1] at f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, sp1],
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], L2,
    fun e he _ => ?_, fun x hx => ?_⟩
  · rw [f2 _ (fun h => by
      have := (sepS B (c := 0x219F) (n := 1) (d := 0x21A0 + e) (k := 1) (by omega) (by omega) (by omega)) 0
        (by decide) 0 (by decide)
      rw [add_ofNat_zero, add_ofNat_zero] at this; rw [← p2v_base'] at h; exact this h.symm), mem1]
  · rw [f2 x (fun h => by
      have := p2vR_sp1 hx 0 (by decide) 0 (by decide)
      rw [add_ofNat_zero, add_ofNat_zero] at this; exact this h.symm), mem1]

theorem w64_split {a b : Word} {L : Nat} (h : a.toNat + 2 ^ 32 * b.toNat = L) :
    a = BitVec.ofNat 32 (L % 2 ^ 32) ∧ b = BitVec.ofNat 32 (L / 2 ^ 32) := by
  have ha := a.isLt; have hb := b.isLt
  constructor <;> apply BitVec.eq_of_toNat_eq <;> rw [BitVec.toNat_ofNat] <;> omega

theorem acc2_of8 {M : Word → BitVec 8} {p : Word} {V : Nat} (h : accV M p 8 = V) : accV M p 2 = V % 2 ^ 64 := by
  rw [← h, ← accV_mod64 M p 6]

theorem umin_ne0 {a : Word} (h : a ≠ 0) : (if a.toNat < 62 then a else 62) ≠ 0 := by
  split
  · exact h
  · decide


/-- `update_fg::<8>` and `update_de::<8>` and their callees, at the offsets
their environments name. -/
structure P2vUpCode (M : Word → BitVec 8) : Prop where
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

theorem P2vUpCode.p2v {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3590) (D : P2vUpCode M0)
    (fR : ∀ x, P2vR B x → M x = M0 x) : P2vUpCode M := by
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
abbrev p2vI (M : Word → BitVec 8) (B : Word) (c : Nat) : Int :=
  sgnVal (M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x20))).toNat (accV M (B + 0x21A0 + BitVec.ofNat 32 c) 8)

/-- A 64-bit matrix entry at offset `c`, as a signed integer. -/
abbrev p2vM (M : Word → BitVec 8) (B : Word) (c : Nat) : Int := i64Val (accV M (B + 0x21A0 + BitVec.ofNat 32 c) 2)

set_option maxHeartbeats 16000000 in
/-- **A call to `update_fg::<8>`**: `f` at offset `ca` and `g` at `cb` times
the rows of the matrix at `ct`, shifted right by `s`, into `co` and
`co + 0x24`. -/
theorem p2v_ufg8F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o : Word} {co ca cb ct s : Nat}
    (F : Fr B 0x3590) (C : P2vCode M) (UC : P2vUpCode M) (st : St M P2V n off (reg n))
    (h1 : fetchRel p256VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P2V + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 updateFg8Address)
    (hev : (P2V + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 ca)
    (ha2 : reg n a2 = B + 0x21A0 + BitVec.ofNat 32 cb) (ha3 : reg n a3 = B + 0x21A0 + BitVec.ofNat 32 ct)
    (ha4 : reg n a4 = BitVec.ofNat 32 s) (hs1 : 1 ≤ s) (hs2 : s ≤ 63)
    (hco : co + 0x45 ≤ 0x13F0) (hca : ca + 33 ≤ 0x13F0) (hcb : cb + 33 ≤ 0x13F0) (hct : ct + 32 ≤ 0x13F0)
    (aco : co % 4 = 0) (aca : ca % 4 = 0) (acb : cb % 4 = 0) (act : ct % 4 = 0)
    (sa : ca + 33 ≤ co ∨ co + 0x45 ≤ ca) (sb : cb + 33 ≤ co ∨ co + 0x45 ≤ cb) (stt : ct + 32 ≤ co ∨ co + 0x45 ≤ ct)
    (hσa : (M (B + 0x21A0 + BitVec.ofNat 32 (ca + 0x20))).toNat ≤ 1)
    (hσb : (M (B + 0x21A0 + BitVec.ofNat 32 (cb + 0x20))).toNat ≤ 1) :
    ∃ n', Steps n n' ∧ St n'.mem P2V n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      (∃ σ A, σ ≤ 1 ∧ sgnVal σ A = p2vI M B ca * p2vM M B ct + p2vI M B cb * p2vM M B (ct + 8) ∧
        (n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x20))).toNat = σ ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 = A / 2 ^ s % 2 ^ 256) ∧
      (∃ σ A, σ ≤ 1 ∧ sgnVal σ A = p2vI M B ca * p2vM M B (ct + 0x10) + p2vI M B cb * p2vM M B (ct + 0x18) ∧
        (n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x24 + 0x20))).toNat = σ ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x24)) 8 = A / 2 ^ s % 2 ^ 256) ∧
      P2vKeepL B M n'.mem [(co, 0x45)] ∧ (∀ x, P2vR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x13F0 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hG : (B + BitVec.ofNat 32 0x1F70).toNat = B.toNat + 0x1F70 := F.at 0x1F70 (by decide)
  have gH : ∀ {b : Word} {len : Nat}, 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 →
      Sep (B + BitVec.ofNat 32 0x1F70) 0x230 b len := fun h1 h2 => F.sepHi (by decide) h1 h2
  have gD : ∀ {b : Word} {len : Nat}, (img% dataWindowAddress) ≤ b.toNat → b.toNat + len ≤ (img% dataWindowAddress + dataWindowSize) →
      Sep (B + BitVec.ofNat 32 0x1F70) 0x230 b len := fun h1 h2 => F.bufData (by decide) h1 h2
  have gF : ∀ {c l : Nat}, c + l ≤ 0x13F0 → Sep (B + 0x21A0 + BitVec.ofNat 32 c) l (B + BitVec.ofNat 32 0x1F70) 0x230 :=
    fun h => by rw [← p2v_base']; exact sepS B (by omega) (by omega) (by omega)
  have EN : UFEnv8 n1.mem (BitVec.ofNat 32 updateFg8Address) (B + BitVec.ofNat 32 0x1F70)
      (B + 0x21A0 + BitVec.ofNat 32 co) (B + 0x21A0 + BitVec.ofNat 32 ca) (B + 0x21A0 + BitVec.ofNat 32 cb)
      (B + 0x21A0 + BitVec.ofNat 32 ct) := by
    rw [mem1]
    refine ⟨by decide, UC.fg, UC.fg_fi, UC.ls, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, UC.zero, UC.one, ?_, ?_, ?_,
      by rw [hG]; omega, by rw [hG]; omega,
      p2v_al F (by omega) aco, p2v_al F (by omega) aca, p2v_al F (by omega) acb, p2v_al F (by omega) act,
      by rw [p2v_at F _ (by omega)]; omega, by rw [p2v_at F _ (by omega)]; omega, by rw [p2v_at F _ (by omega)]; omega,
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
    fun x hx => fr2 x (p2vR_spX hx (by decide) (by decide) (by decide)) (p2vR_hi hx hco)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  exact fr2 _ (by rw [← p2v_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

set_option maxHeartbeats 16000000 in
/-- **A call to `update_de::<8>`**: `d` at offset `ca` and `e` at `cb` times
the rows of the matrix at `ct`, reduced modulo the constant at `mp` with
`-mp⁻¹ mod 2^64` in `a5:a4`, into `co` and `co + 0x24`. -/
theorem p2v_ude8F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o mp mlo mhi : Word}
    {co ca cb ct s : Nat}
    (F : Fr B 0x3590) (C : P2vCode M) (UC : P2vUpCode M) (st : St M P2V n off (reg n))
    (h1 : fetchRel p256VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P2V + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 updateDe8Address)
    (hev : (P2V + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 ca)
    (ha2 : reg n a2 = B + 0x21A0 + BitVec.ofNat 32 cb) (ha3 : reg n a3 = mp) (ha4 : reg n a4 = mlo)
    (ha5 : reg n a5 = mhi) (ha6 : reg n a6 = B + 0x21A0 + BitVec.ofNat 32 ct)
    (ha7 : reg n (17 : Fin 32) = BitVec.ofNat 32 s) (hs1 : 1 ≤ s) (hs2 : s ≤ 63)
    (hco : co + 0x45 ≤ 0x13F0) (hca : ca + 33 ≤ 0x13F0) (hcb : cb + 33 ≤ 0x13F0) (hct : ct + 32 ≤ 0x13F0)
    (aco : co % 4 = 0) (aca : ca % 4 = 0) (acb : cb % 4 = 0) (act : ct % 4 = 0)
    (sa : ca + 33 ≤ co ∨ co + 0x45 ≤ ca) (sb : cb + 33 ≤ co ∨ co + 0x45 ≤ cb) (stt : ct + 32 ≤ co ∨ co + 0x45 ≤ ct)
    (hm1 : (img% dataWindowAddress) ≤ mp.toNat) (hm2 : mp.toNat + 32 ≤ (img% dataWindowAddress + dataWindowSize)) (hm4 : mp.toNat % 4 = 0)
    (hσa : (M (B + 0x21A0 + BitVec.ofNat 32 (ca + 0x20))).toNat ≤ 1)
    (hσb : (M (B + 0x21A0 + BitVec.ofNat 32 (cb + 0x20))).toNat ≤ 1) :
    ∃ n', Steps n n' ∧ St n'.mem P2V n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      (∃ σ A, σ ≤ 1 ∧ sgnVal σ A = p2vI M B ca * p2vM M B ct + p2vI M B cb * p2vM M B (ct + 8) ∧
        (n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x20))).toNat =
          (lrsm8 σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV M mp 8)).1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 = (lrsm8 σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV M mp 8)).2) ∧
      (∃ σ A, σ ≤ 1 ∧ sgnVal σ A = p2vI M B ca * p2vM M B (ct + 0x10) + p2vI M B cb * p2vM M B (ct + 0x18) ∧
        (n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x24 + 0x20))).toNat =
          (lrsm8 σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV M mp 8)).1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 (co + 0x24)) 8 =
          (lrsm8 σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV M mp 8)).2) ∧
      P2vKeepL B M n'.mem [(co, 0x45)] ∧ (∀ x, P2vR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have FS : Fr (B + 0x21A0) 0x13F0 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hG : (B + BitVec.ofNat 32 0x1ED0).toNat = B.toNat + 0x1ED0 := F.at 0x1ED0 (by decide)
  have gH : ∀ {b : Word} {len : Nat}, 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 →
      Sep (B + BitVec.ofNat 32 0x1ED0) 0x2D0 b len := fun h1 h2 => F.sepHi (by decide) h1 h2
  have gD : ∀ {b : Word} {len : Nat}, (img% dataWindowAddress) ≤ b.toNat → b.toNat + len ≤ (img% dataWindowAddress + dataWindowSize) →
      Sep (B + BitVec.ofNat 32 0x1ED0) 0x2D0 b len := fun h1 h2 => F.bufData (by decide) h1 h2
  have gF : ∀ {c l : Nat}, c + l ≤ 0x13F0 → Sep (B + 0x21A0 + BitVec.ofNat 32 c) l (B + BitVec.ofNat 32 0x1ED0) 0x2D0 :=
    fun h => by rw [← p2v_base']; exact sepS B (by omega) (by omega) (by omega)
  have oH : ∀ {b : Word} {len : Nat}, 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 →
      Sep (B + 0x21A0 + BitVec.ofNat 32 co) 0x45 b len := fun h1 h2 => FS.sepHi hco h1 h2
  have oD : ∀ {b : Word} {len : Nat}, (img% dataWindowAddress) ≤ b.toNat → b.toNat + len ≤ (img% dataWindowAddress + dataWindowSize) →
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
      p2v_al F (by omega) aco, p2v_al F (by omega) aca, p2v_al F (by omega) acb, hm4, p2v_al F (by omega) act,
      by rw [p2v_at F _ (by omega)]; omega, by rw [p2v_at F _ (by omega)]; omega, by rw [p2v_at F _ (by omega)]; omega,
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
    fun x hx => fr2 x (p2vR_spX hx (by decide) (by decide) (by decide)) (p2vR_hi hx hco)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  exact fr2 _ (by rw [← p2v_base']; exact sepS B (by omega) (by omega) (by omega))
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
theorem p2v_ueq8F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o q : Word} {cp : Nat}
    (F : Fr B 0x3590) (C : P2vCode M) (hue : CodeIn M (BitVec.ofNat 32 uint8EqAddress) uint8EqCode)
    (st : St M P2V n off (reg n))
    (h1 : fetchRel p256VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P2V + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 uint8EqAddress)
    (hev : (P2V + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 cp) (ha1 : reg n a1 = q)
    (hcp : cp + 32 ≤ 0x13F0) (acp : cp % 4 = 0) (hq4 : q.toNat % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem P2V n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      reg n' a0 = (if accV M (B + 0x21A0 + BitVec.ofNat 32 cp) 8 = accV M q 8 then 1 else 0) ∧
      P2vKeepL B M n'.mem [] ∧ (∀ x, P2vR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [r1 sp (by decide), rsp]
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  obtain ⟨n2, c2, pc2, a02, k2, f2⟩ := uint8Eq_correct n1 (base := BitVec.ofNat 32 uint8EqAddress)
    (by rw [mem1]; exact hue) pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (p2v_al F (by omega) acp) hq4 (by rw [sp1, hS]; omega)
    (by rw [sp1, p2v_sp4]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [sp1, p2v_sp4] at f2
  rw [mem1] at a02
  simp only [limbsEq_iff 8] at a02
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by
    rw [k2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp1], fun r hr => ?_, a02,
    fun e he _ => ?_, fun x hx => ?_⟩
  · have hr' : r ≠ a0 ∧ r ≠ a1 ∧ r ≠ a2 ∧ r ≠ a3 ∧ r ≠ a4 ∧ r ≠ a5 ∧ r ≠ ra := by revert hr; revert r; decide
    obtain ⟨q10, q11, q12, q13, q14, q15, q1⟩ := hr'
    rw [k2 r q10 q11 q12 q13 q14 q15, r1 r q1]
  · rw [f2 _ (by rw [← p2v_base']; exact sepS B (by omega) (by omega) (by omega)), mem1]
  · rw [f2 x (p2vR_sp4 hx), mem1]

set_option maxHeartbeats 8000000 in
/-- **A call to `SignedInt<8>::norm`** of the value at offset `cx` with `f`'s
sign `fs` in `a2` and the modulus at `np`, into offset `co`. -/
theorem p2v_nrm8F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o np fs : Word} {co cx : Nat}
    (F : Fr B 0x3590) (C : P2vCode M) (UC : P2vUpCode M) (EC : P2vEcCode M)
    (hn8 : CodeIn M (BitVec.ofNat 32 norm8Address) norm8Code) (st : St M P2V n off (reg n))
    (h1 : fetchRel p256VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P2V + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 norm8Address)
    (hev : (P2V + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (rsp : reg n sp = B + 0x21A0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 co) (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 cx)
    (ha2 : reg n a2 = fs) (hfs : fs = 0 ∨ fs = 1) (ha3 : reg n a3 = np)
    (hco : co + 32 ≤ 0x13F0) (hcx : cx + 33 ≤ 0x13F0) (aco : co % 4 = 0) (acx : cx % 4 = 0)
    (hn1 : (img% dataWindowAddress) ≤ np.toNat) (hn2 : np.toNat + 32 ≤ (img% dataWindowAddress + dataWindowSize)) (hn4 : np.toNat % 4 = 0)
    (hσ : (M (B + 0x21A0 + BitVec.ofNat 32 (cx + 0x20))).toNat ≤ 1) :
    ∃ n', Steps n n' ∧ St n'.mem P2V n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 8 =
        normVal8 (M (B + 0x21A0 + BitVec.ofNat 32 (cx + 0x20))).toNat fs.toNat
          (accV M (B + 0x21A0 + BitVec.ofNat 32 cx) 8) (accV M np 8) ∧
      P2vKeepL B M n'.mem [(co, 32)] ∧ (∀ x, P2vR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 st.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have FS : Fr (B + 0x21A0) 0x13F0 := F.sub (c := 0x21A0) (by decide) (by decide)
  have EN : Nm8Env n1.mem (BitVec.ofNat 32 norm8Address) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 co)
      (B + 0x21A0 + BitVec.ofNat 32 cx) np := by
    rw [mem1]
    refine ⟨by decide, hn8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hS]; omega, by rw [hS]; omega,
      p2v_al F (by omega) aco, p2v_al F (by omega) acx, hn4, by rw [p2v_at F _ (by omega)]; omega,
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.lowHi (by decide) rfl (by decide) (by decide), FS.lowHi (by decide) rfl (by decide) (by decide),
      FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide), FS.sepHi hco (by decide) (by decide),
      FS.lowN (k := 0x90) (by decide) (by decide) hco, FS.lowN (k := 0x90) (by decide) (by decide) hcx,
      by rw [show n8R (B + 0x21A0) = B + BitVec.ofNat 32 0x2110 from p2v_spX B 0x90 (by decide)]
         exact (F.bufData (by decide) hn1 hn2).symm⟩
    · rw [show BitVec.ofNat 32 norm8Address + 0xFFFFFEA4 = BitVec.ofNat 32 uint8IsNonzeroAddress by decide]; exact EC.unz8
    · rw [show BitVec.ofNat 32 norm8Address + 0xFFFEF2A2 = BitVec.ofNat 32 uintRefIsNonzeroAddress by decide]
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
  have e1 : n8R (B + 0x21A0) = B + BitVec.ofNat 32 0x2110 := p2v_spX B 0x90 (by decide)
  rw [mem1, e1] at f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], A2,
    fun e he hL => ?_, fun x hx => f2 x (p2vR_spX hx (by decide) (by decide) (by decide)) (p2vR_hi hx hco)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  exact f2 _ (by rw [← p2v_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

theorem zext_01 {b : BitVec 8} (h : b.toNat ≤ 1) : b.zeroExtend 32 = 0 ∨ b.zeroExtend 32 = 1 := by
  have : b = 0 ∨ b = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h
    · exact .inl (BitVec.eq_of_toNat_eq h)
    · exact .inr (BitVec.eq_of_toNat_eq h)
  rcases this with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

theorem codeIn_p2v {M M0 : Word → BitVec 8} {B b : Word} {c : List Nat} (F : Fr B 0x3590)
    (fR : ∀ x, P2vR B x → M x = M0 x) (h : CodeIn M0 b c) (h1 : 0x40000000 ≤ b.toNat)
    (h2 : b.toNat + c.length ≤ 2 ^ 32) : CodeIn M b c :=
  codeHi h h1 h2 fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))


def p2vScB : List BInstr := [.lw a2 a1 0x0, .aluImm .add a0 a0 0x1, .aluImm .add a1 a1 0x4]
theorem p2vScB_end : blockEnd p256VerifyPrehashCode 0x3EC p2vScB = some 0x3F2 := by decide

/-- **The scan** at 0x3E8 for a nonzero limb of `g`, from limb `i`: to 0x610
when all 8 are zero, and to 0x3F8 otherwise. -/
theorem p2v_scan {Mx : Word → BitVec 8} {B : Word} (F : Fr B 0x3590) (hc : CodeIn Mx P2V p256VerifyPrehashCode) :
    ∀ j i {m : Machine}, i + j = 8 → St Mx P2V m 0x3E8 (reg m) → reg m a0 = BitVec.ofNat 32 i + 0xFFFFFFFF →
      reg m a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 + BitVec.ofNat 32 (4 * i) → reg m 27 = BitVec.ofNat 32 0x7 →
      (∀ k, k < i → memLoad32 Mx (B + 0x21A0 + BitVec.ofNat 32 0x200 + BitVec.ofNat 32 (4 * k)) = 0) →
      ∃ m', Steps m m' ∧ (∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m' q = reg m q) ∧
        (((∀ k, k < 8 → memLoad32 Mx (B + 0x21A0 + BitVec.ofNat 32 0x200 + BitVec.ofNat 32 (4 * k)) = 0) ∧
          St Mx P2V m' 0x610 (reg m')) ∨
         ((¬ ∀ k, k < 8 → memLoad32 Mx (B + 0x21A0 + BitVec.ofNat 32 0x200 + BitVec.ofNat 32 (4 * k)) = 0) ∧
          St Mx P2V m' 0x3F8 (reg m'))) := by
  intro j
  induction j with
  | zero =>
    intro i m hij st h0 _ h27 hz
    obtain rfl : i = 8 := by omega
    obtain ⟨m1, d1, u1⟩ := st.taken hc 0x610 p2v_at_3e8 (by decide)
      (by show (reg m a0 == reg m 27) = true; rw [h0, h27, ofNat_pred 7]; rfl)
    exact ⟨m1, .single d1, fun q _ _ _ => u1.regs q, .inl ⟨hz, u1.self⟩⟩
  | succ j ih =>
    intro i m hij st h0 h1 h27 hz
    have hi : i < 8 := by omega
    have hne : reg m a0 ≠ reg m 27 := by
      rw [h0, h27]
      cases i with
      | zero => decide
      | succ i =>
        rw [ofNat_pred i]; intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        omega
    obtain ⟨m1, d1, u1⟩ := st.notTaken hc 0x3EC p2v_at_3e8 (by decide)
      (by show (reg m a0 == reg m 27) = false; simpa using hne)
    have hal : (B + 0x21A0 + BitVec.ofNat 32 0x200 + BitVec.ofNat 32 (4 * i)).toNat % 4 = 0 := by
      rw [add_ofNat_assoc]; exact p2v_al F (by omega) (by omega)
    obtain ⟨m2, c2, u2⟩ := u1.self.block p2vScB hc p2vScB_end
      ⟨by show (reg m1 a1 + 0x0).toNat % 4 = 0
          rw [u1.regs, h1, show (0x0 : Word) = BitVec.ofNat 32 0 from rfl, add_ofNat_zero]; exact hal,
        trivial, trivial, trivial⟩
    have s2 : St Mx P2V m2 0x3F2 (reg m2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
    have e1 : reg m1 = reg m := funext u1.regs
    have r2a2 : reg m2 a2 = memLoad32 Mx (B + 0x21A0 + BitVec.ofNat 32 0x200 + BitVec.ofNat 32 (4 * i)) := by
      rw [u2.regs, e1]; simp +decide only [runBlock, BInstr.run, p2vScB, upd, ↓reduceIte, aluEval]
      rw [h1, show (0x0 : Word) = BitVec.ofNat 32 0 from rfl, add_ofNat_zero]
    have r2a0 : reg m2 a0 = BitVec.ofNat 32 i := by
      rw [u2.regs, e1]; simp +decide only [runBlock, BInstr.run, p2vScB, upd, ↓reduceIte, aluEval]
      rw [h0, BitVec.add_assoc, show (0xFFFFFFFF : Word) + 0x1 = 0 from rfl]; exact BitVec.add_zero _
    have r2a1 : reg m2 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 + BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [u2.regs, e1]; simp +decide only [runBlock, BInstr.run, p2vScB, upd, ↓reduceIte, aluEval]
      rw [h1, BitVec.add_assoc, show BitVec.ofNat 32 (4 * i) + 0x4 = BitVec.ofNat 32 (4 * (i + 1)) by
        rw [show (0x4 : Word) = BitVec.ofNat 32 4 from rfl, BitVec.ofNat_add_ofNat, show 4 * i + 4 = 4 * (i + 1) by omega]]
    have k2 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m2 q = reg m q := fun q h0' h1' h2' => by
      have hq : q ∉ p2vScB.filterMap BInstr.dst := by
        simp only [p2vScB, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0', h1', h2']
      rw [u2.regs, e1, runBlock_reg _ _ _ q st.zero hq]
    by_cases hw : memLoad32 Mx (B + 0x21A0 + BitVec.ofNat 32 0x200 + BitVec.ofNat 32 (4 * i)) = 0
    · obtain ⟨m3, d3, u3⟩ := s2.taken hc 0x3E8 p2v_at_3f2 (by decide)
        (by show (reg m2 a2 == reg m2 x0) = true; rw [r2a2, hw, s2.zero]; rfl)
      obtain ⟨m4, c4, k4, h4⟩ := ih (i + 1) (by omega) u3.self (by rw [u3.regs, r2a0, ofNat_pred i])
        (by rw [u3.regs, r2a1]) (by rw [u3.regs, k2 27 (by decide) (by decide) (by decide), h27])
        (fun k hk => by
          rcases Nat.lt_or_ge k i with h | h
          · exact hz k h
          · obtain rfl : k = i := by omega
            exact hw)
      exact ⟨m4, .cons d1 (c2.trans (.cons d3 c4)), fun q h0' h1' h2' => by
        rw [k4 q h0' h1' h2', u3.regs, k2 q h0' h1' h2'], h4⟩
    · obtain ⟨m3, d3, u3⟩ := s2.notTaken hc 0x3F4 p2v_at_3f2 (by decide)
        (by show (reg m2 a2 == reg m2 x0) = false; rw [r2a2, s2.zero]; simpa using hw)
      obtain ⟨m4, d4, u4⟩ := u3.self.notTaken hc 0x3F8 p2v_at_3f4 (by decide)
        (by
          show (reg m3 27).ult (reg m3 a0) = false
          rw [u3.regs, u3.regs, k2 27 (by decide) (by decide) (by decide), h27, r2a0]
          simp only [BitVec.ult, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (show i < 2 ^ 32 by omega)]
          simp only [decide_eq_false_iff_not]; omega)
      exact ⟨m4, .cons d1 (c2.trans (.cons d3 (.single d4))), fun q h0' h1' h2' => by
        rw [u4.regs, u3.regs, k2 q h0' h1' h2'], .inr ⟨fun h => hw (h i hi), u4.self⟩⟩

/-- **The panic at 0x10C8**: `s` has no inverse, and `CtOption::unwrap`'s
assertion fails. -/
theorem p2v_panic_10c8 {B : Word} {n : Machine} (F : Fr B 0x3590) (E : P2vCode n.mem)
    (s : St n.mem P2V n 0x10C8 (reg n)) (rsp : reg n sp = B + 0x21A0) : Panics n := by
  have FS : Fr (B + 0x21A0) 0x13F0 := F.sub (c := 0x21A0) (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x10D0) [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x481] E.self
    (by decide) ⟨trivial, trivial, trivial⟩
  have s1 : St n.mem P2V n1 0x10D0 (reg n1) := ⟨u1.pc, u1.mem.trans (by simp only [runBlock, BInstr.run]), fun _ => rfl⟩
  have sp1 : reg n1 sp = B + 0x21A0 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; exact rsp
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := s1.callRa E.self p2v_at_10d0 p2v_at_10d4
    (cb := BitVec.ofNat 32 assertFailedU8Address) (by decide) (by decide)
  exact Panics.of_steps (c1.trans c2) (assertFailedU8_panics n2 (by rw [mem2]; exact E.K.panic) pc2
    (by rw [regs2, upd_ne (by decide) (by decide), sp1]; exact FS.room (by decide)))

end C3.RV32.P2v
