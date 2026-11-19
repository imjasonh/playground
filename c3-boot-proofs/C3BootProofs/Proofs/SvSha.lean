import C3BootProofs.Proofs.SvFail
import C3BootProofs.Proofs.Sha512Blocks

/-!
# `sigstore::verify`: SHA-384 of the leaf's `tbsCertificate`

`verify_leaf` hashes the `tbsCertificate` with SHA-384 inline: the full
blocks through `sha384UpdateBlocks`, the tail copied into the buffer, then
the padding and the last blocks through `sha512FinBlock`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

theorem sv_sp10 (B : Word) : B + 0x21A0 + 0xFFFFFFF0 = B + BitVec.ofNat 32 0x2190 := by
  rw [BitVec.add_assoc]; rfl

set_option maxHeartbeats 8000000 in
/-- **A `memcpy` of `N` bytes from outside the stack** at `p` into the frame
at offset `c`. -/
theorem sv_mcIn {B : Word} {m : Machine} {off : Nat} {imm o p : Word} {c N : Nat} (F : Fr B 0x3830)
    (E : SvCode m.mem) (s : St m.mem SV m off (reg m))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = MCS) (he8 : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x21A0) (ha0 : reg m a0 = B + 0x21A0 + BitVec.ofNat 32 c)
    (ha1 : reg m a1 = p) (ha2 : reg m a2 = BitVec.ofNat 32 N) (hc : c + N ≤ 0x1690) (hin : SvIn B p N) :
    ∃ m', SvPost B m m' (off + 8) ∧ SvKeep B m.mem m'.mem c N ∧
      ∀ j, j < N → m'.mem (B + 0x21A0 + BitVec.ofNat 32 (c + j)) = m.mem (p + BitVec.ofNat 32 j) := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hb16 : (B + 0x21A0 + 0xFFFFFFF0).toNat = (B + 0x21A0).toNat - 16 := FS.below 16 (by decide) (by decide)
  have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨fA, fW, hFC⟩ := FS.mc
  obtain ⟨n2, c2, u2, fr2, k2⟩ := c_memcpy (dst := B + 0x21A0 + BitVec.ofNat 32 c) (src := p) (S := B + 0x21A0)
    (N := N) s E.self E.K h1 h2 hb he8 hsp ha0 ha1 ha2
    ⟨E.K.body, FS.sepHi (by omega) (by decide) (by decide), hFC, FS.mcN (by omega),
      by rw [sv_sp10]; exact hin.sepLo (by decide),
      by rw [← sv_base']; exact (hin.sepLo (by omega)).symm, fA, fW,
      by rw [FS.at _ (by omega)]; omega, hin.fit⟩
  have lo16 : ∀ x, SvR B x → Sep (B + 0x21A0 + 0xFFFFFFF0) 16 x 1 := fun x hx => svR_lo (k := 16) hx (by decide) (by decide)
  refine ⟨n2, ⟨c2, u2, fun x hx => ?_, fun q hq => ?_⟩, fun e he1 he2 => ?_, fun j hj => ?_⟩
  · rw [fr2 x (lo16 x hx), copyBytes_sep (svR_hi (c := c) (l := N) hx hc) (Nat.le_refl _)]
  · exact k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  · rw [fr2 _ (FS.lowB hb16 (by decide) (by omega)),
      copyBytes_sep (sepS (B + 0x21A0) (c := c) (n := N) (d := e) (k := 1) (by omega) (by omega) (by omega))
        (Nat.le_refl _)]
  · rw [← add_ofNat_assoc, fr2 _ (by rw [add_ofNat_assoc]; exact FS.lowB hb16 (by decide) (by omega)),
      cp_at hj (by omega)]

abbrev SK5 : Word := BitVec.ofNat 32 sha512KAddress

/-- The SHA-512 code `verify_leaf` calls, and the round constants. -/
structure SvShaCode (M : Word → BitVec 8) : Prop where
  blk : CodeIn M (BitVec.ofNat 32 sha384UpdateBlocksAddress) sha384UpdateBlocksCode
  cmp : CodeIn M (BitVec.ofNat 32 sha512CompressAddress) sha512CompressCode
  idx : CodeIn M (BitVec.ofNat 32 rangeFromIndexAddress) rangeFromIndexCode
  fin : CodeIn M (BitVec.ofNat 32 sha512FinBlockAddress) sha512FinBlockCode
  z48 : CodeIn M (BitVec.ofNat 32 zeroArray48Address) zeroArray48Code
  z64 : CodeIn M (BitVec.ofNat 32 zeroArray64Address) zeroArray64Code
  k : CodeIn M SK5 sha512KData

/-- The round constants sit apart from the stack. -/
def SvKSep (B : Word) : Prop := Sep (B + 0xFFFFFE60) 0x39D0 SK5 640

theorem SvShaCode.sv {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3830) (KS : SvKSep B) (D : SvShaCode M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : SvShaCode M := by
  have hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))
  exact ⟨codeHi D.blk (by decide) (by decide) hx, codeHi D.cmp (by decide) (by decide) hx,
    codeHi D.idx (by decide) (by decide) hx, codeHi D.fin (by decide) (by decide) hx,
    codeHi D.z48 (by decide) (by decide) hx, codeHi D.z64 (by decide) (by decide) hx,
    fun i hi' => by
      rw [fR _ (KS.symm.sub (c := i) (l := 1) (by have : sha512KData.length = 640 := rfl; omega)).symm]
      exact D.k i hi'⟩

theorem sv_sp390 (B : Word) : B + 0x21A0 + 0xFFFFFC70 = B + BitVec.ofNat 32 0x1E10 := by
  rw [BitVec.add_assoc]; rfl

set_option maxHeartbeats 16000000 in
/-- **A call to `sha384UpdateBlocks`** with the state at offset `st` and
`nb` blocks at `bp` outside the stack. -/
theorem sv_s5bF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o bp : Word} {st nb : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (SC : SvShaCode M) (KS : SvKSep B) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 sha384UpdateBlocksAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 st) (ha1 : reg n a1 = bp)
    (ha2 : reg n a2 = BitVec.ofNat 32 nb) (hst : st + 0x50 ≤ 0x1690) (hsta : st % 4 = 0)
    (hcnt : (memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 st + 0x40)).toNat + nb < 2 ^ 32)
    (hin : SvIn B bp (128 * nb)) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(st, 0x50)] ∧
      (s5Hv n'.mem (B + 0x21A0 + BitVec.ofNat 32 st)).toList =
        (blockList128 M bp nb).foldl Sha512.compress (s5Hv M (B + 0x21A0 + BitVec.ofNat 32 st)).toList ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 st + 0x40) =
        memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 st + 0x40) + BitVec.ofNat 32 nb ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 st + 0x44) = memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 st + 0x44) ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 st + 0x48) = memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 st + 0x48) ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 st + 0x4C) = memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 st + 0x4C) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have eS : B + 0x21A0 + BitVec.ofNat 32 st = B + BitVec.ofNat 32 (0x21A0 + st) := (sv_base' B st).symm
  have e40 : B + 0x21A0 + BitVec.ofNat 32 st + 0x40 = B + BitVec.ofNat 32 (0x21A0 + st + 0x40) := by
    rw [eS, show (0x40 : Word) = BitVec.ofNat 32 0x40 from rfl, add_ofNat_assoc]
  have stH : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x21A0 + BitVec.ofNat 32 st + 0x40) 16 b l := fun b l h1 h2 => by
    rw [e40]; exact F.sepHi (by omega) h1 h2
  have env : S5Env M (BitVec.ofNat 32 sha512CompressAddress) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 st) bp nb := by
    refine ⟨by decide, SC.cmp, SC.idx, C.K.stub, C.K.body, C.K.mset, SC.k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hS]; omega
    · rw [hS]; omega
    · exact sv_al F (by omega) hsta
    · have := hin.fit; omega
    iterate 5 (· rw [sv_sp390]; exact F.sepHi (by decide) (by decide) (by decide))
    · rw [sv_sp390]; have := KS.sub (c := 0x1A0 + 0x1E10) (l := 0x390) (by decide)
      rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + 0x1E10) = B + BitVec.ofNat 32 0x1E10 by
        rw [BitVec.add_assoc]; rfl] at this
    iterate 5 (· rw [eS]; exact F.sepHi (by omega) (by decide) (by decide))
    · rw [eS]; have := KS.sub (c := 0x1A0 + (0x21A0 + st)) (l := 64) (by omega)
      rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + (0x21A0 + st)) = B + BitVec.ofNat 32 (0x21A0 + st) by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
          BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]; omega] at this
    · rw [eS, sv_sp390]; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp390]; exact hin.sepLo (by decide)
    · rw [eS]; exact hin.sepLo (by omega)
  obtain ⟨n2, c2, pc2, sp2, k2, hv, cnt0, cnt1, cnt2, cnt3, f2⟩ := sha384UpdateBlocks_correct n1
    (by rw [mem1]; exact SC.blk) pc1 (by rw [mem1]; exact env) (by rw [r1 a0 (by decide), ha0])
    (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2]) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev) (by rw [r1 sp (by decide), rsp]) (by rw [mem1]; exact hcnt)
    (stH _ _ (by decide) (by decide)) (stH _ _ (by decide) (by decide)) (stH _ _ (by decide) (by decide))
    (stH _ _ (by decide) (by decide)) (stH _ _ (by decide) (by decide))
    (by rw [e40]; have := KS.sub (c := 0x1A0 + (0x21A0 + st + 0x40)) (l := 16) (by omega)
        rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + (0x21A0 + st + 0x40)) = B + BitVec.ofNat 32 (0x21A0 + st + 0x40) by
          apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
            BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]; omega] at this)
    (by rw [e40, sv_sp390]; exact sepS B (by omega) (by omega) (by omega))
    (by rw [e40]; exact hin.sepLo (by omega))
    (stH _ _ (by decide) (by decide))
  rw [mem1] at hv cnt0 cnt1 cnt2 cnt3 f2
  rw [sv_sp390] at f2
  have hfS : ∀ x, SvR B x → Sep (B + BitVec.ofNat 32 0x1E10) 0x390 x 1 := fun x hx => by
    have := svR_lo (k := 0x390) hx (by decide) (by decide)
    rwa [sv_lo B 0x390 (by decide)] at this
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)],
    fun e he hL => ?_, hv, cnt0, cnt1, cnt2, cnt3, fun x hx => f2 x (hfS x hx) (svR_hi hx hst)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

end C3.RV32.Sv
