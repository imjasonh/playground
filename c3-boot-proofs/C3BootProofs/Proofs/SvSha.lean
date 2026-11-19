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

end C3.RV32.Sv
