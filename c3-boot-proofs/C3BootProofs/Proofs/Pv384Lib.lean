import C3BootProofs.Proofs.Pv384A
import C3BootProofs.Proofs.NonZero384
import C3BootProofs.Proofs.Select
import C3BootProofs.Proofs.Bytes2Scalar384
import C3BootProofs.Proofs.P384Neg
import C3BootProofs.Image.BootloaderData2

/-!
# `p384_verify_prehash`: calls in the caller's terms

Each wrapper runs one call from `p384_verify_prehash` with `sp` at
`B + 0x420` and states what the call leaves in the caller's frame: which
bytes of the frame it wrote, what it wrote there, and that it kept the
callee-saved registers and everything outside the frame.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

/-- Proves `a = B + 0x420 + BitVec.ofNat 32 c` and other sums of words with
constant offsets. -/
macro "pv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq
             simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]
               <;> omega))

/-- Proves that a register holds a value: by `rfl`, `decide`, or as a sum. -/
macro "pv_val" : tactic => `(tactic| first | pv_addr | decide | rfl)

/-- `x` is outside the 0x230C bytes that `p384_verify_prehash` and its
callees may write. -/
abbrev PvR (B x : Word) : Prop := Sep (B + 0xFFFFFE60) 0x230C x 1

/-- `M'` agrees with `M` on the caller's frame below the saves, except on the
`w` bytes at offset `c`. -/
def PvKeep (B : Word) (M M' : Word → BitVec 8) (c w : Nat) : Prop :=
  ∀ e, e + 1 ≤ 0x1D4C → (e < c ∨ c + w ≤ e) →
    M' (B + 0x420 + BitVec.ofNat 32 e) = M (B + 0x420 + BitVec.ofNat 32 e)

/-- `m'` has returned to `off'` from a call at `m`, keeping the callee-saved
registers, `sp`, and everything outside the frame. -/
structure PvPost (B : Word) (m m' : Machine) (off' : Nat) : Prop where
  steps : Steps m m'
  st : St m'.mem PV m' off' (reg m')
  fr : ∀ x, PvR B x → m'.mem x = m.mem x
  regs : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q

/-- More functions `p384_verify_prehash` calls, at their addresses in the image. -/
structure PvCode2 (M : Word → BitVec 8) : Prop where
  nw : CodeIn M (BitVec.ofNat 32 p384ScalarNewAddress) p384ScalarNewCode
  nz : CodeIn M (BitVec.ofNat 32 nonZero384Address) nonZero384Code
  mce : CodeIn M (BitVec.ofNat 32 montyScalarCtEq384Address) montyScalarCtEq384Code
  cn : CodeIn M (BitVec.ofNat 32 choiceNotAddress) choiceNotCode
  cu : CodeIn M (BitVec.ofNat 32 ctUnwrap384Address) ctUnwrap384Code
  unz : CodeIn M (BitVec.ofNat 32 uint12IsNonzeroAddress) uint12IsNonzeroCode
  bs : CodeIn M BS bytes2scalar384Code
  lz : CodeIn M (BitVec.ofNat 32 leadingZerosAddress) leadingZerosCode
  exu : CodeIn M (BitVec.ofNat 32 expectUsizeAddress) expectUsizeCode

theorem PvCode2.hi {M M' : Word → BitVec 8} (C : PvCode2 M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    PvCode2 M' :=
  ⟨codeHi C.nw (by decide) (by decide) h, codeHi C.nz (by decide) (by decide) h,
    codeHi C.mce (by decide) (by decide) h, codeHi C.cn (by decide) (by decide) h,
    codeHi C.cu (by decide) (by decide) h, codeHi C.unz (by decide) (by decide) h,
    codeHi C.bs (by decide) (by decide) h, codeHi C.lz (by decide) (by decide) h,
    codeHi C.exu (by decide) (by decide) h⟩

/-- More constants `p384_verify_prehash` reads. -/
structure PvData2 (M : Word → BitVec 8) : Prop where
  zero : CodeIn M (BitVec.ofNat 32 scalarZero384Address) scalarZero384Data
  nmod : CodeIn M n3M p384OrderData
  r2 : CodeIn M n3R2A p384ScalarR2Data
  one : CodeIn M (BitVec.ofNat 32 p384MontOneAddress) p384MontOneData
  idp : CodeIn M (BitVec.ofNat 32 p384IdentityAddress) p384IdentityData
  g : CodeIn M (BitVec.ofNat 32 p384GAddress) p384GData
  u1 : CodeIn M (BitVec.ofNat 32 u12OneAddress) u12OneData

theorem PvData2.of {M M' : Word → BitVec 8} {S : Word} {N : Nat} (F : Fr S N) (D : PvData2 M)
    (h : ∀ x, Sep (S + 0xFFFFFE60) (N + 0x1A0) x 1 → M' x = M x) : PvData2 M' :=
  ⟨F.dataIn h D.zero (by decide) (by decide), F.dataIn h D.nmod (by decide) (by decide),
    F.dataIn h D.r2 (by decide) (by decide), F.dataIn h D.one (by decide) (by decide),
    F.dataIn h D.idp (by decide) (by decide), F.dataIn h D.g (by decide) (by decide),
    F.dataIn h D.u1 (by decide) (by decide)⟩

/-- The code and constants `p384_verify_prehash` needs. -/
structure PvEnv (M : Word → BitVec 8) : Prop where
  C : PvCode M
  D : PvData M
  C2 : PvCode2 M
  D2 : PvData2 M

theorem pvR_of_hi {B : Word} (F : Fr B 0x21A0) {x : Word} (hx : 0x40000000 ≤ x.toNat) : PvR B x := by
  have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have := F.lo; have := F.hi
  exact sep_of_le (by rw [hb]; omega) (by have := x.isLt; omega)

theorem PvEnv.fr {B : Word} {M M' : Word → BitVec 8} (E : PvEnv M) (F : Fr B 0x21A0)
    (h : ∀ x, PvR B x → M' x = M x) : PvEnv M' :=
  have hb : ∀ x, Sep (B + 0xFFFFFE60) (0x21A0 + 0x1A0) x 1 → PvR B x := fun x hx => by
    have := hx.sub (c := 0) (l := 0x230C) (by decide); rwa [add_ofNat_zero] at this
  ⟨E.C.hi fun x hx => h x (pvR_of_hi F hx), E.D.of F fun x hx => h x (hb x hx),
    E.C2.hi fun x hx => h x (pvR_of_hi F hx), E.D2.of F fun x hx => h x (hb x hx)⟩

theorem PvKeep.trans {B : Word} {M M' M'' : Word → BitVec 8} {c w c' w' : Nat} (h : PvKeep B M M' c w)
    (h' : PvKeep B M' M'' c' w') {e : Nat} (he : e + 1 ≤ 0x1D4C) (h1 : e < c ∨ c + w ≤ e) (h2 : e < c' ∨ c' + w' ≤ e) :
    M'' (B + 0x420 + BitVec.ofNat 32 e) = M (B + 0x420 + BitVec.ofNat 32 e) := by
  rw [h' e he h2, h e he h1]

/-- The limbs of a region a call did not write. -/
theorem PvKeep.acc {B : Word} {M M' : Word → BitVec 8} {c w d k : Nat} (h : PvKeep B M M' c w)
    (hd : d + 4 * k ≤ 0x1D4C) (hs : d + 4 * k ≤ c ∨ c + w ≤ d) :
    accV M' (B + 0x420 + BitVec.ofNat 32 d) k = accV M (B + 0x420 + BitVec.ofNat 32 d) k :=
  accV_S k fun q hq => h _ (by omega) (by omega)

theorem PvPost.trans {B : Word} {m m' m'' : Machine} {off' off'' : Nat} (p : PvPost B m m' off')
    (p' : PvPost B m' m'' off'') : PvPost B m m'' off'' :=
  ⟨p.steps.trans p'.steps, p'.st, fun x hx => by rw [p'.fr x hx, p.fr x hx],
    fun q hq => by rw [p'.regs q hq, p.regs q hq]⟩

theorem pv_lo16 {B : Word} {x : Word} (hx : PvR B x) : Sep (B + 0x420 + 0xFFFFFFF0) 16 x 1 :=
  pvR_lo (k := 16) hx (by decide) (by decide)

set_option maxHeartbeats 4000000 in
/-- A call to `memcpy` of `N` bytes from offset `d` of the frame to offset `c`. -/
theorem pv_mc {B : Word} {m : Machine} {off : Nat} {imm o : Word} {c d N : Nat} (F : Fr B 0x21A0)
    (E : PvEnv m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = MCS) (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 c)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 d) (ha2 : reg m a2 = BitVec.ofNat 32 N)
    (hc : c + N ≤ 0x1D4C) (hd : d + N ≤ 0x1D4C) (hs : c + N ≤ d ∨ d + N ≤ c) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem c N ∧
      ∀ j, j < N → m'.mem (B + 0x420 + BitVec.ofNat 32 (c + j)) = m.mem (B + 0x420 + BitVec.ofNat 32 (d + j)) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hb16 : (B + 0x420 + 0xFFFFFFF0).toNat = (B + 0x420).toNat - 16 := FS.below 16 (by decide) (by decide)
  have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨fA, fW, hFC⟩ := FS.mc
  obtain ⟨n2, c2, u2, fr2, k2⟩ := c_memcpy (dst := B + 0x420 + BitVec.ofNat 32 c)
    (src := B + 0x420 + BitVec.ofNat 32 d) (S := B + 0x420) (N := N) s E.C.self E.C.K h1 h2 hb he8 hsp ha0 ha1 ha2
    ⟨E.C.K.body, FS.sepHi (by omega) (by decide) (by decide), hFC, FS.mcN (by omega), FS.mcN (by omega),
      sepS (B + 0x420) hs (by omega) (by omega), fA, fW, by rw [FS.at _ (by omega)]; omega,
      by rw [FS.at _ (by omega)]; omega⟩
  refine ⟨n2, ⟨c2, u2, fun x hx => ?_, fun q hq => ?_⟩, fun e he1 he2 => ?_, fun j hj => ?_⟩
  · rw [fr2 x (pv_lo16 hx), copyBytes_sep (pvR_hi (c := c) (l := N) hx hc) (Nat.le_refl _)]
  · exact k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  · rw [fr2 _ (FS.lowB hb16 (by decide) (by omega)),
      copyBytes_sep (sepS (B + 0x420) (c := c) (n := N) (d := e) (k := 1) (by omega) (by omega) (by omega))
        (Nat.le_refl _)]
  · rw [fr2 _ (FS.lowB hb16 (by decide) (by omega)), ← add_ofNat_assoc (B + 0x420) c j, cp_at hj (by omega),
      add_ofNat_assoc]

set_option maxHeartbeats 4000000 in
/-- A call to `memcpy` of `N` bytes from the constant at `K` to offset `c` of
the frame. -/
theorem pv_mcK {B K : Word} {m : Machine} {off : Nat} {imm o : Word} {c N : Nat} (F : Fr B 0x21A0)
    (E : PvEnv m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = MCS) (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 c) (ha1 : reg m a1 = K)
    (ha2 : reg m a2 = BitVec.ofNat 32 N) (hc : c + N ≤ 0x1D4C) (hK : 0x3FCC4200 ≤ K.toNat)
    (hK' : K.toNat + N ≤ 0x3FCC4E60) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem c N ∧
      ∀ j, j < N → m'.mem (B + 0x420 + BitVec.ofNat 32 (c + j)) = m.mem (K + BitVec.ofNat 32 j) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hb16 : (B + 0x420 + 0xFFFFFFF0).toNat = (B + 0x420).toNat - 16 := FS.below 16 (by decide) (by decide)
  have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨fA, fW, hFC⟩ := FS.mc
  obtain ⟨n2, c2, u2, fr2, k2⟩ := c_memcpy (dst := B + 0x420 + BitVec.ofNat 32 c)
    (src := K) (S := B + 0x420) (N := N) s E.C.self E.C.K h1 h2 hb he8 hsp ha0 ha1 ha2
    ⟨E.C.K.body, FS.sepHi (by omega) (by decide) (by decide), hFC, FS.mcN (by omega),
      (FS.lowData (c := 16) (by decide) rfl hK hK').symm, FS.bufData (by omega) hK hK', fA, fW,
      by rw [FS.at _ (by omega)]; omega, by omega⟩
  refine ⟨n2, ⟨c2, u2, fun x hx => ?_, fun q hq => ?_⟩, fun e he1 he2 => ?_, fun j hj => ?_⟩
  · rw [fr2 x (pv_lo16 hx), copyBytes_sep (pvR_hi (c := c) (l := N) hx hc) (Nat.le_refl _)]
  · exact k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  · rw [fr2 _ (FS.lowB hb16 (by decide) (by omega)),
      copyBytes_sep (sepS (B + 0x420) (c := c) (n := N) (d := e) (k := 1) (by omega) (by omega) (by omega))
        (Nat.le_refl _)]
  · rw [fr2 _ (FS.lowB hb16 (by decide) (by omega)), ← add_ofNat_assoc (B + 0x420) c j, cp_at hj (by omega)]

theorem pv_S {B : Word} (F : Fr B 0x21A0) : (B + 0x420).toNat = B.toNat + 0x420 := F.at 0x420 (by decide)

theorem pv_below {B : Word} (F : Fr B 0x21A0) {k : Nat} (hk : 0 < k) (hk' : k ≤ 0x5C0) :
    (B + 0x420 + BitVec.ofNat 32 (2 ^ 32 - k)).toNat = B.toNat + 0x420 - k := by
  have := F.lo; have := F.hi
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, show (0x420 : Word).toNat = 0x420 from rfl]; omega

/-- Words below `sp`, apart from a region of the frame. -/
theorem pv_lowS {B : Word} (F : Fr B 0x21A0) {c n k : Nat} (h : c + n ≤ 0x1D80) (hk : 0 < k) (hk' : k ≤ 0x5C0) :
    Sep (B + 0x420 + BitVec.ofNat 32 c) n (B + 0x420 + BitVec.ofNat 32 (2 ^ 32 - k)) k := by
  have := F.lo; have := F.hi
  have e : (B + 0x420 + BitVec.ofNat 32 c).toNat = B.toNat + 0x420 + c := by
    have := F.at (0x420 + c) (by omega); rw [← add_ofNat_assoc] at this; exact this.trans (by omega)
  exact (sep_of_le (a := B + 0x420 + BitVec.ofNat 32 (2 ^ 32 - k)) (n := k) (b := B + 0x420 + BitVec.ofNat 32 c)
    (k := n) (by rw [pv_below F hk hk', e]; omega) (by rw [e]; omega)).symm

/-- Words below `sp`, apart from a constant. -/
theorem pv_lowK {B K : Word} (F : Fr B 0x21A0) {n k : Nat} (hk : k ≤ 0x420) (hK : 0x3FCC4200 ≤ K.toNat)
    (hK' : K.toNat + n ≤ 0x3FCC4E60) : Sep K n (B + 0x420 + BitVec.ofNat 32 (2 ^ 32 - k)) k := by
  have h := F.bufData (c := 0x420 - k) (n := k) (by omega) hK hK'
  rw [show B + BitVec.ofNat 32 (0x420 - k) = B + 0x420 + BitVec.ofNat 32 (2 ^ 32 - k) by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0x420 : Word).toNat = 0x420 from rfl]
    omega] at h
  exact h.symm

/-- A byte of the frame, apart from the `k` bytes below `sp`. -/
theorem pv_lowB {B : Word} (F : Fr B 0x21A0) {k e : Nat} (hk : 0 < k) (hk' : k ≤ 0x5C0) (he : e + 1 ≤ 0x1D80) :
    Sep (B + 0x420 + BitVec.ofNat 32 (2 ^ 32 - k)) k (B + 0x420 + BitVec.ofNat 32 e) 1 :=
  (pv_lowS F he hk hk').symm

set_option maxHeartbeats 8000000 in
/-- A call to `ConstMontyForm<p384::ScalarParams, 12>::new`: the 12 limbs at
offset `cx` of the frame, in Montgomery form, at offset `co`. -/
theorem pv_sn {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cx : Nat} (F : Fr B 0x21A0)
    (E : PvEnv m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 p384ScalarNewAddress)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cx) (hco : co + 48 ≤ 0x1D4C) (hcx : cx + 48 ≤ 0x1D4C)
    (aco : co % 4 = 0) (acx : cx % 4 = 0) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 48 ∧
      accV m'.mem (B + 0x420 + BitVec.ofNat 32 co) 12 =
        accV m.mem (B + 0x420 + BitVec.ofNat 32 cx) 12 * 2 ^ 384 % n384 := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  have hbF : (B + 0x420 + 0xFFFFFF10).toNat = (B + 0x420).toNat - 0xF0 := FS.below 0xF0 (by decide) (by decide)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x420 + 0xFFFFFF10) 0xF0 b l := fun b l hb hl => FS.lowHi (by decide) rfl hb hl
  have EN : N3NEnv n1.mem (BitVec.ofNat 32 p384ScalarNewAddress) (B + 0x420) (B + 0x420 + BitVec.ofNat 32 co)
      (B + 0x420 + BitVec.ofNat 32 cx) := by
    rw [mem1]
    refine ⟨by decide, E.C2.nw, E.D2.nmod, E.D2.r2, ?_⟩
    refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, by omega, by omega, by rw [FS.at _ (by omega)]; omega,
      by rw [FS.at _ (by omega)]; omega, by decide, by decide, by rw [FS.at _ (by omega)]; omega,
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      FS.lowN (k := 0xF0) (by decide) (by decide) (by omega), FS.sepHi (by omega) (by decide) (by decide),
      FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide),
      FS.lowN (k := 0xF0) (by decide) (by decide) (by omega), pv_lowK F (n := 48) (k := 0xF0) (by decide) (by decide) (by decide),
      pv_lowK F (n := 48) (k := 0xF0) (by decide) (by decide) (by decide)⟩
    · rw [show BitVec.ofNat 32 p384ScalarNewAddress + 0xFFFFEE64 = MM by decide]; exact E.C.K.mm
    · rw [show BitVec.ofNat 32 p384ScalarNewAddress + 0xFFFFEE64 + 0x1B0C = MSET by decide]; exact E.C.K.mset
    · rw [show mmBsub (BitVec.ofNat 32 p384ScalarNewAddress + 0xFFFFEE64) = BSUB by decide]; exact E.C.K.bsub
    · rw [show BitVec.ofNat 32 p384ScalarNewAddress + 0xFFFFEE64 + 0x18E = SEL by decide]; exact E.C.K.sel
    · rw [show BitVec.ofNat 32 p384ScalarNewAddress + 0xFFFFEE64 + 0x1B74 = MCS by decide]; exact E.C.K.stub
    · rw [show BitVec.ofNat 32 p384ScalarNewAddress + 0xFFFFEE64 + 0x1B7C = MCS + 8 by decide]; exact E.C.K.body
  obtain ⟨n2, c2, pc2, sp2, k2, val2, fr2⟩ := p384ScalarNew_correct n1 EN pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
    (by rw [r1 sp (by decide)]; exact hsp)
  rw [mem1] at val2 fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0xF0) hx (by decide) (by decide))
      (pvR_hi hx hco), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 0xF0) (by decide) (by decide) (by omega))
      (sepS (B + 0x420) (by omega) (by omega) (by omega)), val2⟩
  by_cases h : q = sp
  · subst h; rw [sp2, hsp]
  · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]

set_option maxHeartbeats 8000000 in
/-- A call to `NonZeroScalar<NistP384>::new`: the 48 bytes at offset `cx`
of the frame, copied to offset `co`, with the choice that they are nonzero
after them. -/
theorem pv_nz {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cx : Nat} (F : Fr B 0x21A0)
    (E : PvEnv m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 nonZero384Address)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cx) (hco : co + 49 ≤ 0x1D4C) (hcx : cx + 48 ≤ 0x1D4C)
    (acx : cx % 4 = 0) (hs : co + 48 ≤ cx ∨ cx + 48 ≤ co) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 49 ∧
      (∀ j, j < 48 → m'.mem (B + 0x420 + BitVec.ofNat 32 (co + j)) = m.mem (B + 0x420 + BitVec.ofNat 32 (cx + j))) ∧
      m'.mem (B + 0x420 + BitVec.ofNat 32 (co + 0x30)) =
        (if ∀ i : Nat, i < 12 → memLoad32 m.mem (B + 0x420 + BitVec.ofNat 32 cx + BitVec.ofNat 32 (4 * i)) = 0
         then 0 else 1) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x420 + 0xFFFFFF9C) 0x64 b l := fun b l hb hl => FS.lowHi (by decide) rfl hb hl
  have EN : NZEnv n1.mem (BitVec.ofNat 32 nonZero384Address) (B + 0x420) (B + 0x420 + BitVec.ofNat 32 co)
      (B + 0x420 + BitVec.ofNat 32 cx) := by
    rw [mem1]
    refine ⟨by decide, E.C2.nz, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, E.D2.zero, by omega, by omega,
      by rw [FS.at _ (by omega)]; omega, by rw [FS.at _ (by omega)]; omega, by rw [FS.at _ (by omega)]; omega,
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      pv_lowK F (n := 48) (k := 0x64) (by decide) (by decide) (by decide),
      FS.lowN (k := 0x64) (by decide) (by decide) (by omega), FS.lowN (k := 0x64) (by decide) (by decide) (by omega),
      FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide),
      sepS (B + 0x420) hs (by omega) (by omega)⟩
    · rw [show BitVec.ofNat 32 nonZero384Address + 0xFFFFFEF6 = BitVec.ofNat 32 montyScalarCtEq384Address by decide]
      exact E.C2.mce
    · rw [show BitVec.ofNat 32 nonZero384Address + 0xFFFFFEF6 + 0xFFFFFAF4 = BitVec.ofNat 32 uint12CtEqAddress by decide]
      exact E.C.K.uce
    · rw [show BitVec.ofNat 32 nonZero384Address + 0xFFFFFEF6 + 0xFFFFFAF4 + 0x80 = BitVec.ofNat 32 splitAt12Address by
        decide]
      exact E.C.K.spl
    · rw [show BitVec.ofNat 32 nonZero384Address + 0xFFFFFEF6 + 0xFFFFFAF4 + 0xFFFF9DBC = BitVec.ofNat 32 limbCtEqAddress
        by decide]
      exact E.C.K.lce
    · rw [show BitVec.ofNat 32 nonZero384Address + 0xFFFFFEF6 + 0xFFFFFAF4 + 0xFFFEF3C4 =
        BitVec.ofNat 32 uintRefIsZeroAddress by decide]
      exact E.C.K.uiz
    · rw [show BitVec.ofNat 32 nonZero384Address + 0xFFFFFEF6 + 0xFFFFFAF4 + 0xFFFEF3C4 + 0x1A =
        BitVec.ofNat 32 uintRefIsNonzeroAddress by decide]
      exact E.C.K.refnz
    · rw [show BitVec.ofNat 32 nonZero384Address + 0xFFFFFEF6 + 0xFFFF99AA = BitVec.ofNat 32 blackBoxU8Address by decide]
      exact E.C.K.bb
    · rw [show BitVec.ofNat 32 nonZero384Address + 0xFFFFDAB2 = BitVec.ofNat 32 choiceNotAddress by decide]
      exact E.C2.cn
    · rw [show BitVec.ofNat 32 nonZero384Address + 0xFFFFDAB2 + 0xFFFFBDEE = BitVec.ofNat 32 blackBoxU8Address by decide]
      exact E.C.K.bb
    · rw [show BitVec.ofNat 32 nonZero384Address + 0x9AA = MCS by decide]; exact E.C.K.stub
    · rw [show BitVec.ofNat 32 nonZero384Address + 0x9AA + 8 = MCS + 8 by decide]; exact E.C.K.body
  obtain ⟨n2, c2, pc2, sp2, cp2, ch2, k2, fr2⟩ := nonZero384_correct n1 EN pc1 (by rw [r1 sp (by decide)]; exact hsp)
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at cp2 ch2 fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0x64) hx (by decide)
      (by decide)) (pvR_hi hx hco), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 0x64) (by decide)
      (by decide) (by omega)) (sepS (B + 0x420) (by omega) (by omega) (by omega)), fun j hj => ?_, ?_⟩
  · by_cases h : q = sp
    · subst h; rw [sp2, hsp]
    · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · rw [← add_ofNat_assoc, cp2 j hj, add_ofNat_assoc]
  · rw [← add_ofNat_assoc]; exact ch2

set_option maxHeartbeats 8000000 in
/-- A call to `CtOption<NonZeroScalar<NistP384>>::unwrap` on a `Some`: the
48 bytes at offset `cs` of the frame, copied to offset `co`. -/
theorem pv_cu {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cs : Nat} (F : Fr B 0x21A0)
    (E : PvEnv m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 ctUnwrap384Address)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cs) (hco : co + 48 ≤ 0x1D4C) (hcs : cs + 49 ≤ 0x1D4C)
    (hs : co + 48 ≤ cs ∨ cs + 48 ≤ co) (hch : m.mem (B + 0x420 + BitVec.ofNat 32 (cs + 0x30)) = 1) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 48 ∧
      ∀ j, j < 48 → m'.mem (B + 0x420 + BitVec.ofNat 32 (co + j)) = m.mem (B + 0x420 + BitVec.ofNat 32 (cs + j)) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  have hb16 : (B + 0x420 + 0xFFFFFFF0).toNat = (B + 0x420).toNat - 16 := FS.below 16 (by decide) (by decide)
  obtain ⟨fA, fW, hFC⟩ := FS.mc
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = B + 0x420 := by rw [r1 sp (by decide)]; exact hsp
  have R := (ctUnwrap384_correct n1 (out := B + 0x420 + BitVec.ofNat 32 co) (s := B + 0x420 + BitVec.ofNat 32 cs)
    (by rw [mem1]; exact E.C.K.panic) (by rw [mem1]; exact E.C2.cu) (by rw [mem1]; exact E.C.K.stub) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8) (by rw [sp1]; exact FS.room (by decide))).1
    (by rw [mem1]; have := hch; rwa [← add_ofNat_assoc] at this)
    (by rw [mem1, sp1]; exact ⟨E.C.K.body, FS.sepHi (by omega) (by decide) (by decide), hFC, FS.mcN (by omega),
      FS.mcN (by omega), sepS (B + 0x420) hs (by omega) (by omega), fA, fW, by rw [FS.at _ (by omega)]; omega,
      by rw [FS.at _ (by omega)]; omega⟩)
  obtain ⟨n2, c2, pc2, sp2, k2, fr2⟩ := R
  rw [sp1, mem1] at fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => ?_, fun q hq => ?_⟩,
    fun e he1 he2 => ?_, fun j hj => ?_⟩
  · rw [fr2 x (pv_lo16 hx), copyBytes_sep (pvR_hi (c := co) (l := 48) hx hco) (Nat.le_refl _)]
  · by_cases h : q = sp
    · subst h; rw [sp2, sp1, hsp]
    · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · rw [fr2 _ (FS.lowB hb16 (by decide) (by omega)),
      copyBytes_sep (sepS (B + 0x420) (c := co) (n := 48) (d := e) (k := 1) (by omega) (by omega) (by omega))
        (Nat.le_refl _)]
  · rw [fr2 _ (FS.lowB hb16 (by decide) (by omega)), ← add_ofNat_assoc (B + 0x420) co j, cp_at hj (by omega),
      add_ofNat_assoc]

/-- A call to `Uint<12>::is_nonzero` on the 12 limbs at offset `cx` of the frame. -/
theorem pv_inz {B : Word} {m : Machine} {off : Nat} {imm o : Word} {cx : Nat} (F : Fr B 0x21A0)
    (E : PvEnv m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 uint12IsNonzeroAddress)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 cx) (hcx : cx + 48 ≤ 0x1D4C)
    (acx : cx % 4 = 0) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem 0 0 ∧
      reg m' a0 = (if ∀ i : Nat, i < 12 →
        memLoad32 m.mem (B + 0x420 + BitVec.ofNat 32 cx + BitVec.ofNat 32 (4 * i)) = 0 then 0 else 1) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = B + 0x420 := by rw [r1 sp (by decide)]; exact hsp
  obtain ⟨n2, c2, pc2, a02, k2, fr2⟩ := uint12IsNonzero_correct n1 (ptr := B + 0x420 + BitVec.ofNat 32 cx) (by decide) (by rw [mem1]; exact E.C2.unz)
    (by rw [mem1, show BitVec.ofNat 32 uint12IsNonzeroAddress + 0xFFFEF156 = BitVec.ofNat 32 uintRefIsNonzeroAddress
      by decide]; exact E.C.K.refnz) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [FS.at _ (by omega)]; omega) (by rw [sp1]; omega)
    (by rw [sp1]; exact FS.lowHi (by decide) rfl (by decide) (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8)
  rw [mem1] at a02 fr2
  rw [sp1] at fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 4) hx (by decide)
      (by decide)), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 4) (by decide) (by decide) (by omega)),
      a02⟩
  rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]

/-- A call to `black_box::<u8>`. -/
theorem pv_bb {B : Word} {m : Machine} {off : Nat} {imm o : Word} (F : Fr B 0x21A0)
    (E : PvEnv m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 blackBoxU8Address)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : reg m sp = B + 0x420) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem 0 0 ∧
      reg m' a0 = ((reg m a0).extractLsb' 0 8).zeroExtend 32 := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  obtain ⟨n2, c2, u2, a02, fr2, k2⟩ := c_bb s E.C.self E.C.K FS h1 h2 hb he8 hsp
  exact ⟨n2, ⟨c2, u2, fun x hx => fr2 x (pvR_lo (k := 1) hx (by decide) (by decide)),
    fun q hq => k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)⟩,
    fun e he1 he2 => fr2 _ (pv_lowB F (k := 1) (by decide) (by decide) (by omega)), a02⟩

set_option maxHeartbeats 8000000 in
/-- A call to the P-384 field `conditional_select`: at offset `co` of the
frame, the 12 limbs at `b` when `c` is 1 and those at `a` when it is 0. -/
theorem pv_csel {B : Word} {m : Machine} {off : Nat} {imm o a b c : Word} {co : Nat} (F : Fr B 0x21A0)
    (E : PvEnv m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = CSEL)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co) (ha1 : reg m a1 = a)
    (ha2 : reg m a2 = b) (ha3 : reg m a3 = c) (hc : c = 0 ∨ c = 1) (hco : co + 48 ≤ 0x1D4C)
    (sA : Sep a 48 (B + 0x420 + 0xFFFFFFA0) 0x60) (sB : Sep b 48 (B + 0x420 + 0xFFFFFFA0) 0x60)
    (hba : b.toNat % 4 = 0) (haw : a.toNat + 48 < 2 ^ 32) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 48 ∧
      accV m'.mem (B + 0x420 + BitVec.ofNat 32 co) 12 = if c = 1 then accV m.mem b 12 else accV m.mem a 12 := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x420 + 0xFFFFFFA0) 0x60 b l := fun b l hb hl => FS.lowHi (by decide) rfl hb hl
  have EN : CSEnv n1.mem CSEL (B + 0x420) (B + 0x420 + BitVec.ofNat 32 co) a b := by
    rw [mem1]
    refine ⟨by decide, E.C.K.csel, ?_, ?_, ?_, ?_, by omega, by omega, hba, haw, by rw [FS.at _ (by omega)]; omega,
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      FS.sepHi (by omega) (by decide) (by decide), FS.sepHi (by omega) (by decide) (by decide),
      FS.lowN (k := 0x60) (by decide) (by decide) (by omega), sA, sB⟩
    · rw [show CSEL + 0x101A = MCS by decide]; exact E.C.K.stub
    · rw [show CSEL + 0x101A + 8 = MCS + 8 by decide]; exact E.C.K.body
    · rw [show CSEL + 0x2EC = BitVec.ofNat 32 uint12CtAssignAddress by decide]; exact E.C.K.cta
    · rw [show CSEL + 0x2EC + 0xFFFF9B66 = BitVec.ofNat 32 sliceCtAssignAddress by decide]; exact E.C.K.sca
  obtain ⟨n2, c2, pc2, sp2, vals, k2, fr2⟩ := condSelect384_correct n1 EN pc1 (by rw [r1 sp (by decide)]; exact hsp)
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3) hc
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at vals fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0x60) hx (by decide)
      (by decide)) (pvR_hi hx hco), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 0x60) (by decide)
      (by decide) (by omega)) (sepS (B + 0x420) (by omega) (by omega) (by omega)), ?_⟩
  · by_cases h : q = sp
    · subst h; rw [sp2, hsp]
    · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · by_cases h : c = 1
    · rw [ite_eq_left h]; exact accV_congr2 12 fun i hi => by rw [vals i hi, ite_eq_left h]
    · rw [ite_eq_right h]; exact accV_congr2 12 fun i hi => by rw [vals i hi, ite_eq_right h]

theorem PvData.lz {M : Word → BitVec 8} (D : PvData M) : lzLimbs M BZO 12 = 0 := by
  rw [lzLimbs, show BZO + BitVec.ofNat 32 (4 * 11) = BZO + BitVec.ofNat 32 (0 + 4 * 11) from rfl,
    code_word D.ord 0 11 (by decide), ite_eq_right (by decide)]
  decide

set_option maxHeartbeats 8000000 in
/-- A call to `bytes2scalar::<NistP384>` on the `n` bytes at `b`, outside the
region: the scalar, in Montgomery form, at offset `co` of the frame. -/
theorem pv_b2s {B : Word} {m : Machine} {off : Nat} {imm o b : Word} {co n : Nat} (F : Fr B 0x21A0)
    (E : PvEnv m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BS)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co) (ha1 : reg m a1 = b)
    (ha2 : reg m a2 = BitVec.ofNat 32 n) (hco : co + 48 ≤ 0x1D4C) (aco : co % 4 = 0) (hbn : b.toNat + n < 2 ^ 32)
    (sb : Sep b n (B + 0xFFFFFE60) 0x230C) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 48 ∧
      accV m'.mem (B + 0x420 + BitVec.ofNat 32 co) 12 = beNat (memBytes m.mem b (min n 48)) * 2 ^ 384 % n384 := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have EB : BZEnv n1.mem := by
    rw [mem1]
    exact ⟨E.C2.bs, E.C2.lz, E.C.K.panic, E.C2.exu, E.C.fb, E.C.K.bsub, E.C.K.bb, E.C2.cn, E.C.K.sca, E.C2.nw,
      E.C.K.mm, E.C.K.sel, E.D2.nmod, E.D2.r2, E.D.n, E.D.lz⟩
  have sG : Sep b n (B + 0x420 + 0xFFFFFE50) 0x1B0 := by
    have := sb.subR (c := 0x5C0 - 0x1B0) (l := 0x1B0) (by decide)
    rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x5C0 - 0x1B0) = B + 0x420 + 0xFFFFFE50 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl] at this
  obtain ⟨n2, c2, pc2, sp2, k2, val2, fr2⟩ := bytes2scalar384_correct n1 (sp0 := B + 0x420)
    (out := B + 0x420 + BitVec.ofNat 32 co) EB pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) (by rw [r1 sp (by decide)]; exact hsp) hFa
    (by have := pv_S F; have := F.lo; omega) (by unfold dramEnd; omega) (by rw [FS.at _ (by omega)]; unfold dramEnd; omega)
    (by rw [FS.at _ (by omega)]; omega) hbn sG (pv_lowS F (k := 0x1B0) (by omega) (by decide) (by decide))
    (pv_lowK F (n := 48) (k := 0x1B0) (by decide) (by decide) (by decide)).symm
    (pv_lowK F (n := 48) (k := 0x1B0) (by decide) (by decide) (by decide)).symm
    (pv_lowK F (n := 48) (k := 0x1B0) (by decide) (by decide) (by decide)).symm
  rw [mem1] at val2 fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0x1B0) hx (by decide)
      (by decide)) (pvR_hi hx hco), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 0x1B0) (by decide)
      (by decide) (by omega)) (sepS (B + 0x420) (by omega) (by omega) (by omega)), val2⟩
  by_cases h : q = sp
  · subst h; rw [sp2, hsp]
  · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]

theorem sep1_ne {a x : Word} (h : Sep a 1 x 1) : x ≠ a := fun e =>
  h 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)

/-- A word store to offset `c` of the frame. -/
theorem pv_sw {B : Word} {m : Machine} {off off' : Nat} {rs1 rs2 : Fin 32} {o len : Word} {c : Nat}
    (F : Fr B 0x21A0) (E : PvEnv m.mem) (s : St m.mem PV m off (reg m))
    (hf : fetchRel p384VerifyPrehashCode off = some (.store .sw rs1 rs2 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (ha : reg m rs1 + o = B + 0x420 + BitVec.ofNat 32 c)
    (hc : c + 4 ≤ 0x1D4C) (ac : c % 4 = 0) :
    ∃ m', Steps m m' ∧ St m'.mem PV m' off' (reg m') ∧ PvEnv m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
      PvKeep B m.mem m'.mem c 4 ∧ memLoad32 m'.mem (B + 0x420 + BitVec.ofNat 32 c) = reg m rs2 ∧
      ∀ q, reg m' q = reg m q := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al
  obtain ⟨m1, d1, u1⟩ := s.sw E.C.self hf hn (by rw [ha, FS.at _ (by omega)]; omega)
  rw [ha] at u1
  have fr : ∀ x, PvR B x → m1.mem x = m.mem x := fun x hx => by
    rw [u1.mem]; exact memStore32_get_sep (pvR_hi hx hc)
  exact ⟨m1, .single d1, ⟨u1.pc, rfl, fun _ => rfl⟩, E.fr F fr, fr,
    fun e he1 he2 => by
      rw [u1.mem]; exact memStore32_get_sep (sepS (B + 0x420) (by omega) (by omega) (by omega)),
    by rw [u1.mem, memLoad32_store32_same], fun q => u1.regs q⟩

/-- A byte store to offset `c` of the frame. -/
theorem pv_sb {B : Word} {m : Machine} {off off' : Nat} {rs1 rs2 : Fin 32} {o len : Word} {c : Nat}
    (F : Fr B 0x21A0) (E : PvEnv m.mem) (s : St m.mem PV m off (reg m))
    (hf : fetchRel p384VerifyPrehashCode off = some (.store .sb rs1 rs2 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (ha : reg m rs1 + o = B + 0x420 + BitVec.ofNat 32 c)
    (hc : c + 1 ≤ 0x1D4C) :
    ∃ m', Steps m m' ∧ St m'.mem PV m' off' (reg m') ∧ PvEnv m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
      PvKeep B m.mem m'.mem c 1 ∧ m'.mem (B + 0x420 + BitVec.ofNat 32 c) = (reg m rs2).extractLsb' 0 8 ∧
      ∀ q, reg m' q = reg m q := by
  obtain ⟨m1, d1, u1⟩ := s.sb E.C.self hf hn
  rw [ha] at u1
  have fr : ∀ x, PvR B x → m1.mem x = m.mem x := fun x hx => by
    rw [u1.mem]; exact memStore8_ne (sep1_ne (pvR_hi (l := 1) hx hc))
  exact ⟨m1, .single d1, ⟨u1.pc, rfl, fun _ => rfl⟩, E.fr F fr, fr,
    fun e he1 he2 => by
      rw [u1.mem]; exact memStore8_ne (sep1_ne (sepS (B + 0x420) (by omega) (by omega) (by omega))),
    by rw [u1.mem, memStore8_same], fun q => u1.regs q⟩

theorem pv_at {B : Word} (F : Fr B 0x21A0) (c : Nat) (hc : c ≤ 0x1D80) :
    (B + 0x420 + BitVec.ofNat 32 c).toNat = B.toNat + 0x420 + c := by
  have := F.at (0x420 + c) (by omega); rw [← add_ofNat_assoc] at this; exact this.trans (by omega)

/-- The limbs a copy from the constant at `K` left at offset `c` of the frame. -/
theorem accV_K {M M' : Word → BitVec 8} {S K : Word} {c : Nat} :
    ∀ k, (∀ q, q < 4 * k → M' (S + BitVec.ofNat 32 (c + q)) = M (K + BitVec.ofNat 32 q)) →
    accV M' (S + BitVec.ofNat 32 c) k = accV M (K + BitVec.ofNat 32 0) k :=
  fun k h => accV_congr2 k fun i hi => by
    rw [ld_ofNat, ld_ofNat]
    simp only [add_ofNat_assoc, Nat.add_assoc, Nat.zero_add]
    rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

set_option exponentiation.threshold 800 in
/-- A nonzero scalar below the order stays nonzero in Montgomery form. -/
theorem n3_mont_ne {R : Nat} (h0 : R ≠ 0) (hR : R < n384) : R * 2 ^ 384 % n384 ≠ 0 := by
  intro h
  have hinv : (2 ^ 384 * n3RInv) % n384 = 1 := by unfold n384 n3RInv; decide
  have e : R * 2 ^ 384 % n384 * n3RInv % n384 = R := by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, hinv, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hR]
  rw [h, Nat.zero_mul, Nat.zero_mod] at e
  exact h0 e.symm

end C3.RV32.Pv
