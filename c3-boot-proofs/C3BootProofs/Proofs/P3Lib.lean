import C3BootProofs.Proofs.Dec384End
import C3BootProofs.Proofs.TagAndThen
import C3BootProofs.Proofs.Sec1Tag
import C3BootProofs.Proofs.EncodedPoint
import C3BootProofs.Proofs.CtEq
import C3BootProofs.Proofs.CtInto
import C3BootProofs.Image.BootloaderData2

/-!
# Calls to the P-384 field and SEC1 functions, from any caller

Each `c_` theorem steps over one call, from a caller whose code is `code` at
`base`, with its frame `Fr S N`: `N` bytes at `S` in DRAM and 0x1A0 bytes
below for the callee, apart from the constants at `dataWindowAddress`.
-/

namespace C3.RV32.P3

open C3.Image C3.RV32.Dq

set_option maxRecDepth 20000

/-- A caller's frame: `N` bytes at `S`, with 0x1A0 bytes below for callees,
in DRAM and apart from the constants. -/
structure Fr (S : Word) (N : Nat) : Prop where
  al : S.toNat % 16 = 0
  lo : 0x3FC801A0 ≤ S.toNat
  hi : S.toNat + N ≤ 0x3FCE0000
  dsep : Sep (S + 0xFFFFFE60) (N + 0x1A0) (img% dataWindowAddress : Word) (img% dataWindowSize)

theorem Fr.at {S : Word} {N : Nat} (F : Fr S N) (c : Nat) (hc : c ≤ N) : (S + BitVec.ofNat 32 c).toNat = S.toNat + c := by
  have := F.hi; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem Fr.below {S : Word} {N : Nat} (F : Fr S N) (c : Nat) (hc : 0 < c) (hc' : c ≤ 0x1A0) :
    (S + BitVec.ofNat 32 (2 ^ 32 - c)).toNat = S.toNat - c := by
  have := F.lo; have := S.isLt; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem Fr.sepHi {S : Word} {N : Nat} (F : Fr S N) {c n : Nat} (h : c + n ≤ N) {b : Word} {len : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + len ≤ 2 ^ 32) : Sep (S + BitVec.ofNat 32 c) n b len :=
  sep_of_le (by rw [F.at c (by omega)]; have := F.hi; omega) hl

theorem Fr.hiOut {S : Word} {N : Nat} (F : Fr S N) {c n : Nat} (h : c + n ≤ N) {x : Word} (hx : 0x40000000 ≤ x.toNat) :
    Sep (S + BitVec.ofNat 32 c) n x 1 := F.sepHi h hx (by have := x.isLt; omega)

theorem Fr.lowData {S : Word} {N : Nat} (F : Fr S N) {k : Word} {c : Nat} (hc : c ≤ 0x1A0)
    (hk : (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 - c) = k) {b : Word} {len : Nat}
    (hb : (img% dataWindowAddress) ≤ b.toNat) (hb2 : b.toNat + len ≤ (img% dataWindowAddress + dataWindowSize)) : Sep (S + k) c b len := by
  have h1 := F.dsep.sub (c := 0x1A0 - c) (l := c) (by omega)
  have h2 := h1.subR (c := b.toNat - (img% dataWindowAddress)) (l := len) (by omega)
  rw [BitVec.add_assoc, hk] at h2
  rwa [show (img% dataWindowAddress : Word) + BitVec.ofNat 32 (b.toNat - (img% dataWindowAddress)) = b by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (img% dataWindowAddress : Word).toNat = (img% dataWindowAddress) from rfl]
    have := b.isLt; omega] at h2

theorem Fr.bufData {S : Word} {N : Nat} (F : Fr S N) {c n : Nat} (h : c + n ≤ N) {b : Word} {len : Nat}
    (hb : (img% dataWindowAddress) ≤ b.toNat) (hb2 : b.toNat + len ≤ (img% dataWindowAddress + dataWindowSize)) : Sep (S + BitVec.ofNat 32 c) n b len := by
  have h1 := F.dsep.sub (c := 0x1A0 + c) (l := n) (by omega)
  have h2 := h1.subR (c := b.toNat - (img% dataWindowAddress)) (l := len) (by omega)
  rw [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
    omega] at h2
  rwa [show (img% dataWindowAddress : Word) + BitVec.ofNat 32 (b.toNat - (img% dataWindowAddress)) = b by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (img% dataWindowAddress : Word).toNat = (img% dataWindowAddress) from rfl]
    have := b.isLt; omega] at h2

theorem Fr.lowHi {S : Word} {N : Nat} (F : Fr S N) {k : Word} {c : Nat} (hc : c ≤ 0x1A0) (hk : k.toNat = 2 ^ 32 - c)
    {b : Word} {len : Nat} (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + len ≤ 2 ^ 32) : Sep (S + k) c b len :=
  sep_of_le (by rw [BitVec.toNat_add, hk]; have := F.lo; have := F.hi; have := S.isLt; omega) hl

theorem Fr.mc {S : Word} {N : Nat} (F : Fr S N) :
    (S + 0xFFFFFFF0).toNat % 4 = 0 ∧ (S + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 ∧
      Sep (S + 0xFFFFFFF0) 16 (MCS + 8) memcpyBodyCode.length := by
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have := F.lo; have := F.hi; have := F.al
  exact ⟨by rw [hb16]; omega, by rw [hb16]; omega,
    sep_of_le (by rw [hb16, show (MCS + 8).toNat = (img% memcpyBodyAddress) from rfl]; omega) (by decide)⟩

theorem Fr.mcN {S : Word} {N : Nat} (F : Fr S N) {c n : Nat} (h : c + n ≤ N) :
    Sep (S + BitVec.ofNat 32 c) n (S + 0xFFFFFFF0) 16 := by
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have := F.lo; have := F.hi
  exact (sep_of_le (by rw [hb16, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm

theorem Fr.lowB {S : Word} {N : Nat} (F : Fr S N) {B : Word} {k : Nat} (hB : B.toNat = S.toNat - k) (hk : k ≤ 0x1A0)
    {d : Nat} (hd : d + 1 ≤ N) : Sep B k (S + BitVec.ofNat 32 d) 1 :=
  sep_of_le (by have := F.lo; rw [hB, F.at d (by omega)]; omega) (by have := F.hi; rw [F.at d (by omega)]; omega)

theorem panic_lo : ∀ p ∈ panicFns, 0x40000000 ≤ p.1 := by decide

theorem panic_hi {M M' : Word → BitVec 8} (h : PanicCode M) (hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    PanicCode M' := by
  intro p hp
  have h1 := panic_lo p hp
  have h2 := (panicFns_hi p hp).2
  have e : (BitVec.ofNat 32 p.1).toNat = p.1 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact (h p hp).hi hx (by rw [e]; exact h1) (by rw [e]; omega)

/-- The P-384 and SEC1 functions a caller calls, and theirs, at their addresses in the image. -/
structure P3Code (M : Word → BitVec 8) : Prop where
  stub : CodeIn M MCS memcpyStubCode
  body : CodeIn M (MCS + 8) memcpyBodyCode
  mset : CodeIn M MSET memsetCode
  bsub : CodeIn M BSUB borrowingSubCode
  sel : CodeIn M SEL uintSelect12Code
  mm : CodeIn M MM mulMont12Code
  p3mul : CodeIn M (BitVec.ofNat 32 p384MulAddress) p384MulCode
  p3add : CodeIn M (BitVec.ofNat 32 p384AddAddress) p384AddCode
  csel : CodeIn M (BitVec.ofNat 32 condSelect384Address) condSelect384Code
  cta : CodeIn M (BitVec.ofNat 32 uint12CtAssignAddress) uint12CtAssignCode
  sca : CodeIn M (BitVec.ofNat 32 sliceCtAssignAddress) sliceCtAssignCode
  bb : CodeIn M (BitVec.ofNat 32 blackBoxU8Address) blackBoxU8Code
  frp : CodeIn M (BitVec.ofNat 32 p384FromReprAddress) p384FromReprCode
  za : CodeIn M (BitVec.ofNat 32 zeroArray48Address) zeroArray48Code
  refnz : CodeIn M (BitVec.ofNat 32 uintRefIsNonzeroAddress) uintRefIsNonzeroCode
  uce : CodeIn M (BitVec.ofNat 32 uint12CtEqAddress) uint12CtEqCode
  spl : CodeIn M (BitVec.ofNat 32 splitAt12Address) splitAt12Code
  lce : CodeIn M (BitVec.ofNat 32 limbCtEqAddress) limbCtEqCode
  uiz : CodeIn M (BitVec.ofNat 32 uintRefIsZeroAddress) uintRefIsZeroCode
  tat : CodeIn M (BitVec.ofNat 32 tagAndThenAddress) tagAndThenCode
  tfu : CodeIn M (BitVec.ofNat 32 tagFromU8Address) tagFromU8Code
  tml : CodeIn M (BitVec.ofNat 32 tagMessageLenAddress) tagMessageLenCode
  isid : CodeIn M (BitVec.ofNat 32 encodedPointIsIdentityAddress) encodedPointIsIdentityCode
  tag : CodeIn M (BitVec.ofNat 32 encodedPointTagAddress) encodedPointTagCode
  ext : CodeIn M (BitVec.ofNat 32 expectTagAddress) expectTagCode
  into : CodeIn M (BitVec.ofNat 32 ctIntoAffine384Address) ctIntoAffine384Code
  uor : CodeIn M (BitVec.ofNat 32 unwrapOr384Address) unwrapOr384Code
  panic : PanicCode M

theorem P3Code.hi {M M' : Word → BitVec 8} (K : P3Code M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    P3Code M' :=
  ⟨codeHi K.stub (by decide) (by decide) h, codeHi K.body (by decide) (by decide) h,
    codeHi K.mset (by decide) (by decide) h, codeHi K.bsub (by decide) (by decide) h,
    codeHi K.sel (by decide) (by decide) h, codeHi K.mm (by decide) (by decide) h,
    codeHi K.p3mul (by decide) (by decide) h, codeHi K.p3add (by decide) (by decide) h,
    codeHi K.csel (by decide) (by decide) h, codeHi K.cta (by decide) (by decide) h,
    codeHi K.sca (by decide) (by decide) h, codeHi K.bb (by decide) (by decide) h,
    codeHi K.frp (by decide) (by decide) h, codeHi K.za (by decide) (by decide) h,
    codeHi K.refnz (by decide) (by decide) h, codeHi K.uce (by decide) (by decide) h,
    codeHi K.spl (by decide) (by decide) h, codeHi K.lce (by decide) (by decide) h,
    codeHi K.uiz (by decide) (by decide) h, codeHi K.tat (by decide) (by decide) h,
    codeHi K.tfu (by decide) (by decide) h, codeHi K.tml (by decide) (by decide) h,
    codeHi K.isid (by decide) (by decide) h, codeHi K.tag (by decide) (by decide) h,
    codeHi K.ext (by decide) (by decide) h, codeHi K.into (by decide) (by decide) h,
    codeHi K.uor (by decide) (by decide) h, panic_hi K.panic h⟩

/-- The P-384 constants: the field parameters, `a`, and `b`. -/
structure P3Data (M : Word → BitVec 8) : Prop where
  params : CodeIn M PARAMS p384ParamsData
  ca : CodeIn M CURVEA p384CurveAData
  cb : CodeIn M p3bA p384BData

theorem P3Data.of {M M' : Word → BitVec 8} {S : Word} {N : Nat} (F : Fr S N) (D : P3Data M)
    (h : ∀ x, Sep (S + 0xFFFFFE60) (N + 0x1A0) x 1 → M' x = M x) : P3Data M' := by
  have hd := F.dsep
  have cd : ∀ (b : Word) (d : List Nat), CodeIn M b d → (img% dataWindowAddress) ≤ b.toNat → b.toNat + d.length ≤ (img% dataWindowAddress + dataWindowSize) →
      CodeIn M' b d := fun b d hc h1 h2 i hi => by
    rw [h _ (hd.subR (c := (b + BitVec.ofNat 32 i).toNat - (img% dataWindowAddress)) (l := 1) (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) |> fun s => by
        rwa [show (img% dataWindowAddress : Word) + BitVec.ofNat 32 ((b + BitVec.ofNat 32 i).toNat - (img% dataWindowAddress)) =
          b + BitVec.ofNat 32 i from by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat,
              show (img% dataWindowAddress : Word).toNat = (img% dataWindowAddress) from rfl]
            omega] at s)]
    exact hc i hi
  exact ⟨cd _ _ D.params (by decide) (by decide), cd _ _ D.ca (by decide) (by decide),
    cd _ _ D.cb (by decide) (by decide)⟩

theorem P3Data.pmod {M : Word → BitVec 8} (D : P3Data M) : CodeIn M p3M p384ModulusData := fun i hi => by
  have hb : ∀ i, i < 48 → byteAt p384ParamsData i = byteAt p384ModulusData i := by decide
  rw [show p3M = PARAMS from rfl, D.params i (by have : p384ModulusData.length = 48 := rfl; have : p384ParamsData.length = 156 := rfl; omega),
    hb i (by have : p384ModulusData.length = 48 := rfl; omega)]

theorem P3Data.N {M : Word → BitVec 8} (D : P3Data M) : accV M PARAMS 12 = p384 := by
  rw [show PARAMS = PARAMS + BitVec.ofNat 32 0 from (add_ofNat_zero _).symm, code_accV D.params 0 12 (by decide), params_N]

theorem P3Data.N0 {M : Word → BitVec 8} (D : P3Data M) : memLoad32 M PARAMS = 0xFFFFFFFF := by
  rw [show PARAMS = PARAMS + BitVec.ofNat 32 (0 + 4 * 0) from (add_ofNat_zero _).symm, code_word D.params 0 0 (by decide),
    params_n0]

theorem P3Data.r2lt {M : Word → BitVec 8} (D : P3Data M) : accV M (PARAMS + BitVec.ofNat 32 0x60) 12 < accV M PARAMS 12 := by
  rw [code_accV D.params 0x60 12 (by decide), D.N]; exact params_r2

/-- A call to `memcpy` from a caller, with `sp` at `S`. -/
theorem c_memcpy {base : Word} {code : List Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o dst src S : Word}
    {N : Nat} (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P3Code Mx)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = MCS) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = dst) (ha1 : g a1 = src) (ha2 : g a2 = BitVec.ofNat 32 N)
    (E : McEnv Mx (MCS + 8) dst src (S + 0xFFFFFFF0) N) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → n'.mem x = copyBytes Mx dst src N x) ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
        r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ ra → reg n' r = g r := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, pc2, sp2, a02, mem2, k2⟩ := memcpy_correct n1 MCS (base + BitVec.ofNat 32 (off + 8)) dst src N
    (fun i hi => by rw [mem1]; exact K.stub i hi) (by decide) pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) (by rw [mem1, r1 sp (by decide), hsp]; exact E)
  rw [r1 sp (by decide), hsp, mem1] at mem2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, mem2,
    fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hra => ?_⟩
  by_cases hs : r = sp
  · subst hs; rw [sp2, r1 sp (by decide)]
  · rw [k2 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hs, r1 r hra]

/-- A call to `memset` from a caller. -/
theorem c_memset {base : Word} {code : List Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o dst b : Word}
    {N : Nat} (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P3Code Mx)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = MSET) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : g a0 = dst) (ha1 : g a1 = b) (ha2 : g a2 = BitVec.ofNat 32 N)
    (hw : dst.toNat + N < 2 ^ 32) (hDC : Sep dst N MSET memsetCode.length) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧ n'.mem = fillBytes Mx dst (b.extractLsb' 0 8) N ∧
      ∀ r, r ≠ a0 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ ra → reg n' r = g r := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, pc2, mem2, a02, k2⟩ := memset_correct n1 MSET (base + BitVec.ofNat 32 (off + 8)) dst b N
    (fun i hi => by rw [mem1]; exact K.mset i hi) (by decide) pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) hw hDC
  rw [mem1] at mem2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, mem2,
    fun r h0 h2 h3 h4 h5 h6 hra => by rw [k2 r h2 h3 h4 h5 h6, r1 r hra]⟩

set_option maxRecDepth 100000 in
/-- A call to `ConstMontyForm<p384::FieldParams>::mul` from a caller: the
12 words at `out` become the Montgomery product of those at `xp` and `yp`. -/
theorem c_p3mul {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o out xp yp S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P3Code Mx) (D : P3Data Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = P3MUL) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = xp) (ha2 : g a2 = yp)
    {co : Nat} (hco : co + 48 ≤ N) (eo : out = S + BitVec.ofNat 32 co) (aco : co % 4 = 0)
    (sX : Sep xp 48 (S + 0xFFFFFF10) 0xF0) (aX : xp.toNat % 4 = 0)
    (sY : Sep yp 48 (S + 0xFFFFFF10) 0xF0) (aY : yp.toNat % 4 = 0)
    (hY : limbVal (wordsAt Mx yp 12) < p384) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      limbVal (wordsAt n'.mem out 12) = p3fm (limbVal (wordsAt Mx xp 12)) (limbVal (wordsAt Mx yp 12)) ∧
      (∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 → Sep out 48 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFF10).toNat = S.toNat - 0xF0 := F.below 0xF0 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFF10) 0xF0 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have E : P3MEnv n1.mem P3MUL (reg n1 sp) out xp yp := by
    rw [sp1, mem1]
    refine ⟨by decide, K.p3mul, D.pmod, ?_⟩
    rw [p3mul_mm]
    refine ⟨by decide, K.mm, by rw [mm_mset]; exact K.mset, by rw [mm_bsub]; exact K.bsub, by rw [mm_sel]; exact K.sel,
      by rw [mm_stub]; exact K.stub, by rw [mm_body]; exact K.body, by omega, by omega, ?_, aX, aY, by decide, ?_,
      frC _ _ (by decide) (by decide), frC _ _ (by rw [mm_mset]; decide) (by rw [mm_mset]; decide),
      frC _ _ (by rw [mm_bsub]; decide) (by rw [mm_bsub]; decide), frC _ _ (by rw [mm_sel]; decide) (by rw [mm_sel]; decide),
      frC _ _ (by rw [mm_stub]; decide) (by rw [mm_stub]; decide), frC _ _ (by rw [mm_body]; decide)
        (by rw [mm_body]; decide), ?_, ?_, ?_, ?_, sX, sY, (F.lowData (c := 0xF0) (by decide) rfl (by decide) (by decide)).symm⟩
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo]; exact (sep_of_le (by rw [hbF, F.at co (by omega)]; omega) (by rw [F.at co (by omega)]; omega)).symm
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, mm_sel]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, mm_body]; exact F.sepHi hco (by decide) (by decide)
  obtain ⟨n2, c2, pc2, sp2, k2, hv2, fr2⟩ := p384Mul_correct n1 E pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8) rfl (by rw [mem1]; exact hY)
  rw [mem1] at hv2 fr2
  rw [sp1] at fr2 sp2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, hv2, fr2, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]⟩

/-- A call to `ConstMontyForm<p384::FieldParams>::add` from a caller. -/
theorem c_p3add {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o out lp rp S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P3Code Mx) (D : P3Data Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = P3ADD) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = lp) (ha2 : g a2 = rp)
    {co : Nat} (hco : co + 48 ≤ N) (eo : out = S + BitVec.ofNat 32 co) (aco : co % 4 = 0)
    (sL : Sep lp 48 (S + 0xFFFFFF4C) 0xB4) (aL : lp.toNat % 4 = 0)
    (sR : Sep rp 48 (S + 0xFFFFFF4C) 0xB4) (aR : rp.toNat % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      limbVal (wordsAt n'.mem out 12) = p3AddRes (limbVal (wordsAt Mx lp 12)) (limbVal (wordsAt Mx rp 12)) ∧
      (∀ x, Sep (S + 0xFFFFFF4C) 0xB4 x 1 → Sep out 48 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 → q ≠ ra →
        reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFF4C).toNat = S.toNat - 0xB4 := F.below 0xB4 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFF4C) 0xB4 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have E : P3Env n1.mem P3ADD (reg n1 sp) out lp rp := by
    rw [sp1, mem1]
    refine ⟨by decide, K.p3add, by rw [p3add_mset]; exact K.mset, by rw [p3add_bsub]; exact K.bsub,
      by rw [p3add_stub]; exact K.stub, by rw [p3add_body]; exact K.body, D.pmod, by omega, by omega, ?_, aL, aR, ?_,
      frC _ _ (by decide) (by decide), frC _ _ (by rw [p3add_mset]; decide) (by rw [p3add_mset]; decide),
      frC _ _ (by rw [p3add_bsub]; decide) (by rw [p3add_bsub]; decide),
      frC _ _ (by rw [p3add_stub]; decide) (by rw [p3add_stub]; decide),
      frC _ _ (by rw [p3add_body]; decide) (by rw [p3add_body]; decide),
      F.lowData (c := 0xB4) (by decide) rfl (by decide) (by decide), ?_, ?_, ?_, sL, sR⟩
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, p3add_body]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo]; exact (sep_of_le (by rw [hbF, F.at co (by omega)]; omega) (by rw [F.at co (by omega)]; omega)).symm
  obtain ⟨n2, c2, pc2, sp2, k2, hv2, fr2⟩ := p384Add_correct n1 E pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8) rfl
  rw [mem1] at hv2 fr2
  rw [sp1] at fr2 sp2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, hv2, fr2, sp2,
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hr => by rw [k2 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9, r1 q hr]⟩

/-- A call to `ConstMontyForm<p384::FieldParams>::conditional_select` from
the caller, with all three operands in its frame. -/
theorem c_csel {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o out a b c S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P3Code Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = CSEL) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = a) (ha2 : g a2 = b) (ha3 : g a3 = c) (hc : c = 0 ∨ c = 1)
    {co ca cb : Nat} (hco : co + 48 ≤ N) (hca : ca + 48 ≤ N) (hcb : cb + 48 ≤ N)
    (eo : out = S + BitVec.ofNat 32 co) (ea : a = S + BitVec.ofNat 32 ca) (eb : b = S + BitVec.ofNat 32 cb)
    (acb : cb % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      (∀ i, i < 12 → memLoad32 n'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 Mx (b + BitVec.ofNat 32 (4 * i)) else memLoad32 Mx (a + BitVec.ofNat 32 (4 * i))) ∧
      (∀ x, Sep (S + 0xFFFFFFA0) 0x60 x 1 → Sep out 48 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFFA0).toNat = S.toNat - 0x60 := F.below 0x60 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFFA0) 0x60 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have frS : ∀ cz, cz + 48 ≤ N → Sep (S + BitVec.ofNat 32 cz) 48 (S + 0xFFFFFFA0) 0x60 := fun cz h =>
    (sep_of_le (by rw [hbF, F.at cz (by omega)]; omega) (by rw [F.at cz (by omega)]; omega)).symm
  have E : CSEnv n1.mem CSEL (reg n1 sp) out a b := by
    rw [sp1, mem1]
    refine ⟨by decide, K.csel, by rw [csel_stub]; exact K.stub, by rw [csel_body]; exact K.body,
      by rw [csel_cta]; exact K.cta, by rw [csel_sca]; exact K.sca, by omega, by omega, ?_, ?_, ?_,
      frC _ _ (by decide) (by decide), frC _ _ (by rw [csel_stub]; decide) (by rw [csel_stub]; decide),
      frC _ _ (by rw [csel_body]; decide) (by rw [csel_body]; decide),
      frC _ _ (by rw [csel_cta]; decide) (by rw [csel_cta]; decide),
      frC _ _ (by rw [csel_sca]; decide) (by rw [csel_sca]; decide), ?_, ?_, ?_, ?_, ?_⟩
    · rw [eb, F.at cb (by omega)]; omega
    · rw [ea, F.at ca (by omega)]; omega
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, csel_body]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo]; exact frS co hco
    · rw [ea]; exact frS ca hca
    · rw [eb]; exact frS cb hcb
  obtain ⟨n2, c2, pc2, sp2, vals, k2, fr2⟩ := condSelect384_correct n1 E pc1 rfl (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3)
    hc (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at vals fr2
  rw [sp1] at fr2 sp2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, vals, fr2, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]⟩

/-- A call to `black_box::<u8>` from a caller. -/
theorem c_bb {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P3Code Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 blackBoxU8Address)
    (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : g sp = S) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      reg n' a0 = ((g a0).extractLsb' 0 8).zeroExtend 32 ∧
      (∀ x, Sep (S + 0xFFFFFFFF) 1 x 1 → n'.mem x = Mx x) ∧ ∀ q, q ≠ a0 → q ≠ ra → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hb1 : (S + 0xFFFFFFFF).toNat = S.toNat - 1 := F.below 1 (by decide) (by decide)
  have hSl := F.lo; have hSh := F.hi
  obtain ⟨n2, c2, pc2, a02, k2, fr2⟩ := blackBoxU8_correct n1 (by rw [mem1]; exact K.bb) pc1
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
    (by rw [sp1]; exact F.lowHi (by decide) rfl (by decide) (by decide))
  rw [mem1] at fr2
  rw [sp1] at fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [a02, r1 a0 (by decide)], fr2,
    fun q h0 hr => by rw [k2 q h0, r1 q hr]⟩

/-- A call to `<p384::FieldElement as PrimeField>::from_repr` from
the caller, with the result at `S + co` and the 48 input bytes at `inp`. -/
theorem c_frp {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o out inp S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P3Code Mx) (D : P3Data Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = FRP) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = inp)
    {co : Nat} (hco : co + 49 ≤ N) (eo : out = S + BitVec.ofNat 32 co)
    (sI : Sep inp 48 (S + 0xFFFFFE60) 0x1A0) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      (beNat (memBytes Mx inp 48) < p384 →
        n'.mem (out + 0x30) = 1 ∧ accV n'.mem out 12 < p384 ∧
        accV n'.mem out 12 * 2 ^ 384 % p384 = beNat (memBytes Mx inp 48) * accV Mx (PARAMS + BitVec.ofNat 32 0x60) 12 % p384) ∧
      (p384 ≤ beNat (memBytes Mx inp 48) → n'.mem (out + 0x30) = 0 ∧ accV n'.mem out 12 = 0) ∧
      (∀ x, Sep (S + 0xFFFFFE60) 0x1A0 x 1 → Sep out 49 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have E : FRPEnv n1.mem := by
    rw [mem1]
    exact ⟨K.frp, K.za, K.mset, K.stub, K.body, K.bsub, K.refnz, K.mm, K.sel, K.bb, K.csel, K.cta, K.sca, D.N0,
      by rw [show p384Np = PARAMS from rfl]; exact D.r2lt⟩
  obtain ⟨n2, c2, pc2, sp2, k2, ok, bad, fr2⟩ := p384FromRepr_correct (out := out) (inp := inp) n1 E pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) sp1 hSa (by omega)
    (by omega) (by rw [eo, F.at co (by omega)]; omega)
    (by rw [eo]; exact (sep_of_le (by rw [hbF, F.at co (by omega)]; omega) (by rw [F.at co (by omega)]; omega)).symm) sI
    (F.lowData (c := 0x1A0) (by decide) rfl (by decide) (by decide))
  rw [mem1, show p384Np = PARAMS from rfl, D.N] at ok bad
  rw [mem1] at fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, ok, bad, fr2, sp2,
    fun q hq => by rw [k2 q hq, r1 q (by revert hq; revert q; decide)]⟩

abbrev UCE : Word := BitVec.ofNat 32 uint12CtEqAddress
theorem uce_spl : UCE + 0x80 = BitVec.ofNat 32 splitAt12Address := by decide
theorem uce_lce : UCE + 0xFFFF9DBC = BitVec.ofNat 32 limbCtEqAddress := by decide
theorem uce_uiz : UCE + 0xFFFEF3C4 = BitVec.ofNat 32 uintRefIsZeroAddress := by decide
theorem uce_unz : UCE + 0xFFFEF3C4 + 0x1A = BitVec.ofNat 32 uintRefIsNonzeroAddress := by decide

/-- A call to `Uint<12>::ct_eq`: `a0` is 1 when the 12 words at `pa` and `pb` are equal, else 0. -/
theorem c_uce {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o pa pb S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P3Code Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = UCE) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = pa) (ha1 : g a1 = pb) (hpa : pa.toNat % 4 = 0) (hpb : pb.toNat % 4 = 0)
    (sA : Sep pa 48 (S + 0xFFFFFFBC) 0x44) (sB : Sep pb 48 (S + 0xFFFFFFBC) 0x44) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      reg n' a0 = (if ∀ i : Nat, i < 12 → memLoad32 Mx (pa + BitVec.ofNat 32 (4 * i)) =
        memLoad32 Mx (pb + BitVec.ofNat 32 (4 * i)) then 1 else 0) ∧
      (∀ x, Sep (S + 0xFFFFFFBC) 0x44 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, oidKeep q = true → q ≠ ra → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFFBC).toNat = S.toNat - 0x44 := F.below 0x44 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFFBC) 0x44 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have E : UCEEnv n1.mem UCE S pa pb := by
    rw [mem1]
    exact ⟨by decide, K.uce, by rw [uce_spl]; exact K.spl, by rw [uce_lce]; exact K.lce, by rw [uce_uiz]; exact K.uiz,
      by rw [uce_unz]; exact K.refnz, by omega, by omega, hpa, hpb, frC _ _ (by decide) (by decide),
      frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide),
      frC _ _ (by decide) (by decide), sA, sB⟩
  obtain ⟨n2, c2, pc2, sp2, a02, k2, fr2⟩ := uint12CtEq_correct n1 E pc1 sp1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at a02 fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, a02, fr2, sp2, fun q hq hr => by rw [k2 q hq, r1 q hr]⟩

/-- A call to `Tag::message_len`. -/
theorem c_tml {base : Word} {code : List Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o t fe : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P3Code Mx)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 tagMessageLenAddress)
    (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (ha0 : g a0 = t) (ha1 : g a1 = fe) :
    ∃ n', Steps n n' ∧ St Mx base n' (off + 8) (reg n') ∧ reg n' a0 = tagMsgLen t fe ∧
      ∀ r, r ≠ a0 → r ≠ a2 → r ≠ a3 → r ≠ ra → reg n' r = g r := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, pc2, a02, mem2, k2⟩ := tagMessageLen_correct (t := t) (fe := fe) n1 (by decide) (by rw [mem1]; exact K.tml) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8)
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], by rw [mem2, mem1], fun _ => rfl⟩, a02,
    fun r h0 h2 h3 hr => by rw [k2 r h0 h2 h3, r1 r hr]⟩

abbrev TAT : Word := BitVec.ofNat 32 tagAndThenAddress
theorem tat_tfu : TAT + 0x3E = BitVec.ofNat 32 tagFromU8Address := by decide
theorem tat_stub : TAT + 0x119B4 = MCS := by decide

/-- A call to `Result<u8, Error>::and_then(Tag::from_u8)` on an `Ok`. -/
theorem c_tat {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o out rp S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P3Code Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = TAT) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = rp) {co cr : Nat} (hco : co + 0x34 ≤ N) (hcr : cr + 0x34 ≤ N)
    (eo : out = S + BitVec.ofNat 32 co) (er : rp = S + BitVec.ofNat 32 cr) (aco : co % 4 = 0) (acr : cr % 4 = 0)
    (hd : co + 0x34 ≤ cr ∨ cr + 0x34 ≤ co) (hok : memLoad32 Mx rp = 0xFFFFFFFF) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      n'.mem = tagFromU8Mem Mx out ((Mx (rp + 4)).zeroExtend 32) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  obtain ⟨fA, fW, hFC⟩ := F.mc
  have E : McEnv n1.mem (TAT + 0x119B4 + 8) out rp (reg n1 sp + 0xFFFFFFF0) 0x34 := by
    rw [sp1, mem1, tat_stub, eo, er]
    exact ⟨K.body, F.sepHi hco (by decide) (by decide), hFC, F.mcN hco, F.mcN hcr, sepS S hd (by omega) (by omega),
      fA, fW, by rw [F.at _ (by omega)]; omega, by rw [F.at _ (by omega)]; omega⟩
  obtain ⟨n2, c2, pc2, sp2, k2, res⟩ := tagAndThen_correct n1 (by decide) (by rw [mem1]; exact K.tat)
    (by rw [mem1, tat_tfu]; exact K.tfu) (by rw [mem1, tat_stub]; exact K.stub) E pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [eo, F.at _ (by omega)]; omega) (by rw [er, F.at _ (by omega)]; omega)
    (by rw [eo, tat_tfu]; exact F.sepHi (by omega) (by decide) (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8)
  rw [mem1, ite_eq_left hok] at res
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, res, by rw [sp2, sp1],
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]⟩

theorem Fr.room {S : Word} {N : Nat} (F : Fr S N) {k : Nat} (hk : k ≤ 0x1A0) : Room S k := by
  have := F.al; have := F.lo; have := F.hi
  exact ⟨by omega, by omega, show S.toNat ≤ 0x3FCE0000 by omega⟩

/-- A call to `EncodedPoint::is_identity` for a valid tag `t`. -/
theorem c_isid {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o S : Word} {t : BitVec 8}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P3Code Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 encodedPointIsIdentityAddress)
    (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : g sp = S) (ha0 : g a0 = t.zeroExtend 32)
    (ht : Sec1TagOk t) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧ reg n' a0 = (if t = 0 then 1 else 0) ∧
      reg n' sp = S ∧ (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ ra → reg n' q = g q) ∧
      ∀ x, Sep (S + 0xFFFFFFB0) 0x50 x 1 → n'.mem x = Mx x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  obtain ⟨n2, c2, pc2, a02, sp2, k2, fr2⟩ := (encodedPointIsIdentity_correct n1 (by rw [mem1]; exact K.panic)
    (by rw [mem1]; exact K.isid) (by rw [mem1]; exact K.tag) (by rw [mem1]; exact K.tfu) (by rw [mem1]; exact K.ext) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
    (by rw [sp1]; exact F.room (by decide))).1 ht
  rw [mem1, sp1] at fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, a02, by rw [sp2, sp1],
    fun q h0 h1 h2 h3 hr => by rw [k2 q h0 h1 h2 h3, r1 q hr], fr2⟩

/-- A call to `EncodedPoint::tag` for a valid tag `t`. -/
theorem c_tag {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o S : Word} {t : BitVec 8}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P3Code Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 encodedPointTagAddress)
    (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : g sp = S) (ha0 : g a0 = t.zeroExtend 32)
    (ht : Sec1TagOk t) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧ reg n' a0 = t.zeroExtend 32 ∧
      reg n' sp = S ∧ (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ ra → reg n' q = g q) ∧
      ∀ x, Sep (S + 0xFFFFFFC0) 0x40 x 1 → n'.mem x = Mx x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  obtain ⟨n2, c2, pc2, a02, sp2, k2, fr2⟩ := (encodedPointTag_correct n1 (by rw [mem1]; exact K.panic)
    (by rw [mem1]; exact K.tag) (by rw [mem1]; exact K.tfu) (by rw [mem1]; exact K.ext) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
    (by rw [sp1]; exact F.room (by decide))).1 ht
  rw [mem1, sp1] at fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, a02, by rw [sp2, sp1],
    fun q h0 h1 h2 h3 hr => by rw [k2 q h0 h1 h2 h3, r1 q hr], fr2⟩

abbrev UOR : Word := BitVec.ofNat 32 unwrapOr384Address
theorem uor_cs : UOR + 0x1070C = BitVec.ofNat 32 condSelect384Address := by decide
theorem uor_stub : UOR + 0x1070C + 0x101A = MCS := by decide
theorem uor_body : UOR + 0x1070C + 0x101A + 8 = MCS + 8 := by decide
theorem uor_cta : UOR + 0x1070C + 0x2EC = BitVec.ofNat 32 uint12CtAssignAddress := by decide
theorem uor_sca : UOR + 0x1070C + 0x2EC + 0xFFFF9B66 = BitVec.ofNat 32 sliceCtAssignAddress := by decide

/-- A call to `CtOption<AffinePoint<NistP384>>::into`: the point at `s` when
its choice byte at `s + 0x64` is 1, else the identity at `p384AffineIdentityAddress`, then
the choice. -/
theorem c_into {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o out sv S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P3Code Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 ctIntoAffine384Address)
    (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = sv) {co cs : Nat} (hco : co + 0x65 ≤ N) (hcs : cs + 0x65 ≤ N)
    (eo : out = S + BitVec.ofNat 32 co) (es : sv = S + BitVec.ofNat 32 cs) (acs : cs % 4 = 0)
    (hd : co + 0x65 ≤ cs ∨ cs + 0x65 ≤ co) (hch : Mx (sv + 0x64) = 0 ∨ Mx (sv + 0x64) = 1) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      (∀ i, i < 12 → memLoad32 n'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if Mx (sv + 0x64) = 1 then memLoad32 Mx (sv + BitVec.ofNat 32 (4 * i))
        else memLoad32 Mx ((img% p384AffineIdentityAddress) + BitVec.ofNat 32 (4 * i))) ∧
      (∀ i, i < 12 → memLoad32 n'.mem (out + 0x30 + BitVec.ofNat 32 (4 * i)) =
        if Mx (sv + 0x64) = 1 then memLoad32 Mx (sv + 0x30 + BitVec.ofNat 32 (4 * i))
        else memLoad32 Mx ((img% p384AffineIdentityAddress) + 0x30 + BitVec.ofNat 32 (4 * i))) ∧
      n'.mem (out + 0x60) = (if Mx (sv + 0x64) = 1 then Mx (sv + 0x60) else Mx ((img% p384AffineIdentityAddress) + 0x60)) ∧
      n'.mem (out + 0x64) = Mx (sv + 0x64) ∧ reg n' sp = S ∧
      (∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q) ∧
      ∀ y, Sep (S + 0xFFFFFF70) 0x90 y 1 → Sep out 0x65 y 1 → n'.mem y = Mx y := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have hb90 : (S + 0xFFFFFF70).toNat = S.toNat - 0x90 := F.below 0x90 (by decide) (by decide)
  have eG : S + 0xFFFFFFF0 + 0xFFFFFF80 = S + 0xFFFFFF70 := by rw [BitVec.add_assoc]; rfl
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 →
      Sep (S + 0xFFFFFFF0 + 0xFFFFFF80) 0x80 b len := fun b len hb hl => by
    rw [eG]; exact sep_of_le (by rw [hb90]; omega) hl
  have oT : (out).toNat = S.toNat + co := by rw [eo, F.at co (by omega)]
  have sT : (sv).toNat = S.toNat + cs := by rw [es, F.at cs (by omega)]
  have hID : Sep (S + 0xFFFFFF70) 0x90 (img% p384AffineIdentityAddress : Word) 0x61 :=
    F.lowData (c := 0x90) (by decide) rfl (by decide) (by decide)
  have E : UOEnv n1.mem UOR (S + 0xFFFFFFF0) out sv (img% p384AffineIdentityAddress) := by
    rw [mem1]
    refine ⟨by decide, K.uor, by rw [uor_cs]; exact K.csel, by rw [uor_stub]; exact K.stub, by rw [uor_body]; exact K.body,
      by rw [uor_cta]; exact K.cta, by rw [uor_sca]; exact K.sca, by rw [hb16]; omega, by rw [hb16]; omega,
      by omega, by omega, by decide, by omega, frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide),
      frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide),
      frC _ _ (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (rw [eo]; exact F.sepHi (by omega) (by decide) (by decide))
      | skip
    · rw [eG]; exact (sep_of_le (by rw [hb90]; omega) (by omega)).symm
    · rw [eG]; exact (sep_of_le (by rw [hb90]; omega) (by omega)).symm
    · rw [eG]; have := hID.sub (c := 0) (l := 0x80) (by decide); rw [add_ofNat_zero] at this; exact this.symm
    · rw [eo, es]; exact sepS S (by omega) (by omega) (by omega)
    · rw [eo]; exact F.bufData (by omega) (by decide) (by decide)
  obtain ⟨n2, c2, pc2, sp2, w2, v2, z2, ch2, k2, fr2⟩ := ctIntoAffine384_correct n1 (by rw [mem1]; exact K.into) E pc1 sp1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8) (by rw [mem1]; exact hch) (by omega) (by omega) (by omega)
    (by rw [eo]; exact F.mcN hco) (by rw [es]; exact F.mcN hcs)
    ((F.lowData (c := 16) (by decide) rfl (by decide) (by decide)).symm)
  rw [mem1] at w2 v2 z2 ch2 fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, w2, v2, z2, ch2, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], fr2⟩

end C3.RV32.P3
