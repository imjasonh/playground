import C3BootProofs.Proofs.P3Lib
import C3BootProofs.Proofs.P256FromRepr
import C3BootProofs.Proofs.FieldMul
import C3BootProofs.Proofs.FieldAdd
import C3BootProofs.Proofs.Uint8CtEq
import C3BootProofs.Image.BootloaderData5

/-!
# Calls to the P-256 field functions, from any caller

The P-256 counterparts of `P3Lib`: `from_repr`, `conditional_select`, the
field `multiply` and `add`, `Uint<8>::ct_eq`, and `CtOption::into`, for a
caller with its frame `Fr S N`.
-/

namespace C3.RV32.P2

open C3.Image C3.RV32.Dq C3.RV32.P3

set_option maxRecDepth 20000

/-- `2^-256 mod p` for P-256. -/
def p2RInv : Nat := 0xfffffffe00000003fffffffd0000000200000001fffffffe0000000300000000

/-- The Montgomery product for P-256. -/
def p2fm (a b : Nat) : Nat := a * b * p2RInv % p256

set_option exponentiation.threshold 600 in
theorem p256_pos : 0 < p256 := by unfold p256; decide

theorem p2fm_lt (a b : Nat) : p2fm a b < p256 := Nat.mod_lt _ p256_pos

theorem p2_mont {R A B : Nat} (hR : R < p256) (h : (R * 2 ^ 256) % p256 = (A * B) % p256) : R = p2fm A B := by
  have hinv : (2 ^ 256 * p2RInv) % p256 = 1 := by unfold p256 p2RInv; decide
  unfold p2fm
  calc R = R % p256 := (Nat.mod_eq_of_lt hR).symm
    _ = (R * ((2 ^ 256 * p2RInv) % p256)) % p256 := by rw [hinv, Nat.mul_one]
    _ = (R * 2 ^ 256 * p2RInv) % p256 := by rw [Nat.mul_mod_mod, Nat.mul_assoc]
    _ = ((R * 2 ^ 256) % p256 * p2RInv) % p256 := by rw [Nat.mod_mul_mod]
    _ = ((A * B) % p256 * p2RInv) % p256 := by rw [h]
    _ = (A * B * p2RInv) % p256 := by rw [Nat.mod_mul_mod]

abbrev P2N : Word := BitVec.ofNat 32 p256ParamsAddress
abbrev P2A : Word := BitVec.ofNat 32 p256CurveAAddress
abbrev P2B : Word := BitVec.ofNat 32 p256BAddress

/-- The P-256 functions a caller calls, beyond the shared ones. -/
structure P2Code (M : Word → BitVec 8) : Prop where
  K : P3Code M
  frq : CodeIn M FRQ p256FromReprCode
  sz : CodeIn M (BitVec.ofNat 32 shaZero32Address) shaZero32Code
  mm8 : CodeIn M (BitVec.ofNat 32 mulMont8Address) mulMont8Code
  sel8 : CodeIn M (BitVec.ofNat 32 uintSelect8Address) uintSelect8Code
  csel2 : CodeIn M (BitVec.ofNat 32 condSelect256Address) condSelect256Code
  fmul : CodeIn M (BitVec.ofNat 32 fieldMulAddress) fieldMulCode
  wm : CodeIn M (BitVec.ofNat 32 wideMulAddress) wideMulCode
  si : CodeIn M (BitVec.ofNat 32 subInnerAddress) subInnerCode
  fadd : CodeIn M (BitVec.ofNat 32 fieldAddAddress) fieldAddCode
  u8ce : CodeIn M (BitVec.ofNat 32 uint8CtEqAddress) uint8CtEqCode
  spl8 : CodeIn M (BitVec.ofNat 32 splitAt8Address) splitAt8Code
  into2 : CodeIn M (BitVec.ofNat 32 ctIntoAffine256Address) ctIntoAffine256Code
  uor2 : CodeIn M (BitVec.ofNat 32 unwrapOr256Address) unwrapOr256Code

theorem P2Code.hi {M M' : Word → BitVec 8} (K : P2Code M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    P2Code M' :=
  ⟨K.K.hi h, codeHi K.frq (by decide) (by decide) h, codeHi K.sz (by decide) (by decide) h,
    codeHi K.mm8 (by decide) (by decide) h, codeHi K.sel8 (by decide) (by decide) h,
    codeHi K.csel2 (by decide) (by decide) h, codeHi K.fmul (by decide) (by decide) h,
    codeHi K.wm (by decide) (by decide) h, codeHi K.si (by decide) (by decide) h,
    codeHi K.fadd (by decide) (by decide) h, codeHi K.u8ce (by decide) (by decide) h,
    codeHi K.spl8 (by decide) (by decide) h, codeHi K.into2 (by decide) (by decide) h,
    codeHi K.uor2 (by decide) (by decide) h⟩

/-- The P-256 constants: the field parameters, `a`, and `b`, in Montgomery form. -/
structure P2Data (M : Word → BitVec 8) : Prop where
  params : CodeIn M P2N p256ParamsData
  ca : CodeIn M P2A p256CurveAData
  cb : CodeIn M P2B p256BData

theorem P2Data.ofR {M M' : Word → BitVec 8} (D : P2Data M)
    (h : ∀ i, i < (img% dataWindowSize) → M' ((img% dataWindowAddress : Word) + BitVec.ofNat 32 i) = M ((img% dataWindowAddress : Word) + BitVec.ofNat 32 i)) :
    P2Data M' := by
  have cd : ∀ (b : Word) (d : List Nat), CodeIn M b d → (img% dataWindowAddress) ≤ b.toNat → b.toNat + d.length ≤ (img% dataWindowAddress + dataWindowSize) →
      CodeIn M' b d := fun b d hc h1 h2 i hi => by
    have e : b + BitVec.ofNat 32 i = (img% dataWindowAddress : Word) + BitVec.ofNat 32 (b.toNat - (img% dataWindowAddress) + i) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show (img% dataWindowAddress : Word).toNat = (img% dataWindowAddress) from rfl]
      omega
    rw [e, h _ (by omega), ← e]
    exact hc i hi
  exact ⟨cd _ _ D.params (by decide) (by decide), cd _ _ D.ca (by decide) (by decide), cd _ _ D.cb (by decide) (by decide)⟩

theorem P2Data.of {M M' : Word → BitVec 8} {S : Word} {N : Nat} (F : Fr S N) (D : P2Data M)
    (h : ∀ x, Sep (S + 0xFFFFFE60) (N + 0x1A0) x 1 → M' x = M x) : P2Data M' :=
  D.ofR fun i hi => h _ (F.dsep.subR (c := i) (l := 1) hi)

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 600 in
theorem p2params_N : dataVal p256ParamsData 0 8 = p256 := by unfold p256; decide
theorem p2params_n0 : wordAt p256ParamsData 0 0 = 0xFFFFFFFF := by decide
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 600 in
theorem p2params_r2 : dataVal p256ParamsData 0x40 8 < p256 := by unfold p256; decide

theorem P2Data.N {M : Word → BitVec 8} (D : P2Data M) : accV M p256Np 8 = p256 := by
  rw [show p256Np = P2N + BitVec.ofNat 32 0 from rfl, code_accV D.params 0 8 (by decide), p2params_N]

theorem P2Data.N0 {M : Word → BitVec 8} (D : P2Data M) : memLoad32 M p256Np = 0xFFFFFFFF := by
  rw [show p256Np = P2N + BitVec.ofNat 32 (0 + 4 * 0) from rfl, code_word D.params 0 0 (by decide), p2params_n0]

theorem P2Data.r2lt {M : Word → BitVec 8} (D : P2Data M) : accV M (p256Np + 0x40) 8 < accV M p256Np 8 := by
  rw [D.N, show p256Np + 0x40 = P2N + BitVec.ofNat 32 0x40 from rfl, code_accV D.params 0x40 8 (by decide)]
  exact p2params_r2

abbrev CS2 : Word := BitVec.ofNat 32 condSelect256Address
theorem cs2_stub : CS2 + 0x323E = MCS := by decide
theorem cs2_body : CS2 + 0x323E + 8 = MCS + 8 := by decide
theorem cs2_sca : CS2 + 0xFFFFC076 = BitVec.ofNat 32 sliceCtAssignAddress := by decide

/-- A call to the P-256 field `conditional_select`, with all three operands in the caller's frame. -/
theorem c2_csel {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o out a b c S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P2Code Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = CS2) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = a) (ha2 : g a2 = b) (ha3 : g a3 = c) (hc : c = 0 ∨ c = 1)
    {co ca cb : Nat} (hco : co + 32 ≤ N) (hca : ca + 32 ≤ N) (hcb : cb + 32 ≤ N)
    (eo : out = S + BitVec.ofNat 32 co) (ea : a = S + BitVec.ofNat 32 ca) (eb : b = S + BitVec.ofNat 32 cb)
    (acb : cb % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      (∀ i, i < 8 → memLoad32 n'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 Mx (b + BitVec.ofNat 32 (4 * i)) else memLoad32 Mx (a + BitVec.ofNat 32 (4 * i))) ∧
      (∀ x, Sep (S + 0xFFFFFFB0) 0x50 x 1 → Sep out 32 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFFB0).toNat = S.toNat - 0x50 := F.below 0x50 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFFB0) 0x50 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have frS : ∀ cz, cz + 32 ≤ N → Sep (S + BitVec.ofNat 32 cz) 32 (S + 0xFFFFFFB0) 0x50 := fun cz h =>
    (sep_of_le (by rw [hbF, F.at cz (by omega)]; omega) (by rw [F.at cz (by omega)]; omega)).symm
  have E : CS2Env n1.mem CS2 (reg n1 sp) out a b := by
    rw [sp1, mem1]
    refine ⟨by decide, K.csel2, by rw [cs2_stub]; exact K.K.stub, by rw [cs2_body]; exact K.K.body,
      by rw [cs2_sca]; exact K.K.sca, by omega, by omega, ?_, ?_, ?_,
      frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide),
      frC _ _ (by decide) (by decide), ?_, ?_, ?_, ?_, ?_⟩
    · rw [eb, F.at cb (by omega)]; omega
    · rw [ea, F.at ca (by omega)]; omega
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo]; exact frS co hco
    · rw [ea]; exact frS ca hca
    · rw [eb]; exact frS cb hcb
  obtain ⟨n2, c2, pc2, sp2, vals, k2, fr2⟩ := condSelect256_correct n1 E pc1 rfl (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3)
    hc (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at vals fr2
  rw [sp1] at fr2 sp2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, vals, fr2, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]⟩

/-- A call to P-256 `FieldElement::from_repr` on the 32 bytes at `inp`. -/
theorem c2_frp {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o out inp S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P2Code Mx) (D : P2Data Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = FRQ) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = inp)
    {co : Nat} (hco : co + 33 ≤ N) (eo : out = S + BitVec.ofNat 32 co)
    (sI : Sep inp 32 (S + 0xFFFFFEC0) 0x140) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      (beNat (memBytes Mx inp 32) < p256 →
        n'.mem (out + 0x20) = 1 ∧ accV n'.mem out 8 < p256 ∧
        accV n'.mem out 8 * 2 ^ 256 % p256 = beNat (memBytes Mx inp 32) * dataVal p256ParamsData 0x40 8 % p256) ∧
      (p256 ≤ beNat (memBytes Mx inp 32) → n'.mem (out + 0x20) = 0 ∧ accV n'.mem out 8 = 0) ∧
      (∀ x, Sep (S + 0xFFFFFEC0) 0x140 x 1 → Sep out 33 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFEC0).toNat = S.toNat - 0x140 := F.below 0x140 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have E : FRQEnv n1.mem := by
    rw [mem1]
    exact ⟨K.frq, K.sz, K.K.mset, K.K.stub, K.K.body, K.K.bsub, K.K.refnz, K.mm8, K.sel8, K.K.bb, K.csel2, K.K.sca, D.N0,
      D.r2lt⟩
  have hR : accV Mx (p256Np + 0x40) 8 = dataVal p256ParamsData 0x40 8 :=
    code_accV D.params 0x40 8 (by decide)
  obtain ⟨n2, c2, pc2, sp2, k2, ok, bad, fr2⟩ := p256FromRepr_correct (out := out) (inp := inp) n1 E pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8) sp1 hSa (by omega) (by omega) (by rw [eo, F.at co (by omega)]; omega)
    (by rw [eo]; exact (sep_of_le (by rw [hbF, F.at co (by omega)]; omega) (by rw [F.at co (by omega)]; omega)).symm) sI
    (F.lowData (c := 0x140) (by decide) rfl (by decide) (by decide))
  rw [mem1, D.N] at ok bad
  rw [hR] at ok
  rw [mem1] at fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, ok, bad, fr2, sp2,
    fun q hq => by rw [k2 q hq, r1 q (by revert hq; revert q; decide)]⟩

abbrev FMUL : Word := BitVec.ofNat 32 fieldMulAddress
abbrev FADD : Word := BitVec.ofNat 32 fieldAddAddress
theorem fm_wm : FMUL + 0xFFFFBD44 = BitVec.ofNat 32 wideMulAddress := by decide
theorem fm_si : FMUL + 0x40C = BitVec.ofNat 32 subInnerAddress := by decide
theorem fa_si : FADD + 0xFFFFFC46 = BitVec.ofNat 32 subInnerAddress := by decide
theorem fm_mset : FMUL + 0xFFFFBD44 + 0x7446 = MSET := by decide
theorem fm_stub : FMUL + 0xFFFFBD44 + 0x74AE = MCS := by decide
theorem fm_body : FMUL + 0xFFFFBD44 + 0x74B6 = MCS + 8 := by decide
theorem fm_bsub : siBsub (FMUL + 0x40C) = BSUB := by decide
theorem fa_bsub : siBsub (FADD + 0xFFFFFC46) = BSUB := by decide

/-- A call to P-256 `FieldElement::multiply`: the Montgomery product of operands below `p`. -/
theorem c2_fmul {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o out xp yp S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P2Code Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = FMUL) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = xp) (ha2 : g a2 = yp)
    {co : Nat} (hco : co + 32 ≤ N) (eo : out = S + BitVec.ofNat 32 co) (aco : co % 4 = 0)
    (sX : Sep xp 32 (S + 0xFFFFFED0) 0x130) (aX : xp.toNat % 4 = 0)
    (sY : Sep yp 32 (S + 0xFFFFFED0) 0x130) (aY : yp.toNat % 4 = 0)
    (hX : accV Mx xp 8 < p256) (hY : accV Mx yp 8 < p256) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      accV n'.mem out 8 = p2fm (accV Mx xp 8) (accV Mx yp 8) ∧
      (∀ x, Sep (S + 0xFFFFFED0) 0x130 x 1 → Sep out 32 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
        q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → q ≠ ra →
        reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFED0).toNat = S.toNat - 0x130 := F.below 0x130 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFED0) 0x130 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have E : FMEnv n1.mem FMUL (reg n1 sp) out xp yp := by
    rw [sp1, mem1]
    refine ⟨by decide, K.fmul, by rw [fm_wm]; exact K.wm, by rw [fm_mset]; exact K.K.mset, by rw [fm_stub]; exact K.K.stub,
      by rw [fm_body]; exact K.K.body, by rw [fm_si]; exact K.si, by rw [fm_bsub]; exact K.K.bsub,
      by omega, by rw [eo, F.at co (by omega)]; omega, aX, aY, by omega, by rw [eo, F.at co (by omega)]; omega,
      frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide),
      frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide),
      frC _ _ (by decide) (by decide), ?_, ?_, sX, sY⟩
    · rw [eo]; exact (sep_of_le (by rw [hbF, F.at co (by omega)]; omega) (by rw [F.at co (by omega)]; omega)).symm
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
  obtain ⟨n2, c2, pc2, sp2, k2, v2, lt2, fr2⟩ := fieldMul_correct n1 E pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8) rfl
  rw [mem1, limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt] at v2 lt2
  rw [mem1] at fr2
  rw [sp1] at fr2 sp2
  have hlt : accV n2.mem out 8 < p256 := lt2 (by
    calc accV Mx xp 8 * accV Mx yp 8 < p256 * p256 := Nat.mul_lt_mul_of_lt_of_lt hX hY
      _ ≤ p256 * 2 ^ 256 := Nat.mul_le_mul_left _ (by unfold p256; decide))
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, p2_mont hlt v2, fr2, sp2,
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hr => by
      rw [k2 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14, r1 q hr]⟩

/-- A call to P-256 `field_impl::add`. -/
theorem c2_fadd {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o out lp rp S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P2Code Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = FADD) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = lp) (ha2 : g a2 = rp)
    {co : Nat} (hco : co + 32 ≤ N) (eo : out = S + BitVec.ofNat 32 co) (aco : co % 4 = 0)
    (sL : Sep lp 32 (S + 0xFFFFFF4C) 0xB4) (aL : lp.toNat % 4 = 0)
    (sR : Sep rp 32 (S + 0xFFFFFF4C) 0xB4) (aR : rp.toNat % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      accV n'.mem out 8 = subRes (accV Mx lp 8 + accV Mx rp 8) ∧
      (∀ x, Sep (S + 0xFFFFFF4C) 0xB4 x 1 → Sep out 32 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
        q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → q ≠ ra →
        reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFF4C).toNat = S.toNat - 0xB4 := F.below 0xB4 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFF4C) 0xB4 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have E : FAEnv n1.mem FADD (reg n1 sp) out lp rp := by
    rw [sp1, mem1]
    refine ⟨by decide, K.fadd, by rw [fa_si]; exact K.si, by rw [fa_bsub]; exact K.K.bsub,
      by omega, by rw [eo, F.at co (by omega)]; omega, aL, aR, by omega, by rw [eo, F.at co (by omega)]; omega,
      frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide), ?_, ?_, sL, sR⟩
    · rw [eo]; exact (sep_of_le (by rw [hbF, F.at co (by omega)]; omega) (by rw [F.at co (by omega)]; omega)).symm
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
  obtain ⟨n2, c2, pc2, sp2, k2, v2, fr2⟩ := fieldAdd_correct n1 E pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8) rfl
  rw [mem1, limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt] at v2
  rw [mem1] at fr2
  rw [sp1] at fr2 sp2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, v2, fr2, sp2,
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hr => by
      rw [k2 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14, r1 q hr]⟩

abbrev U8CE : Word := BitVec.ofNat 32 uint8CtEqAddress
theorem u8_spl : U8CE + 0x80 = BitVec.ofNat 32 splitAt8Address := by decide
theorem u8_lce : U8CE + 0xFFFFBCE6 = BitVec.ofNat 32 limbCtEqAddress := by decide
theorem u8_uiz : U8CE + 0xFFFF12EE = BitVec.ofNat 32 uintRefIsZeroAddress := by decide
theorem u8_unz : U8CE + 0xFFFF12EE + 0x1A = BitVec.ofNat 32 uintRefIsNonzeroAddress := by decide

/-- A call to `Uint<8>::ct_eq`. -/
theorem c2_uce {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o pa pb S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P2Code Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = U8CE) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = pa) (ha1 : g a1 = pb) (hpa : pa.toNat % 4 = 0) (hpb : pb.toNat % 4 = 0)
    (sA : Sep pa 32 (S + 0xFFFFFFBC) 0x44) (sB : Sep pb 32 (S + 0xFFFFFFBC) 0x44) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      reg n' a0 = (if ∀ i : Nat, i < 8 → memLoad32 Mx (pa + BitVec.ofNat 32 (4 * i)) =
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
  have E : U8CEEnv n1.mem U8CE S pa pb := by
    rw [mem1]
    exact ⟨by decide, K.u8ce, by rw [u8_spl]; exact K.spl8, by rw [u8_lce]; exact K.K.lce, by rw [u8_uiz]; exact K.K.uiz,
      by rw [u8_unz]; exact K.K.refnz, by omega, by omega, hpa, hpb, frC _ _ (by decide) (by decide),
      frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide),
      frC _ _ (by decide) (by decide), sA, sB⟩
  obtain ⟨n2, c2, pc2, sp2, a02, k2, fr2⟩ := uint8CtEq_correct n1 E pc1 sp1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at a02 fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, a02, fr2, sp2, fun q hq hr => by rw [k2 q hq, r1 q hr]⟩

abbrev UOR2 : Word := BitVec.ofNat 32 unwrapOr256Address
theorem uor2_cs : UOR2 + 0xE460 = CS2 := by decide

/-- A call to `CtOption<AffinePoint<NistP256>>::into`: the point at `s` when
its choice byte at `s + 0x44` is 1, else the identity at `p256AffineIdXAddress`, then
the choice. -/
theorem c2_into {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o out sv S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P2Code Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 ctIntoAffine256Address)
    (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = sv) {co cs : Nat} (hco : co + 0x45 ≤ N) (hcs : cs + 0x45 ≤ N)
    (eo : out = S + BitVec.ofNat 32 co) (es : sv = S + BitVec.ofNat 32 cs) (acs : cs % 4 = 0)
    (hd : co + 0x45 ≤ cs ∨ cs + 0x45 ≤ co) (hch : Mx (sv + 0x44) = 0 ∨ Mx (sv + 0x44) = 1) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      (∀ i, i < 8 → memLoad32 n'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if Mx (sv + 0x44) = 1 then memLoad32 Mx (sv + BitVec.ofNat 32 (4 * i))
        else memLoad32 Mx ((img% p256AffineIdXAddress) + BitVec.ofNat 32 (4 * i))) ∧
      (∀ i, i < 8 → memLoad32 n'.mem (out + 0x20 + BitVec.ofNat 32 (4 * i)) =
        if Mx (sv + 0x44) = 1 then memLoad32 Mx (sv + 0x20 + BitVec.ofNat 32 (4 * i))
        else memLoad32 Mx ((img% p256AffineIdXAddress) + 0x20 + BitVec.ofNat 32 (4 * i))) ∧
      n'.mem (out + 0x40) = (if Mx (sv + 0x44) = 1 then Mx (sv + 0x40) else Mx ((img% p256AffineIdXAddress) + 0x40)) ∧
      n'.mem (out + 0x44) = Mx (sv + 0x44) ∧ reg n' sp = S ∧
      (∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q) ∧
      ∀ y, Sep (S + 0xFFFFFF80) 0x80 y 1 → Sep out 0x45 y 1 → n'.mem y = Mx y := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have hb80 : (S + 0xFFFFFF80).toNat = S.toNat - 0x80 := F.below 0x80 (by decide) (by decide)
  have eG : S + 0xFFFFFFF0 + 0xFFFFFF90 = S + 0xFFFFFF80 := by rw [BitVec.add_assoc]; rfl
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 →
      Sep (S + 0xFFFFFFF0 + 0xFFFFFF90) 0x70 b len := fun b len hb hl => by
    rw [eG]; exact sep_of_le (by rw [hb80]; omega) hl
  have oT : (out).toNat = S.toNat + co := by rw [eo, F.at co (by omega)]
  have sT : (sv).toNat = S.toNat + cs := by rw [es, F.at cs (by omega)]
  have hID : Sep (S + 0xFFFFFF80) 0x80 (img% p256AffineIdXAddress : Word) 0x41 :=
    F.lowData (c := 0x80) (by decide) rfl (by decide) (by decide)
  have E : UO2Env n1.mem UOR2 (S + 0xFFFFFFF0) out sv (img% p256AffineIdXAddress) := by
    rw [mem1]
    refine ⟨by decide, K.uor2, by rw [uor2_cs]; exact K.csel2, by rw [uor2_cs, cs2_stub]; exact K.K.stub,
      by rw [uor2_cs, cs2_body]; exact K.K.body, by rw [uor2_cs, cs2_sca]; exact K.K.sca, by rw [hb16]; omega,
      by rw [hb16]; omega, by omega, by omega, by decide, by omega, frC _ _ (by decide) (by decide),
      frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide),
      frC _ _ (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (rw [eo]; exact F.sepHi (by omega) (by decide) (by decide))
      | skip
    · rw [eG]; exact (sep_of_le (by rw [hb80]; omega) (by omega)).symm
    · rw [eG]; exact (sep_of_le (by rw [hb80]; omega) (by omega)).symm
    · rw [eG]; have := hID.sub (c := 0) (l := 0x70) (by decide); rw [add_ofNat_zero] at this; exact this.symm
    · rw [eo, es]; exact sepS S (by omega) (by omega) (by omega)
    · rw [eo]; exact F.bufData (by omega) (by decide) (by decide)
  obtain ⟨n2, c2, pc2, sp2, w2, v2, z2, ch2, k2, fr2⟩ := ctIntoAffine256_correct n1 (by rw [mem1]; exact K.into2) E pc1 sp1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8) (by rw [mem1]; exact hch) (by omega) (by omega) (by omega)
    (by rw [eo]; exact F.mcN hco) (by rw [es]; exact F.mcN hcs)
    ((F.lowData (c := 16) (by decide) rfl (by decide) (by decide)).symm)
  rw [mem1] at w2 v2 z2 ch2 fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, w2, v2, z2, ch2, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], fr2⟩

end C3.RV32.P2
