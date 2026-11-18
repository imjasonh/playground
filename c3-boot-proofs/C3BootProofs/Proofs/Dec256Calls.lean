import C3BootProofs.Proofs.Fs256Main
import C3BootProofs.Proofs.Dec256At
import C3BootProofs.Proofs.P256Neg
import C3BootProofs.Proofs.P256Retrieve

/-!
# P-256 point decompression: the data it reads and the calls it makes

The code and constants `AffinePoint<NistP256>::decompress` uses, and wrappers
for its calls that are not already in `P2Lib.lean`, from any caller's frame.
-/

namespace C3.RV32.Gd

open C3.Image C3.RV32.Dq C3.RV32.P3 C3.RV32.P2

set_option maxRecDepth 20000

abbrev MM8 : Word := BitVec.ofNat 32 mulMont8Address
abbrev SEL8 : Word := BitVec.ofNat 32 uintSelect8Address
abbrev NEG2 : Word := BitVec.ofNat 32 p256FieldNegAddress
abbrev RT2 : Word := BitVec.ofNat 32 p256FieldRetrieveAddress
abbrev EQ8 : Word := BitVec.ofNat 32 uint8EqAddress
abbrev CMAP2 : Word := BitVec.ofNat 32 ctMap256Address
abbrev CTE : Word := BitVec.ofNat 32 choiceCtEqAddress
abbrev EXP2 : Word := BitVec.ofNat 32 p256SqrtExpAddress
abbrev ZERO2 : Word := BitVec.ofNat 32 p256ZeroAddress

/-- The code `decompress` runs and calls, at its addresses in the image. -/
structure GdCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M GD p256DecompressCode
  K : P2Code M
  neg : CodeIn M NEG2 p256FieldNegCode
  fsub : CodeIn M (BitVec.ofNat 32 fieldSubAddress) fieldSubCode
  rt : CodeIn M RT2 p256FieldRetrieveCode
  eq8 : CodeIn M EQ8 uint8EqCode
  cmap : CodeIn M CMAP2 ctMap256Code
  cte : CodeIn M CTE choiceCtEqCode

theorem GdCode.hi {M M' : Word → BitVec 8} (C : GdCode M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    GdCode M' :=
  ⟨codeHi C.self (by decide) (by decide) h, C.K.hi h, codeHi C.neg (by decide) (by decide) h,
    codeHi C.fsub (by decide) (by decide) h, codeHi C.rt (by decide) (by decide) h,
    codeHi C.eq8 (by decide) (by decide) h, codeHi C.cmap (by decide) (by decide) h,
    codeHi C.cte (by decide) (by decide) h⟩

/-- The constants `decompress` reads: the field parameters, `a`, `b`, the
square-root exponent `(p + 1) / 4`, and the zero element. -/
structure GdData (M : Word → BitVec 8) : Prop where
  D : P2Data M
  ex : CodeIn M EXP2 p256SqrtExpData
  zero : CodeIn M ZERO2 p256ZeroData

theorem GdData.ofR {M M' : Word → BitVec 8} (G : GdData M)
    (h : ∀ i, i < 0xC60 → M' ((0x3FCC4200 : Word) + BitVec.ofNat 32 i) = M ((0x3FCC4200 : Word) + BitVec.ofNat 32 i)) :
    GdData M' := by
  have cd : ∀ (b : Word) (d : List Nat), CodeIn M b d → 0x3FCC4200 ≤ b.toNat → b.toNat + d.length ≤ 0x3FCC4E60 →
      CodeIn M' b d := fun b d hc h1 h2 i hi => by
    have e : b + BitVec.ofNat 32 i = (0x3FCC4200 : Word) + BitVec.ofNat 32 (b.toNat - 0x3FCC4200 + i) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show (0x3FCC4200 : Word).toNat = 0x3FCC4200 from rfl]
      omega
    rw [e, h _ (by omega), ← e]
    exact hc i hi
  exact ⟨G.D.ofR h, cd _ _ G.ex (by decide) (by decide), cd _ _ G.zero (by decide) (by decide)⟩

theorem GdData.of {M M' : Word → BitVec 8} {S : Word} {N : Nat} (F : Fr S N) (G : GdData M)
    (h : ∀ x, Sep (S + 0xFFFFFE60) (N + 0x1A0) x 1 → M' x = M x) : GdData M' :=
  G.ofR fun i hi => h _ (F.dsep.subR (c := i) (l := 1) hi)

theorem mm8_mset : MM8 + 0x3CA8 = MSET := by decide
theorem mm8_bsub : mmBsub8 MM8 = BSUB := by decide
theorem mm8_sel : MM8 + 0x18E = SEL8 := by decide
theorem mm8_stub : MM8 + 0x3D10 = MCS := by decide
theorem mm8_body : MM8 + 0x3D18 = MCS + 8 := by decide

set_option maxRecDepth 100000 in
/-- A call to `mul_montgomery_form::<8>` with all four operands in the
caller's frame and `K` in `a4`. -/
theorem c2_mm {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o out xp yp np Kv S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P2Code Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = MM8) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = xp) (ha2 : g a2 = yp) (ha3 : g a3 = np) (ha4 : g a4 = Kv)
    {co cx cy cn : Nat} (hco : co + 32 ≤ N) (hcx : cx + 32 ≤ N) (hcy : cy + 32 ≤ N) (hcn : cn + 32 ≤ N)
    (eo : out = S + BitVec.ofNat 32 co) (ex : xp = S + BitVec.ofNat 32 cx) (ey : yp = S + BitVec.ofNat 32 cy)
    (en : np = S + BitVec.ofNat 32 cn) (aco : co % 4 = 0) (acx : cx % 4 = 0) (acy : cy % 4 = 0) (acn : cn % 4 = 0)
    (hk : (Kv.toNat * (memLoad32 Mx np).toNat + 1) % 2 ^ 32 = 0) (hYN : accV Mx yp 8 < accV Mx np 8) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      accV n'.mem out 8 < accV Mx np 8 ∧
      accV n'.mem out 8 * 2 ^ 256 % accV Mx np 8 = accV Mx xp 8 * accV Mx yp 8 % accV Mx np 8 ∧
      (∀ x, Sep (S + 0xFFFFFF40) 0xC0 x 1 → Sep out 32 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFF40).toNat = S.toNat - 0xC0 := F.below 0xC0 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFF40) 0xC0 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have frS : ∀ cz, cz + 32 ≤ N → Sep (S + BitVec.ofNat 32 cz) 32 (S + 0xFFFFFF40) 0xC0 := fun cz h =>
    (sep_of_le (by rw [hbF, F.at cz (by omega)]; omega) (by rw [F.at cz (by omega)]; omega)).symm
  have E : MMEnv8 n1.mem MM8 (reg n1 sp) out xp yp np := by
    rw [sp1, mem1]
    refine ⟨by decide, K.mm8, by rw [mm8_mset]; exact K.K.mset, by rw [mm8_bsub]; exact K.K.bsub,
      by rw [mm8_sel]; exact K.sel8, by rw [mm8_stub]; exact K.K.stub, by rw [mm8_body]; exact K.K.body,
      by omega, by omega, ?_, ?_, ?_, ?_, ?_,
      frC _ _ (by decide) (by decide), frC _ _ (by rw [mm8_mset]; decide) (by rw [mm8_mset]; decide),
      frC _ _ (by rw [mm8_bsub]; decide) (by rw [mm8_bsub]; decide), frC _ _ (by rw [mm8_sel]; decide) (by rw [mm8_sel]; decide),
      frC _ _ (by rw [mm8_stub]; decide) (by rw [mm8_stub]; decide), frC _ _ (by rw [mm8_body]; decide)
        (by rw [mm8_body]; decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eo, F.at co (by omega)]; omega
    · rw [ex, F.at cx (by omega)]; omega
    · rw [ey, F.at cy (by omega)]; omega
    · rw [en, F.at cn (by omega)]; omega
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo]; exact frS co hco
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, mm8_sel]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, mm8_body]; exact F.sepHi hco (by decide) (by decide)
    · rw [ex]; exact frS cx hcx
    · rw [ey]; exact frS cy hcy
    · rw [en]; exact frS cn hcn
  obtain ⟨n2, c2, pc2, sp2, hlt, hcg, fr2, k2⟩ := mulMont8_correct (K := Kv) n1 E pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3)
    (by rw [r1 a4 (by decide)]; exact ha4) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) rfl
    (by rw [mem1]; exact hk) (by rw [mem1]; exact hYN)
  rw [mem1] at hlt hcg fr2
  rw [sp1] at fr2 sp2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, hlt, hcg, fr2, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]⟩

theorem sel8_mset : SEL8 + 0x3B1A = MSET := by decide
theorem sel8_stub : SEL8 + 0x3B82 = MCS := by decide
theorem sel8_body : SEL8 + 0x3B8A = MCS + 8 := by decide

/-- The registers `Uint<8>::select` leaves alone. -/
def sel8Keep (q : Fin 32) : Bool := q.val ∈ [1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

set_option maxRecDepth 100000 in
/-- A call to `Uint<8>::select` with all three operands in the caller's frame. -/
theorem c2_sel {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o out ap bp c S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P2Code Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = SEL8) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = ap) (ha2 : g a2 = bp) (ha3 : g a3 = c) (hc : c = 0 ∨ c = 1)
    {co ca cb : Nat} (hco : co + 32 ≤ N) (hca : ca + 32 ≤ N) (hcb : cb + 32 ≤ N)
    (eo : out = S + BitVec.ofNat 32 co) (ea : ap = S + BitVec.ofNat 32 ca) (eb : bp = S + BitVec.ofNat 32 cb)
    (aco : co % 4 = 0) (aca : ca % 4 = 0) (acb : cb % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      (∀ i, i < 8 → memLoad32 n'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 Mx (bp + BitVec.ofNat 32 (4 * i)) else memLoad32 Mx (ap + BitVec.ofNat 32 (4 * i))) ∧
      (∀ x, Sep (S + 0xFFFFFFC0) 0x40 x 1 → Sep out 32 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, sel8Keep q = true → q ≠ ra → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFFC0).toNat = S.toNat - 0x40 := F.below 0x40 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFFC0) 0x40 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have frS : ∀ cz, cz + 32 ≤ N → Sep (S + BitVec.ofNat 32 cz) 32 (S + 0xFFFFFFC0) 0x40 := fun cz h =>
    (sep_of_le (by rw [hbF, F.at cz (by omega)]; omega) (by rw [F.at cz (by omega)]; omega)).symm
  have E : Sel8Env n1.mem SEL8 (reg n1 sp) out ap bp := by
    rw [sp1, mem1]
    refine ⟨by decide, K.sel8, by rw [sel8_mset]; exact K.K.mset, by rw [sel8_stub]; exact K.K.stub,
      by rw [sel8_body]; exact K.K.body, by omega, by omega, ?_, ?_, ?_, ?_,
      frC _ _ (by decide) (by decide), frC _ _ (by rw [sel8_mset]; decide) (by rw [sel8_mset]; decide),
      frC _ _ (by rw [sel8_stub]; decide) (by rw [sel8_stub]; decide), frC _ _ (by rw [sel8_body]; decide)
        (by rw [sel8_body]; decide), ?_, ?_, ?_, ?_, ?_⟩
    · rw [eo, F.at co (by omega)]; omega
    · rw [ea, F.at ca (by omega)]; omega
    · rw [eb, F.at cb (by omega)]; omega
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo]; exact frS co hco
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, sel8_body]; exact F.sepHi hco (by decide) (by decide)
    · rw [ea]; exact frS ca hca
    · rw [eb]; exact frS cb hcb
  obtain ⟨n2, c2, pc2, sp2, vals, fr2, k2⟩ := uintSelect8_correct (c := c) n1 (by rw [sp1] at E; rw [sp1]; exact E) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2)
    (by rw [r1 a3 (by decide)]; exact ha3) hc (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at vals fr2
  rw [sp1] at fr2 sp2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, vals, fr2, sp2,
    fun q hq hr => by rw [k2 q (by revert hq; revert q; decide), r1 q hr]⟩

theorem neg2_fs : NEG2 + 0x12 = BitVec.ofNat 32 fieldSubAddress := by decide
theorem neg2_si : NEG2 + 0x12 + 0xFFFFFB24 = BitVec.ofNat 32 subInnerAddress := by decide
theorem neg2_bsub : siBsub (NEG2 + 0x12 + 0xFFFFFB24) = BSUB := by decide

set_option maxRecDepth 100000 in
/-- A call to P-256 `FieldElement::neg` with both operands in the caller's frame. -/
theorem c2_neg {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o out xp S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P2Code Mx) (C : GdCode Mx) (G : GdData Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = NEG2) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = xp)
    {co cx : Nat} (hco : co + 32 ≤ N) (hcx : cx + 32 ≤ N)
    (eo : out = S + BitVec.ofNat 32 co) (ex : xp = S + BitVec.ofNat 32 cx) (aco : co % 4 = 0) (acx : cx % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      accV n'.mem out 8 = subGen 0 (accV Mx xp 8) ∧
      (∀ x, Sep (S + 0xFFFFFF4C) 0xB4 x 1 → Sep out 32 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFF4C).toNat = S.toNat - 0xB4 := F.below 0xB4 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFF4C) 0xB4 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have frS : ∀ cz, cz + 32 ≤ N → Sep (S + BitVec.ofNat 32 cz) 32 (S + 0xFFFFFF4C) 0xB4 := fun cz h =>
    (sep_of_le (by rw [hbF, F.at cz (by omega)]; omega) (by rw [F.at cz (by omega)]; omega)).symm
  have E : FSEnv n1.mem (NEG2 + 0x12) (reg n1 sp) out (BitVec.ofNat 32 p256ZeroAddress) xp := by
    rw [sp1, mem1]
    refine ⟨by decide, by rw [neg2_fs]; exact C.fsub, by rw [neg2_si]; exact K.si, by rw [neg2_bsub]; exact K.K.bsub,
      by omega, ?_, by decide, ?_, by omega, ?_,
      frC _ _ (by decide) (by decide), frC _ _ (by decide) (by decide), frC _ _ (by rw [neg2_bsub]; decide)
        (by rw [neg2_bsub]; decide), ?_, ?_, (F.lowData (c := 0xB4) (by decide) rfl (by decide) (by decide)).symm, ?_⟩
    · rw [eo, F.at co (by omega)]; omega
    · rw [ex, F.at cx (by omega)]; omega
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo]; exact frS co hco
    · rw [eo, neg2_fs]; exact F.sepHi hco (by decide) (by decide)
    · rw [ex]; exact frS cx hcx
  obtain ⟨n2, c2, pc2, sp2, k2, hv2, fr2⟩ := p256FieldNeg_correct n1 (by decide) (by rw [mem1]; exact C.neg) E
    (by rw [mem1]; exact G.zero) pc1 (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) rfl
  rw [mem1, limbVal_wordsAt, limbVal_wordsAt] at hv2
  rw [mem1] at fr2
  rw [sp1] at fr2 sp2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, hv2, fr2, sp2,
    fun q hq => by
      rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]⟩

theorem rt2_mset : RT2 + 0x27AE = MSET := by decide
theorem rt2_stub : RT2 + 0x2816 = MCS := by decide
theorem rt2_body : RT2 + 0x281E = MCS + 8 := by decide

set_option maxRecDepth 100000 in
/-- A call to `ConstMontyForm<p256::FieldParams>::retrieve` with both operands in the caller's frame. -/
theorem c2_rt {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o out xp S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P2Code Mx) (C : GdCode Mx) (D : P2Data Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = RT2) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = xp)
    {co cx : Nat} (hco : co + 32 ≤ N) (hcx : cx + 32 ≤ N)
    (eo : out = S + BitVec.ofNat 32 co) (ex : xp = S + BitVec.ofNat 32 cx) (aco : co % 4 = 0) (acx : cx % 4 = 0)
    (hX : accV Mx xp 8 < p256) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      accV n'.mem out 8 = p2fm (accV Mx xp 8) 1 ∧
      (∀ x, Sep (S + 0xFFFFFFC0) 0x40 x 1 → Sep out 32 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFFC0).toNat = S.toNat - 0x40 := F.below 0x40 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFFC0) 0x40 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have frS : ∀ cz, cz + 32 ≤ N → Sep (S + BitVec.ofNat 32 cz) 32 (S + 0xFFFFFFC0) 0x40 := fun cz h =>
    (sep_of_le (by rw [hbF, F.at cz (by omega)]; omega) (by rw [F.at cz (by omega)]; omega)).symm
  have E : PREnv n1.mem RT2 (reg n1 sp) out xp := by
    rw [sp1, mem1]
    refine ⟨by decide, C.rt, by rw [rt2_mset]; exact K.K.mset, by rw [rt2_stub]; exact K.K.stub,
      by rw [rt2_body]; exact K.K.body, by omega, by omega, ?_, ?_, ?_, D.N0,
      frC _ _ (by decide) (by decide), frC _ _ (by rw [rt2_mset]; decide) (by rw [rt2_mset]; decide),
      frC _ _ (by rw [rt2_stub]; decide) (by rw [rt2_stub]; decide), frC _ _ (by rw [rt2_body]; decide)
        (by rw [rt2_body]; decide), ?_, ?_, ?_, ?_, (F.lowData (c := 0x40) (by decide) rfl (by decide) (by decide)).symm⟩
    · rw [eo, F.at co (by omega)]; omega
    · rw [ex, F.at cx (by omega)]; omega
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo]; exact frS co hco
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, rt2_body]; exact F.sepHi hco (by decide) (by decide)
    · rw [ex]; exact frS cx hcx
  obtain ⟨n2, c2, pc2, sp2, hcg, hlt, fr2, k2⟩ := p256FieldRetrieve_correct n1 E pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) rfl
  rw [mem1, D.N] at hcg hlt
  rw [mem1] at fr2
  rw [sp1] at fr2 sp2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, p2_mont (hlt hX) (by rw [hcg, Nat.mul_one]), fr2, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]⟩

/-- A call to `Uint<8>::eq`. -/
theorem c2_eq8 {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o p q S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (C : GdCode Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = EQ8)
    (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = p) (ha1 : g a1 = q) (hp : p.toNat % 4 = 0) (hq : q.toNat % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      reg n' a0 = (if ∀ i : Nat, i < 8 → memLoad32 Mx (p + BitVec.ofNat 32 (4 * i)) =
        memLoad32 Mx (q + BitVec.ofNat 32 (4 * i)) then 1 else 0) ∧
      (∀ x, Sep (S + 0xFFFFFFFC) 4 x 1 → n'.mem x = Mx x) ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg n' r = g r := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  obtain ⟨n2, c2, pc2, a02, k2, fr2⟩ := uint8Eq_correct n1 (by rw [mem1]; exact C.eq8) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) hp hq (by rw [sp1]; omega)
    (by rw [sp1]; exact F.lowHi (by decide) rfl (by decide) (by decide)) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at a02 fr2
  rw [sp1] at fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, a02, fr2,
    fun r h0 h1 h2 h3 h4 h5 hr => by rw [k2 r h0 h1 h2 h3 h4 h5, r1 r hr]⟩

theorem cmap2_mset : CMAP2 + 0x2DF0 = MSET := by decide
theorem cmap2_cs : CMAP2 + 0xFFFFFC1A = CS2 := by decide
theorem cmap2_stub : CMAP2 + 0xFFFFFC1A + 0x323E = MCS := by decide
theorem cmap2_body : CMAP2 + 0xFFFFFC1A + 0x323E + 8 = MCS + 8 := by decide
theorem cmap2_sca : CMAP2 + 0xFFFFFC1A + 0xFFFFC076 = BitVec.ofNat 32 sliceCtAssignAddress := by decide

set_option maxRecDepth 100000 in
/-- A call to `CtOption<MontyFieldElement<p256>>::map` with both operands in the caller's frame. -/
theorem c2_cmap {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o out x S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P2Code Mx) (C : GdCode Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = CMAP2) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = x)
    {co cx : Nat} (hco : co + 0x21 ≤ N) (hcx : cx + 0x21 ≤ N)
    (eo : out = S + BitVec.ofNat 32 co) (ex : x = S + BitVec.ofNat 32 cx) (acx : cx % 4 = 0)
    (hc : Mx (x + 0x20) = 0 ∨ Mx (x + 0x20) = 1) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      (∀ i, i < 8 → memLoad32 n'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if Mx (x + 0x20) = 1 then memLoad32 Mx (x + BitVec.ofNat 32 (4 * i)) else 0) ∧
      n'.mem (out + 0x20) = Mx (x + 0x20) ∧
      (∀ y, Sep (S + 0xFFFFFF80) 0x80 y 1 → Sep out 0x21 y 1 → n'.mem y = Mx y) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFF80).toNat = S.toNat - 0x80 := F.below 0x80 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFF80) 0x80 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have frS : ∀ cz, cz + 0x21 ≤ N → Sep (S + BitVec.ofNat 32 cz) 0x21 (S + 0xFFFFFF80) 0x80 := fun cz h =>
    (sep_of_le (by rw [hbF, F.at cz (by omega)]; omega) (by rw [F.at cz (by omega)]; omega)).symm
  have E : CM2Env n1.mem CMAP2 (reg n1 sp) out x := by
    rw [sp1, mem1]
    refine ⟨by decide, C.cmap, by rw [cmap2_mset]; exact K.K.mset, by rw [cmap2_cs]; exact K.csel2,
      by rw [cmap2_stub]; exact K.K.stub, by rw [cmap2_body]; exact K.K.body, by rw [cmap2_sca]; exact K.K.sca,
      by omega, by omega, ?_, ?_,
      frC _ _ (by decide) (by decide), frC _ _ (by rw [cmap2_mset]; decide) (by rw [cmap2_mset]; decide),
      frC _ _ (by rw [cmap2_cs]; decide) (by rw [cmap2_cs]; decide), frC _ _ (by rw [cmap2_stub]; decide)
        (by rw [cmap2_stub]; decide), frC _ _ (by rw [cmap2_body]; decide) (by rw [cmap2_body]; decide),
      frC _ _ (by rw [cmap2_sca]; decide) (by rw [cmap2_sca]; decide), ?_, ?_, ?_, ?_, ?_⟩
    · rw [ex, F.at cx (by omega)]; omega
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, cmap2_cs]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, cmap2_body]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo]; exact frS co hco
    · rw [ex]; exact frS cx hcx
  obtain ⟨n2, c2, pc2, sp2, vals, top, k2, fr2⟩ := ctMap256_correct n1 E pc1 rfl (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [mem1]; exact hc) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8)
  rw [mem1] at vals top fr2
  rw [sp1] at fr2 sp2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, vals, top, fr2, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]⟩

/-- A call to `<Choice as ConstantTimeEq>::ct_eq`. -/
theorem c2_cte {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o a b S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (K : P2Code Mx) (C : GdCode Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = CTE)
    (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : g sp = S) (ha0 : g a0 = a) (ha1 : g a1 = b) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧
      reg n' a0 = (if (a ^^^ b) &&& 1 = 0 then 1 else 0) ∧
      (∀ x, Sep (S + 0xFFFFFFEF) 0x11 x 1 → n'.mem x = Mx x) ∧ ∀ q, q ≠ a0 → q ≠ t1 → q ≠ ra → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨n2, c2, pc2, a02, k2, fr2⟩ := choiceCtEq_correct (a := a) (b := b) n1 (by decide) (by rw [mem1]; exact C.cte)
    (by rw [mem1, cte_bb]; exact K.K.bb) pc1 (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) (by rw [sp1]; omega)
    (by rw [sp1]; exact F.lowHi (by decide) rfl (by decide) (by decide))
    (by rw [sp1, cte_bb]; exact F.lowHi (by decide) rfl (by decide) (by decide))
  rw [mem1] at fr2
  rw [sp1] at fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, a02, fr2, fun q h0 h1 hr => by rw [k2 q h0 h1, r1 q hr]⟩

end C3.RV32.Gd
