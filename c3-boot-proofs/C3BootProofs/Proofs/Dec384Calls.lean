import C3BootProofs.Proofs.Dec384Pow
import C3BootProofs.Proofs.P384PtEnv
import C3BootProofs.Image.BootloaderData

/-!
# P-384 point decompression: the data it reads and the calls it makes

The constants `decompress` reads from the image, and wrappers for its calls
to the field arithmetic, from its frame at `S`.
-/

namespace C3.RV32.Dq

open C3.Image

set_option maxRecDepth 20000

abbrev PARAMS : Word := BitVec.ofNat 32 p384ParamsAddress
abbrev EXPA : Word := BitVec.ofNat 32 p384SqrtExpAddress
abbrev CURVEA : Word := BitVec.ofNat 32 p384CurveAAddress

/-- The constants `decompress` reads, where the image puts them. -/
structure DqData (M : Word → BitVec 8) : Prop where
  params : CodeIn M PARAMS p384ParamsData
  exp : CodeIn M EXPA p384SqrtExpData
  ca : CodeIn M CURVEA p384CurveAData
  cb : CodeIn M p3bA p384BData

/-- The word at byte `o + 4i` of `d`, little-endian. -/
def wordAt (d : List Nat) (o i : Nat) : Word :=
  byteAt d (o + 4 * i + 3) ++ byteAt d (o + 4 * i + 2) ++ byteAt d (o + 4 * i + 1) ++ byteAt d (o + 4 * i)

/-- The `n` words of `d` from byte `o`, as a number. -/
def dataVal (d : List Nat) (o : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => dataVal d o n + (wordAt d o n).toNat * 2 ^ (32 * n)

theorem code_word {M : Word → BitVec 8} {addr : Word} {d : List Nat} (h : CodeIn M addr d) (o i : Nat)
    (hi : o + 4 * i + 4 ≤ d.length) : memLoad32 M (addr + BitVec.ofNat 32 (o + 4 * i)) = wordAt d o i := by
  rw [ld_ofNat, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc, h _ (by omega), h _ (by omega),
    h _ (by omega), h _ (by omega)]
  rfl

theorem code_accV {M : Word → BitVec 8} {addr : Word} {d : List Nat} (h : CodeIn M addr d) (o : Nat) :
    ∀ n, o + 4 * n ≤ d.length → accV M (addr + BitVec.ofNat 32 o) n = dataVal d o n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [accV_succ1, code_accV h o n (by omega), add_ofNat_assoc, code_word h o n (by omega)]; rfl

theorem DqData.of {M M' : Word → BitVec 8} {S : Word} (F : DqFrame S) (D : DqData M)
    (h : ∀ x, Sep (S + 0xFFFFFE60) 0xBF0 x 1 → M' x = M x) : DqData M' := by
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
  exact ⟨cd _ _ D.params (by decide) (by decide), cd _ _ D.exp (by decide) (by decide),
    cd _ _ D.ca (by decide) (by decide), cd _ _ D.cb (by decide) (by decide)⟩

theorem DqData.pmod {M : Word → BitVec 8} (D : DqData M) : CodeIn M p3M p384ModulusData := fun i hi => by
  have hb : ∀ i, i < 48 → byteAt p384ParamsData i = byteAt p384ModulusData i := by decide
  rw [show p3M = PARAMS from rfl, D.params i (by have : p384ModulusData.length = 48 := rfl; have : p384ParamsData.length = 156 := rfl; omega),
    hb i (by have : p384ModulusData.length = 48 := rfl; omega)]

set_option exponentiation.threshold 600 in
theorem params_N : dataVal p384ParamsData 0 12 = p384 := by unfold p384; decide

set_option exponentiation.threshold 600 in
theorem params_one : dataVal p384ParamsData 0x30 12 = p3one := by unfold p3one p384; decide

set_option exponentiation.threshold 600 in
theorem params_r2 : dataVal p384ParamsData 0x60 12 < p384 := by unfold p384; decide

theorem params_n0 : wordAt p384ParamsData 0 0 = 0xFFFFFFFF := by decide

set_option exponentiation.threshold 600 in
theorem exp_words : ∀ j, j < 12 → wordAt p384SqrtExpData 0 j = expLimb j := by unfold expLimb sqrtExp p384; decide

theorem DqData.N {M : Word → BitVec 8} (D : DqData M) : accV M PARAMS 12 = p384 := by
  rw [show PARAMS = PARAMS + BitVec.ofNat 32 0 from (add_ofNat_zero _).symm, code_accV D.params 0 12 (by decide), params_N]

theorem DqData.N0 {M : Word → BitVec 8} (D : DqData M) : memLoad32 M PARAMS = 0xFFFFFFFF := by
  rw [show PARAMS = PARAMS + BitVec.ofNat 32 (0 + 4 * 0) from (add_ofNat_zero _).symm, code_word D.params 0 0 (by decide),
    params_n0]

theorem DqData.one {M : Word → BitVec 8} (D : DqData M) : accV M (PARAMS + BitVec.ofNat 32 0x30) 12 = p3one := by
  rw [code_accV D.params 0x30 12 (by decide), params_one]

theorem DqData.r2lt {M : Word → BitVec 8} (D : DqData M) : accV M (PARAMS + BitVec.ofNat 32 0x60) 12 < accV M PARAMS 12 := by
  rw [code_accV D.params 0x60 12 (by decide), D.N]; exact params_r2

theorem DqData.ex {M : Word → BitVec 8} (D : DqData M) (j : Nat) (hj : j < 12) :
    memLoad32 M (EXPA + BitVec.ofNat 32 (0 + 4 * j)) = expLimb j := by
  rw [code_word D.exp 0 j (by have : p384SqrtExpData.length = 48 := rfl; omega), exp_words j hj]

/-- A stack region below the frame is apart from the constants. -/
theorem DqFrame.lowData {S : Word} (F : DqFrame S) {k : Word} {c : Nat} (hc : c ≤ 0x1A0)
    (hk : (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 - c) = k) {b : Word} {len : Nat}
    (hb : (img% dataWindowAddress) ≤ b.toNat) (hb2 : b.toNat + len ≤ (img% dataWindowAddress + dataWindowSize)) : Sep (S + k) c b len := by
  have h1 := F.dsep.sub (c := 0x1A0 - c) (l := c) (by omega)
  have h2 := h1.subR (c := b.toNat - (img% dataWindowAddress)) (l := len) (by omega)
  rw [BitVec.add_assoc, hk] at h2
  rwa [show (img% dataWindowAddress : Word) + BitVec.ofNat 32 (b.toNat - (img% dataWindowAddress)) = b by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (img% dataWindowAddress : Word).toNat = (img% dataWindowAddress) from rfl]
    have := b.isLt; omega] at h2

/-- A buffer in the frame is apart from the constants. -/
theorem DqFrame.bufData {S : Word} (F : DqFrame S) {c n : Nat} (h : c + n ≤ 0xA50) {b : Word} {len : Nat}
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

abbrev P3MUL : Word := BitVec.ofNat 32 p384MulAddress
theorem p3mul_mm : P3MUL + 0xFFFFF45E = MM := by decide

set_option maxRecDepth 100000 in
/-- A call to `ConstMontyForm<p384::FieldParams>::mul` from `decompress`: the
12 words at `out` become the Montgomery product of those at `xp` and `yp`. -/
theorem dq_p3mul {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o out xp yp S : Word}
    (s : St Mx DP n off g) (C : DqCode Mx) (D : DqData Mx) (F : DqFrame S)
    (h1 : fetchRel p384DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DP + BitVec.ofNat 32 off + imm + o = P3MUL) (he8 : (DP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = xp) (ha2 : g a2 = yp)
    {co : Nat} (hco : co + 48 ≤ 0xA50) (eo : out = S + BitVec.ofNat 32 co) (aco : co % 4 = 0)
    (sX : Sep xp 48 (S + 0xFFFFFF10) 0xF0) (aX : xp.toNat % 4 = 0)
    (sY : Sep yp 48 (S + 0xFFFFFF10) 0xF0) (aY : yp.toNat % 4 = 0)
    (hY : limbVal (wordsAt Mx yp 12) < p384) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' (off + 8) (reg n') ∧
      limbVal (wordsAt n'.mem out 12) = p3fm (limbVal (wordsAt Mx xp 12)) (limbVal (wordsAt Mx yp 12)) ∧
      (∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 → Sep out 48 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFF10).toNat = S.toNat - 0xF0 := F.below 0xF0 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFF10) 0xF0 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have E : P3MEnv n1.mem P3MUL (reg n1 sp) out xp yp := by
    rw [sp1, mem1]
    refine ⟨by decide, C.p3mul, D.pmod, ?_⟩
    rw [p3mul_mm]
    refine ⟨by decide, C.mm, by rw [mm_mset]; exact C.mset, by rw [mm_bsub]; exact C.bsub, by rw [mm_sel]; exact C.sel,
      by rw [mm_stub]; exact C.stub, by rw [mm_body]; exact C.body, by omega, by omega, ?_, aX, aY, by decide, ?_,
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

abbrev P3ADD : Word := BitVec.ofNat 32 p384AddAddress
theorem p3add_mset : P3ADD + 0x144C2 = MSET := by decide
theorem p3add_bsub : p3Bsub P3ADD = BSUB := by decide
theorem p3add_stub : P3ADD + 0x1452A = MCS := by decide
theorem p3add_body : P3ADD + 0x14532 = MCS + 8 := by decide

/-- A call to `ConstMontyForm<p384::FieldParams>::add` from `decompress`. -/
theorem dq_p3add {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o out lp rp S : Word}
    (s : St Mx DP n off g) (C : DqCode Mx) (D : DqData Mx) (F : DqFrame S)
    (h1 : fetchRel p384DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DP + BitVec.ofNat 32 off + imm + o = P3ADD) (he8 : (DP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = lp) (ha2 : g a2 = rp)
    {co : Nat} (hco : co + 48 ≤ 0xA50) (eo : out = S + BitVec.ofNat 32 co) (aco : co % 4 = 0)
    (sL : Sep lp 48 (S + 0xFFFFFF4C) 0xB4) (aL : lp.toNat % 4 = 0)
    (sR : Sep rp 48 (S + 0xFFFFFF4C) 0xB4) (aR : rp.toNat % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' (off + 8) (reg n') ∧
      limbVal (wordsAt n'.mem out 12) = p3AddRes (limbVal (wordsAt Mx lp 12)) (limbVal (wordsAt Mx rp 12)) ∧
      (∀ x, Sep (S + 0xFFFFFF4C) 0xB4 x 1 → Sep out 48 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 → q ≠ ra →
        reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFF4C).toNat = S.toNat - 0xB4 := F.below 0xB4 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFF4C) 0xB4 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have E : P3Env n1.mem P3ADD (reg n1 sp) out lp rp := by
    rw [sp1, mem1]
    refine ⟨by decide, C.p3add, by rw [p3add_mset]; exact C.mset, by rw [p3add_bsub]; exact C.bsub,
      by rw [p3add_stub]; exact C.stub, by rw [p3add_body]; exact C.body, D.pmod, by omega, by omega, ?_, aL, aR, ?_,
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

abbrev CSEL : Word := BitVec.ofNat 32 condSelect384Address
theorem csel_stub : CSEL + 0x101A = MCS := by decide
theorem csel_body : CSEL + 0x101A + 8 = MCS + 8 := by decide
theorem csel_cta : CSEL + 0x2EC = BitVec.ofNat 32 uint12CtAssignAddress := by decide
theorem csel_sca : CSEL + 0x2EC + 0xFFFF9B66 = BitVec.ofNat 32 sliceCtAssignAddress := by decide

/-- A call to `ConstMontyForm<p384::FieldParams>::conditional_select` from
`decompress`, with all three operands in its frame. -/
theorem dq_csel {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o out a b c S : Word}
    (s : St Mx DP n off g) (C : DqCode Mx) (F : DqFrame S)
    (h1 : fetchRel p384DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DP + BitVec.ofNat 32 off + imm + o = CSEL) (he8 : (DP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = a) (ha2 : g a2 = b) (ha3 : g a3 = c) (hc : c = 0 ∨ c = 1)
    {co ca cb : Nat} (hco : co + 48 ≤ 0xA50) (hca : ca + 48 ≤ 0xA50) (hcb : cb + 48 ≤ 0xA50)
    (eo : out = S + BitVec.ofNat 32 co) (ea : a = S + BitVec.ofNat 32 ca) (eb : b = S + BitVec.ofNat 32 cb)
    (acb : cb % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' (off + 8) (reg n') ∧
      (∀ i, i < 12 → memLoad32 n'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 Mx (b + BitVec.ofNat 32 (4 * i)) else memLoad32 Mx (a + BitVec.ofNat 32 (4 * i))) ∧
      (∀ x, Sep (S + 0xFFFFFFA0) 0x60 x 1 → Sep out 48 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFFA0).toNat = S.toNat - 0x60 := F.below 0x60 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFFA0) 0x60 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have frS : ∀ cz, cz + 48 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 cz) 48 (S + 0xFFFFFFA0) 0x60 := fun cz h =>
    (sep_of_le (by rw [hbF, F.at cz (by omega)]; omega) (by rw [F.at cz (by omega)]; omega)).symm
  have E : CSEnv n1.mem CSEL (reg n1 sp) out a b := by
    rw [sp1, mem1]
    refine ⟨by decide, C.csel, by rw [csel_stub]; exact C.stub, by rw [csel_body]; exact C.body,
      by rw [csel_cta]; exact C.cta, by rw [csel_sca]; exact C.sca, by omega, by omega, ?_, ?_, ?_,
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

abbrev CMAP : Word := BitVec.ofNat 32 ctMap384Address
theorem cmap_mset : CMAP + 0xEC6 = MSET := by decide
theorem cmap_cs : CMAP + 0xFFFFFF14 = CSEL := by decide
theorem cmap_stub : CMAP + 0xFFFFFF14 + 0x101A = MCS := by decide
theorem cmap_body : CMAP + 0xFFFFFF14 + 0x101A + 8 = MCS + 8 := by decide
theorem cmap_cta : CMAP + 0xFFFFFF14 + 0x2EC = BitVec.ofNat 32 uint12CtAssignAddress := by decide
theorem cmap_sca : CMAP + 0xFFFFFF14 + 0x2EC + 0xFFFF9B66 = BitVec.ofNat 32 sliceCtAssignAddress := by decide

/-- A call to `CtOption<MontyFieldElement<p384>>::map` from `decompress`. -/
theorem dq_cmap {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o out x S : Word}
    (s : St Mx DP n off g) (C : DqCode Mx) (F : DqFrame S)
    (h1 : fetchRel p384DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DP + BitVec.ofNat 32 off + imm + o = CMAP) (he8 : (DP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = x)
    {co cx : Nat} (hco : co + 0x31 ≤ 0xA50) (hcx : cx + 0x31 ≤ 0xA50)
    (eo : out = S + BitVec.ofNat 32 co) (ex : x = S + BitVec.ofNat 32 cx) (acx : cx % 4 = 0)
    (hc : Mx (x + 0x30) = 0 ∨ Mx (x + 0x30) = 1) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' (off + 8) (reg n') ∧
      (∀ i, i < 12 → memLoad32 n'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if Mx (x + 0x30) = 1 then memLoad32 Mx (x + BitVec.ofNat 32 (4 * i)) else 0) ∧
      n'.mem (out + 0x30) = Mx (x + 0x30) ∧
      (∀ y, Sep (S + 0xFFFFFF60) 0xA0 y 1 → Sep out 0x31 y 1 → n'.mem y = Mx y) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFF60).toNat = S.toNat - 0xA0 := F.below 0xA0 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFF60) 0xA0 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have frS : ∀ cz, cz + 0x31 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 cz) 0x31 (S + 0xFFFFFF60) 0xA0 := fun cz h =>
    (sep_of_le (by rw [hbF, F.at cz (by omega)]; omega) (by rw [F.at cz (by omega)]; omega)).symm
  have E : CMEnv n1.mem CMAP (reg n1 sp) out x := by
    rw [sp1, mem1]
    refine ⟨by decide, C.cmap, by rw [cmap_mset]; exact C.mset, by rw [cmap_cs]; exact C.csel,
      by rw [cmap_stub]; exact C.stub, by rw [cmap_body]; exact C.body, by rw [cmap_cta]; exact C.cta,
      by rw [cmap_sca]; exact C.sca, by omega, by omega, ?_, ?_,
      frC _ _ (by decide) (by decide), frC _ _ (by rw [cmap_mset]; decide) (by rw [cmap_mset]; decide),
      frC _ _ (by rw [cmap_cs]; decide) (by rw [cmap_cs]; decide), frC _ _ (by rw [cmap_stub]; decide)
        (by rw [cmap_stub]; decide), frC _ _ (by rw [cmap_body]; decide) (by rw [cmap_body]; decide),
      frC _ _ (by rw [cmap_cta]; decide) (by rw [cmap_cta]; decide), frC _ _ (by rw [cmap_sca]; decide)
        (by rw [cmap_sca]; decide), ?_, ?_, ?_, ?_, ?_⟩
    · rw [ex, F.at cx (by omega)]; omega
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, cmap_cs]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, cmap_body]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo]; exact frS co hco
    · rw [ex]; exact frS cx hcx
  obtain ⟨n2, c2, pc2, sp2, vals, top, k2, fr2⟩ := ctMap384_correct n1 E pc1 rfl (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [mem1]; exact hc) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8)
  rw [mem1] at vals top fr2
  rw [sp1] at fr2 sp2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, vals, top, fr2, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]⟩

abbrev NEG : Word := BitVec.ofNat 32 p384NegAddress
theorem neg_nz : NEG + 0x130AC = BitVec.ofNat 32 uint12IsNonzeroAddress := by decide
theorem neg_ref : NEG + 0x3F2 = BitVec.ofNat 32 uintRefIsNonzeroAddress := by decide
theorem neg_mset : NEG + 0x13D7C = MSET := by decide
theorem neg_bsub : ngBsub NEG = BSUB := by decide
theorem neg_stub : NEG + 0x13DE4 = MCS := by decide
theorem neg_body : NEG + 0x13DEC = MCS + 8 := by decide

/-- A call to `ConstMontyForm<p384::FieldParams>::neg` from `decompress`. -/
theorem dq_neg {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o out xp S : Word}
    (s : St Mx DP n off g) (C : DqCode Mx) (D : DqData Mx) (F : DqFrame S)
    (h1 : fetchRel p384DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DP + BitVec.ofNat 32 off + imm + o = NEG) (he8 : (DP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = xp)
    {co cx : Nat} (hco : co + 48 ≤ 0xA50) (hcx : cx + 48 ≤ 0xA50)
    (eo : out = S + BitVec.ofNat 32 co) (ex : xp = S + BitVec.ofNat 32 cx) (aco : co % 4 = 0) (acx : cx % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' (off + 8) (reg n') ∧
      accV n'.mem out 12 = (if accV Mx xp 12 = 0 then 0 else (p384 + 2 ^ 384 - accV Mx xp 12) % 2 ^ 384) ∧
      (∀ x, Sep (S + 0xFFFFFFAC) 0x54 x 1 → Sep out 48 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, ngKeep q = true → q ≠ ra → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFFAC).toNat = S.toNat - 0x54 := F.below 0x54 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFFAC) 0x54 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have frS : ∀ cz, cz + 48 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 cz) 48 (S + 0xFFFFFFAC) 0x54 := fun cz h =>
    (sep_of_le (by rw [hbF, F.at cz (by omega)]; omega) (by rw [F.at cz (by omega)]; omega)).symm
  have E : NgEnv n1.mem NEG (reg n1 sp) out xp := by
    rw [sp1, mem1]
    refine ⟨by decide, C.neg, by rw [neg_nz]; exact C.nz12, by rw [neg_ref]; exact C.refnz, by rw [neg_mset]; exact C.mset,
      by rw [neg_bsub]; exact C.bsub, by rw [neg_stub]; exact C.stub, by rw [neg_body]; exact C.body, D.pmod,
      by omega, by omega, ?_, ?_, ?_, frC _ _ (by decide) (by decide), frC _ _ (by rw [neg_nz]; decide) (by rw [neg_nz]; decide),
      frC _ _ (by rw [neg_ref]; decide) (by rw [neg_ref]; decide), frC _ _ (by rw [neg_mset]; decide) (by rw [neg_mset]; decide),
      frC _ _ (by rw [neg_bsub]; decide) (by rw [neg_bsub]; decide), frC _ _ (by rw [neg_stub]; decide) (by rw [neg_stub]; decide),
      frC _ _ (by rw [neg_body]; decide) (by rw [neg_body]; decide),
      F.lowData (c := 0x54) (by decide) rfl (by decide) (by decide), ?_, ?_, ?_, ?_⟩
    · rw [eo, F.at co (by omega)]; omega
    · rw [ex, F.at cx (by omega)]; omega
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, neg_body]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo]; exact frS co hco
    · rw [ex]; exact frS cx hcx
  obtain ⟨n2, c2, pc2, sp2, k2, hv2, fr2⟩ := p384Neg_correct n1 E pc1 rfl (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at hv2 fr2
  rw [sp1] at fr2 sp2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, hv2, fr2, sp2, fun q hq hr => by rw [k2 q hq, r1 q hr]⟩

abbrev SQM : Word := BitVec.ofNat 32 sqMont12Address
theorem sqm_mset : SQM + 0xE5E = MSET := by decide
theorem sqm_bsub : sqBsub SQM = BSUB := by decide
theorem sqm_sel : SQM + 0xFFFFF4E0 = SEL := by decide
theorem sqm_stub : SQM + 0xEC6 = MCS := by decide
theorem sqm_body : SQM + 0xECE = MCS + 8 := by decide

/-- A call to `square_montgomery_form::<12>` from `decompress`, with the
modulus `N` at `np` in its frame and `K = 1`. -/
theorem dq_sqm {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o out xp np S : Word}
    (s : St Mx DP n off g) (C : DqCode Mx) (F : DqFrame S)
    (h1 : fetchRel p384DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DP + BitVec.ofNat 32 off + imm + o = SQM) (he8 : (DP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = xp) (ha2 : g a2 = np) (ha3 : g a3 = 1)
    {co cx cn : Nat} (hco : co + 48 ≤ 0xA50) (hcx : cx + 48 ≤ 0xA50) (hcn : cn + 48 ≤ 0xA50)
    (eo : out = S + BitVec.ofNat 32 co) (ex : xp = S + BitVec.ofNat 32 cx) (en : np = S + BitVec.ofNat 32 cn)
    (aco : co % 4 = 0) (acx : cx % 4 = 0) (acn : cn % 4 = 0)
    (hN0 : memLoad32 Mx np = 0xFFFFFFFF) (hN : accV Mx np 12 = p384) (hX : accV Mx xp 12 < p384) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' (off + 8) (reg n') ∧
      accV n'.mem out 12 = p3fm (accV Mx xp 12) (accV Mx xp 12) ∧
      (∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 → Sep out 48 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFF10).toNat = S.toNat - 0xF0 := F.below 0xF0 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFF10) 0xF0 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have frS : ∀ cz, cz + 48 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 cz) 48 (S + 0xFFFFFF10) 0xF0 := fun cz h =>
    (sep_of_le (by rw [hbF, F.at cz (by omega)]; omega) (by rw [F.at cz (by omega)]; omega)).symm
  have E : SQEnv n1.mem SQM (reg n1 sp) out xp np := by
    rw [sp1, mem1]
    refine ⟨by decide, C.sqm, by rw [sqm_mset]; exact C.mset, by rw [sqm_bsub]; exact C.bsub, by rw [sqm_sel]; exact C.sel,
      by rw [sqm_stub]; exact C.stub, by rw [sqm_body]; exact C.body, by omega, by omega, ?_, ?_, ?_, ?_,
      frC _ _ (by decide) (by decide), frC _ _ (by rw [sqm_mset]; decide) (by rw [sqm_mset]; decide),
      frC _ _ (by rw [sqm_bsub]; decide) (by rw [sqm_bsub]; decide), frC _ _ (by rw [sqm_sel]; decide) (by rw [sqm_sel]; decide),
      frC _ _ (by rw [sqm_stub]; decide) (by rw [sqm_stub]; decide), frC _ _ (by rw [sqm_body]; decide)
        (by rw [sqm_body]; decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eo, F.at co (by omega)]; omega
    · rw [ex, F.at cx (by omega)]; omega
    · rw [en, F.at cn (by omega)]; omega
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo]; exact frS co hco
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, sqm_sel]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, sqm_body]; exact F.sepHi hco (by decide) (by decide)
    · rw [ex]; exact frS cx hcx
    · rw [en]; exact frS cn hcn
  obtain ⟨n2, c2, pc2, sp2, hlt, hcg, fr2, k2⟩ := sqrMont12_correct (K := 1) n1 E pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) rfl (by rw [mem1, hN0]; decide) (by rw [mem1, hN]; exact hX)
  rw [mem1, hN] at hlt hcg
  rw [mem1] at fr2
  rw [sp1] at fr2 sp2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, p3_mont hlt hcg, fr2, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]⟩

abbrev RT : Word := BitVec.ofNat 32 p384FieldRetrieveAddress
theorem rt_mr : RT + 0xFFFFFF24 = BitVec.ofNat 32 montRetrieve12Address := by decide
theorem rt_mset : RT + 0xFFFFFF24 + 0xA30 = MSET := by decide
theorem rt_stub : RT + 0xFFFFFF24 + 0xA98 = MCS := by decide
theorem rt_body : RT + 0xFFFFFF24 + 0xAA0 = MCS + 8 := by decide

/-- A call to `ConstMontyForm<p384::FieldParams>::retrieve` from `decompress`. -/
theorem dq_rt {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o out xp S : Word}
    (s : St Mx DP n off g) (C : DqCode Mx) (D : DqData Mx) (F : DqFrame S)
    (h1 : fetchRel p384DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DP + BitVec.ofNat 32 off + imm + o = RT) (he8 : (DP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = xp)
    {co cx : Nat} (hco : co + 48 ≤ 0xA50) (hcx : cx + 48 ≤ 0xA50)
    (eo : out = S + BitVec.ofNat 32 co) (ex : xp = S + BitVec.ofNat 32 cx) (aco : co % 4 = 0) (acx : cx % 4 = 0)
    (hX : accV Mx xp 12 < p384) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' (off + 8) (reg n') ∧
      accV n'.mem out 12 = p3fm (accV Mx xp 12) 1 ∧
      (∀ x, Sep (S + 0xFFFFFFB0) 0x50 x 1 → Sep out 48 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFFB0).toNat = S.toNat - 0x50 := F.below 0x50 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFFB0) 0x50 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have frS : ∀ cz, cz + 48 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 cz) 48 (S + 0xFFFFFFB0) 0x50 := fun cz h =>
    (sep_of_le (by rw [hbF, F.at cz (by omega)]; omega) (by rw [F.at cz (by omega)]; omega)).symm
  have E : P3REnv n1.mem RT (reg n1 sp) out xp := by
    rw [sp1, mem1]
    refine ⟨by decide, C.rt, D.pmod, ?_⟩
    refine ⟨by decide, by rw [rt_mr]; exact C.mr, by rw [rt_mset]; exact C.mset, by rw [rt_stub]; exact C.stub,
      by rw [rt_body]; exact C.body, by omega, by omega, ?_, ?_, by decide, ?_,
      frC _ _ (by rw [rt_mr]; decide) (by rw [rt_mr]; decide), frC _ _ (by rw [rt_mset]; decide) (by rw [rt_mset]; decide),
      frC _ _ (by rw [rt_stub]; decide) (by rw [rt_stub]; decide), frC _ _ (by rw [rt_body]; decide) (by rw [rt_body]; decide),
      ?_, ?_, ?_, ?_, (F.lowData (c := 0x50) (by decide) rfl (by decide) (by decide)).symm⟩
    · rw [eo, F.at co (by omega)]; omega
    · rw [ex, F.at cx (by omega)]; omega
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo]; exact frS co hco
    · rw [eo, rt_mr]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, rt_body]; exact F.sepHi hco (by decide) (by decide)
    · rw [ex]; exact frS cx hcx
  obtain ⟨n2, c2, pc2, sp2, k2, hv2, fr2⟩ := p384FieldRetrieve_correct n1 E pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) rfl
    (by rw [mem1]; exact hX)
  rw [mem1] at hv2 fr2
  rw [sp1] at fr2 sp2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, hv2, fr2, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]⟩

/-- A stack region below the frame is apart from the code. -/
theorem DqFrame.lowHi {S : Word} (F : DqFrame S) {k : Word} {c : Nat} (hc : c ≤ 0x1A0) (hk : k.toNat = 2 ^ 32 - c)
    {b : Word} {len : Nat} (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + len ≤ 2 ^ 32) : Sep (S + k) c b len :=
  sep_of_le (by rw [BitVec.toNat_add, hk]; have := F.lo; have := F.hi; have := S.isLt; omega) hl

/-- A call to `Uint<12>::eq` from `decompress`. -/
theorem dq_eq12 {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o p q S : Word}
    (s : St Mx DP n off g) (C : DqCode Mx) (F : DqFrame S)
    (h1 : fetchRel p384DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DP + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 uint12EqAddress)
    (he8 : (DP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = p) (ha1 : g a1 = q) (hp : p.toNat % 4 = 0) (hq : q.toNat % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' (off + 8) (reg n') ∧
      reg n' a0 = (if ∀ i : Nat, i < 12 → memLoad32 Mx (p + BitVec.ofNat 32 (4 * i)) =
        memLoad32 Mx (q + BitVec.ofNat 32 (4 * i)) then 1 else 0) ∧
      (∀ x, Sep (S + 0xFFFFFFFC) 4 x 1 → n'.mem x = Mx x) ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg n' r = g r := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hb4 : (S + 0xFFFFFFFC).toNat = S.toNat - 4 := F.below 4 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  obtain ⟨n2, c2, pc2, a02, k2, fr2⟩ := uint12Eq_correct n1 (by rw [mem1]; exact C.eq12) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) hp hq (by rw [sp1]; omega)
    (by rw [sp1]; exact F.lowHi (by decide) rfl (by decide) (by decide)) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at a02 fr2
  rw [sp1] at fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, a02, fr2,
    fun r h0 h1 h2 h3 h4 h5 hr => by rw [k2 r h0 h1 h2 h3 h4 h5, r1 r hr]⟩

/-- A call to `black_box::<u8>` from `decompress`. -/
theorem dq_bb {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o S : Word}
    (s : St Mx DP n off g) (C : DqCode Mx) (F : DqFrame S)
    (h1 : fetchRel p384DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DP + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 blackBoxU8Address)
    (he8 : (DP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : g sp = S) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' (off + 8) (reg n') ∧
      reg n' a0 = ((g a0).extractLsb' 0 8).zeroExtend 32 ∧
      (∀ x, Sep (S + 0xFFFFFFFF) 1 x 1 → n'.mem x = Mx x) ∧ ∀ q, q ≠ a0 → q ≠ ra → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hb1 : (S + 0xFFFFFFFF).toNat = S.toNat - 1 := F.below 1 (by decide) (by decide)
  have hSl := F.lo; have hSh := F.hi
  obtain ⟨n2, c2, pc2, a02, k2, fr2⟩ := blackBoxU8_correct n1 (by rw [mem1]; exact C.bb) pc1
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
    (by rw [sp1]; exact F.lowHi (by decide) rfl (by decide) (by decide))
  rw [mem1] at fr2
  rw [sp1] at fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [a02, r1 a0 (by decide)], fr2,
    fun q h0 hr => by rw [k2 q h0, r1 q hr]⟩

theorem cte_bb : BitVec.ofNat 32 choiceCtEqAddress + 0x9A7E = BitVec.ofNat 32 blackBoxU8Address := by decide

/-- A call to `<Choice as ConstantTimeEq>::ct_eq` from `decompress`. -/
theorem dq_cte {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o a b S : Word}
    (s : St Mx DP n off g) (C : DqCode Mx) (F : DqFrame S)
    (h1 : fetchRel p384DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DP + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 choiceCtEqAddress)
    (he8 : (DP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : g sp = S) (ha0 : g a0 = a) (ha1 : g a1 = b) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' (off + 8) (reg n') ∧
      reg n' a0 = (if (a ^^^ b) &&& 1 = 0 then 1 else 0) ∧
      (∀ x, Sep (S + 0xFFFFFFEF) 0x11 x 1 → n'.mem x = Mx x) ∧ ∀ q, q ≠ a0 → q ≠ t1 → q ≠ ra → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hb1 : (S + 0xFFFFFFEF).toNat = S.toNat - 0x11 := F.below 0x11 (by decide) (by decide)
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨n2, c2, pc2, a02, k2, fr2⟩ := choiceCtEq_correct (a := a) (b := b) n1 (by decide) (by rw [mem1]; exact C.cte)
    (by rw [mem1, cte_bb]; exact C.bb) pc1 (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) (by rw [sp1]; omega)
    (by rw [sp1]; exact F.lowHi (by decide) rfl (by decide) (by decide))
    (by rw [sp1, cte_bb]; exact F.lowHi (by decide) rfl (by decide) (by decide))
  rw [mem1] at fr2
  rw [sp1] at fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, a02, fr2, fun q h0 h1 hr => by rw [k2 q h0 h1, r1 q hr]⟩

/-- A call to `<p384::FieldElement as PrimeField>::from_repr` from
`decompress`, with the result at `S + co` and the 48 input bytes at `inp`. -/
theorem dq_frp {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o out inp S : Word}
    (s : St Mx DP n off g) (C : DqCode Mx) (D : DqData Mx) (F : DqFrame S)
    (h1 : fetchRel p384DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DP + BitVec.ofNat 32 off + imm + o = FRP) (he8 : (DP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = inp)
    {co : Nat} (hco : co + 49 ≤ 0xA50) (eo : out = S + BitVec.ofNat 32 co)
    (sI : Sep inp 48 (S + 0xFFFFFE60) 0x1A0) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' (off + 8) (reg n') ∧
      (beNat (memBytes Mx inp 48) < p384 →
        n'.mem (out + 0x30) = 1 ∧ accV n'.mem out 12 < p384 ∧
        accV n'.mem out 12 * 2 ^ 384 % p384 = beNat (memBytes Mx inp 48) * accV Mx (PARAMS + BitVec.ofNat 32 0x60) 12 % p384) ∧
      (p384 ≤ beNat (memBytes Mx inp 48) → n'.mem (out + 0x30) = 0 ∧ accV n'.mem out 12 = 0) ∧
      (∀ x, Sep (S + 0xFFFFFE60) 0x1A0 x 1 → Sep out 49 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have E : FRPEnv n1.mem := by
    rw [mem1]
    exact ⟨C.frp, C.za, C.mset, C.stub, C.body, C.bsub, C.refnz, C.mm, C.sel, C.bb, C.csel, C.cta, C.sca, D.N0,
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

end C3.RV32.Dq
