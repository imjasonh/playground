import C3BootProofs.Proofs.Pv384At
import C3BootProofs.Proofs.Fs384Main
import C3BootProofs.Proofs.ByteCompare
import C3BootProofs.Proofs.ScalarFromSlice384
import C3BootProofs.Proofs.ScalarIsZero

/-!
# `p384_verify_prehash`: its callees

Wrappers that run one call from `p384_verify_prehash` and state its result
in the caller's terms.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

/-- A frame inside a frame: a callee's frame at offset `c` of the caller's. -/
theorem _root_.C3.RV32.P3.Fr.sub {S : Word} {N : Nat} (F : Fr S N) {c n : Nat} (hc : c % 16 = 0) (h : c + n ≤ N) :
    Fr (S + BitVec.ofNat 32 c) n := by
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  refine ⟨by rw [F.at c (by omega)]; omega, by rw [F.at c (by omega)]; omega, by rw [F.at c (by omega)]; omega, ?_⟩
  have := F.dsep.sub (c := c) (l := n + 0x1A0) (by omega)
  rwa [BitVec.add_assoc, BitVec.add_comm (0xFFFFFE60 : Word), ← BitVec.add_assoc] at this

abbrev ISR : Word := BitVec.ofNat 32 inScalarRangeAddress

/-- A call to `in_scalar_range`, which reads its two byte strings and
writes nothing. -/
theorem c_isr {base : Word} {code : List Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o x y : Word} {k k' : Nat}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (hc : CodeIn Mx ISR inScalarRangeCode)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = ISR) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : g a0 = x) (ha1 : g a1 = BitVec.ofNat 32 k) (ha2 : g a2 = y) (ha3 : g a3 = BitVec.ofNat 32 k')
    (hk : k < 2 ^ 32) (hk' : k' < 2 ^ 32) :
    ∃ n', Steps n n' ∧ St Mx base n' (off + 8) (reg n') ∧
      reg n' a0 = (if inScalarRange (memBytes Mx x k) (memBytes Mx y k') then 1 else 0) ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg n' r = g r := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, pc2, a02, k2, mem2⟩ := inScalarRange_correct n1 (x := x) (o := y) (n := k) (n' := k') (by decide) (by rw [mem1]; exact hc) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3) hk hk'
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at a02
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], by rw [mem2, mem1], fun _ => rfl⟩, a02,
    fun r h0 h1 h2 h3 h4 h5 hr => by rw [k2 r h0 h1 h2 h3 h4 h5, r1 r hr]⟩

abbrev SZ : Word := BitVec.ofNat 32 scalarIsZero384Address

/-- The code `p384_verify_prehash` runs, above 0x40000000. -/
structure PvCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M PV p384VerifyPrehashCode
  K : P3Code M
  fs : Fs.FsCode M
  isr : CodeIn M ISR inScalarRangeCode
  bf : CodeIn M BF scalarFromSlice384Code
  fb : FBEnv M
  sz : CodeIn M SZ scalarIsZero384Code

theorem _root_.C3.RV32.FBEnv.hi {M M' : Word → BitVec 8} (E : FBEnv M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    FBEnv M' :=
  ⟨codeHi E.cod (by decide) (by decide) h, codeHi E.ms (by decide) (by decide) h, codeHi E.fl (by decide) (by decide) h,
    codeHi E.cs (by decide) (by decide) h, codeHi E.cb (by decide) (by decide) h⟩

theorem PvCode.hi {M M' : Word → BitVec 8} (C : PvCode M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    PvCode M' :=
  ⟨codeHi C.self (by decide) (by decide) h, C.K.hi h, C.fs.hi h, codeHi C.isr (by decide) (by decide) h,
    codeHi C.bf (by decide) (by decide) h, C.fb.hi h, codeHi C.sz (by decide) (by decide) h⟩

/-- The constants `p384_verify_prehash` reads, between `dataWindowAddress` and 0x3FCC4E60. -/
structure PvData (M : Word → BitVec 8) : Prop where
  D : P3Data M
  ord : CodeIn M BZO b2sOrder384Data

/-- A constant between `dataWindowAddress` and `dataWindowAddress + dataWindowSize` survives a change to memory
that keeps outside a frame. -/
theorem _root_.C3.RV32.P3.Fr.dataIn {S : Word} {N : Nat} (F : Fr S N) {M M' : Word → BitVec 8}
    (h : ∀ x, Sep (S + 0xFFFFFE60) (N + 0x1A0) x 1 → M' x = M x) {b : Word} {d : List Nat} (hc : CodeIn M b d)
    (h1 : (img% dataWindowAddress) ≤ b.toNat) (h2 : b.toNat + d.length ≤ (img% dataWindowAddress + dataWindowSize)) : CodeIn M' b d := fun i hi => by
  have hd := F.dsep
  rw [h _ (hd.subR (c := (b + BitVec.ofNat 32 i).toNat - (img% dataWindowAddress)) (l := 1) (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) |> fun s => by
      rwa [show (img% dataWindowAddress : Word) + BitVec.ofNat 32 ((b + BitVec.ofNat 32 i).toNat - (img% dataWindowAddress)) =
        b + BitVec.ofNat 32 i from by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat,
            show (img% dataWindowAddress : Word).toNat = (img% dataWindowAddress) from rfl]
          omega] at s)]
  exact hc i hi

theorem PvData.of {M M' : Word → BitVec 8} {S : Word} {N : Nat} (F : Fr S N) (D : PvData M)
    (h : ∀ x, Sep (S + 0xFFFFFE60) (N + 0x1A0) x 1 → M' x = M x) : PvData M' :=
  ⟨D.D.of F h, F.dataIn h D.ord (by decide) (by decide)⟩

set_option exponentiation.threshold 600 in
theorem bzo_val : dataVal b2sOrder384Data 0 12 = n384 := by unfold n384; decide

theorem PvData.n {M : Word → BitVec 8} (D : PvData M) : accV M BZO 12 = n384 := by
  rw [show BZO = BZO + BitVec.ofNat 32 0 from rfl, code_accV D.ord 0 12 (by decide), bzo_val]

/-- The `k` bytes below `S` are apart from a region of the frame. -/
theorem _root_.C3.RV32.P3.Fr.lowN {S : Word} {N : Nat} (F : Fr S N) {k : Nat} (hk : 0 < k) (hk' : k ≤ 0x1A0) {c n : Nat}
    (h : c + n ≤ N) : Sep (S + BitVec.ofNat 32 c) n (S + BitVec.ofNat 32 (2 ^ 32 - k)) k := by
  have hb : (S + BitVec.ofNat 32 (2 ^ 32 - k)).toNat = S.toNat - k := F.below k hk hk'
  have := F.lo; have := F.hi
  exact (sep_of_le (by rw [hb, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm

set_option maxRecDepth 100000 in
/-- A call to `ScalarValue::<NistP384>::from_slice`. -/
theorem c_bf {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o out b S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (C : PvCode Mx) (D : PvData Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = BF) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = b) {co : Nat} (hco : co + 52 ≤ N)
    (eo : out = S + BitVec.ofNat 32 co) (aco : co % 4 = 0) (sB : Sep b 48 (S + 0xFFFFFF10) 0xF0) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧ reg n' sp = S ∧
      (∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q) ∧
      (beNat (memBytes Mx b 48) < n384 → memLoad32 n'.mem out = 0 ∧
        accV n'.mem (out + 4) 12 = beNat (memBytes Mx b 48)) ∧
      (n384 ≤ beNat (memBytes Mx b 48) → memLoad32 n'.mem out = 1) ∧
      ∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 → Sep out 52 x 1 → n'.mem x = Mx x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  obtain ⟨n2, c2, pc2, sp2, k2, ok2, bad2, fr2⟩ := scalarFromSlice384_correct n1 (sp0 := S) (out := out) (b := b)
    (by rw [mem1]; exact ⟨C.bf, C.fb, C.K.bsub, C.K.refnz, C.K.bb, D.n⟩) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (by rw [regs1]; simp +decide [upd])
    (even_clear _ he8) sp1 (by omega) (by omega) (by omega) (by rw [eo, F.at _ (by omega)]; omega)
    (by rw [eo, F.at _ (by omega)]; omega) sB (by rw [eo]; exact F.lowN (k := 0xF0) (by decide) (by decide) hco)
    (F.lowData (c := 0xF0) (by decide) rfl (by decide) (by decide))
  rw [mem1] at ok2 bad2 fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], ok2, bad2, fr2⟩

set_option maxRecDepth 100000 in
/-- A call to `ScalarValue::<NistP384>::is_zero`. -/
theorem c_sz {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o x S : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (C : PvCode Mx) (F : Fr S N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = SZ) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = x) {cx : Nat} (hcx : cx + 48 ≤ N) (ex : x = S + BitVec.ofNat 32 cx)
    (acx : cx % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧ reg n' sp = S ∧
      reg n' a0 = (if ∀ i : Nat, i < 12 → memLoad32 Mx (x + BitVec.ofNat 32 (4 * i)) = 0 then 1 else 0) ∧
      (∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q) ∧
      ∀ y, Sep (S + 0xFFFFFFAC) 0x54 y 1 → n'.mem y = Mx y := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  obtain ⟨n2, c2, pc2, sp2, a02, k2, fr2⟩ := scalarIsZero384_correct n1 (P := SZ) (sp0 := S) (x := x)
    (by rw [mem1]; exact ⟨by decide, C.sz, by rw [show SZ + 0x13A12 = MSET by decide]; exact C.K.mset,
      by rw [show SZ + 0xC876 = BitVec.ofNat 32 limbCtEqAddress by decide]; exact C.K.lce,
      by rw [show SZ + 0x6E = BitVec.ofNat 32 uintRefIsZeroAddress by decide]; exact C.K.uiz,
      by rw [show SZ + 0x6E + 0x1A = BitVec.ofNat 32 uintRefIsNonzeroAddress by decide]; exact C.K.refnz,
      by rw [show SZ + 0xC970 = BitVec.ofNat 32 blackBoxU8Address by decide]; exact C.K.bb,
      by omega, by omega, by rw [ex, F.at _ (by omega)]; omega, by rw [ex, F.at _ (by omega)]; omega,
      F.lowHi (by decide) rfl (by decide) (by decide), F.lowHi (by decide) rfl (by decide) (by decide),
      F.lowHi (by decide) rfl (by decide) (by decide), F.lowHi (by decide) rfl (by decide) (by decide),
      F.lowHi (by decide) rfl (by decide) (by decide), F.lowHi (by decide) rfl (by decide) (by decide),
      by rw [ex]; exact F.lowN (k := 0x54) (by decide) (by decide) hcx⟩) pc1 sp1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at a02 fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], fr2⟩

set_option maxRecDepth 100000 in
/-- A call to `VerifyingKey::<NistP384>::from_sec1_bytes`, whose frame takes
the 0x420 bytes below the caller's `sp`. -/
theorem c_fs {base : Word} {code : List Nat} {N : Nat} {Mx : Word → BitVec 8} {n : Machine} {off : Nat}
    {g : Fin 32 → Word} {imm o inp out B : Word}
    (s : St Mx base n off g) (hcd : CodeIn Mx base code) (C : PvCode Mx) (D : PvData Mx) (F : Fr B N)
    (hN : 0x420 ≤ N)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = Fs.FP) (he8 : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = B + 0x420) (ha0 : g a0 = out) (ha1 : g a1 = inp)
    (sI : Sep inp 0x61 (B + 0xFFFFFE60) 0x5C0) (hI : inp.toNat + 0x61 ≤ 0x40000000)
    {co : Nat} (hco : co + 0x68 ≤ N) (hco' : 0x420 ≤ co) (eo : out = B + BitVec.ofNat 32 co) (aco : co % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem base n' (off + 8) (reg n') ∧ reg n' sp = B + 0x420 ∧
      (∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q) ∧
      (Fs.FsOk Mx inp → memLoad32 n'.mem out = 0 ∧
        accV n'.mem (out + BitVec.ofNat 32 4) 12 = Fs.fsVal Mx inp 1 * 2 ^ 384 % p384 ∧
        accV n'.mem (out + BitVec.ofNat 32 0x34) 12 = Fs.fsVal Mx inp 0x31 * 2 ^ 384 % p384 ∧
        n'.mem (out + BitVec.ofNat 32 0x64) = 0) ∧
      (¬ Fs.FsOk Mx inp → memLoad32 n'.mem out = 1) ∧
      ∀ x, Sep (B + 0xFFFFFE60) 0x5C0 x 1 → Sep out 0x68 x 1 → n'.mem x = Mx x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have F' : Fr B 0x420 := by have := F.sub (c := 0) (n := 0x420) (by decide) (by omega); rwa [add_ofNat_zero] at this
  have hO : out.toNat + 0x68 ≤ 0x40000000 := by rw [eo, F.at _ (by omega)]; omega
  have sO : Sep out 0x68 (B + 0xFFFFFE60) 0x5C0 := by
    have hb1A : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    rw [eo]; exact (sep_of_le (by rw [hb1A, F.at co (by omega)]; omega) (by rw [F.at co (by omega)]; omega)).symm
  have hra1 : reg n1 ra = base + BitVec.ofNat 32 (off + 8) := by rw [regs1]; simp +decide [upd]
  obtain ⟨n2, c2, ⟨pc2, sp2, sv2, k2, fr2⟩, ok2, bad2⟩ := Fs.p384FromSec1_correct n1 (S := B) (inp := inp) (out := out)
    (by rw [mem1]; exact C.fs) (by rw [mem1]; exact D.D) F' pc1 (by rw [r1 sp (by decide)]; exact hsp)
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [hra1]; exact even_clear _ he8) sI hI (by rw [eo, F.at _ (by omega)]; omega) hO sO
  rw [mem1] at ok2 bad2 fr2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2, hra1], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_, ok2, bad2, fr2⟩
  by_cases h34 : q.val ∈ [3, 4, 26, 27]
  · rw [k2 q h34, r1 q (by revert h34; revert q; decide)]
  · obtain ⟨k, hk, hk0, rfl⟩ : ∃ k, k < 11 ∧ 0 < k ∧ savedReg k = q := by revert hq h34; revert q; decide
    have hne : ∀ k, k < 11 → 0 < k → savedReg k ≠ ra := by decide
    rw [sv2 k hk, r1 _ (hne k hk hk0)]

end C3.RV32.Pv
