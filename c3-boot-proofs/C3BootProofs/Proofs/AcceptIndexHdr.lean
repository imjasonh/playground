import C3BootProofs.Proofs.AcceptIndexHead
import C3BootProofs.Proofs.ImageHeader

/-!
# `boot_main`'s first closure: the index stage's magic, version, and count

From 0x2EC the index stage reads the header it copied into the frame with a
`Reader`: the magic, then the version, which must be 2, then the count of
roots, which must be at most 64. At 0x376 it is about to clear the buffer
for the index of lengths.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3

set_option maxRecDepth 100000

theorem acx_br {ptr len pos n : Word} (h : pos.toNat + n.toNat ≤ len.toNat) :
    bytesResult ptr len pos n = some (ptr + pos, pos + n) := by
  rw [bytesResult_eq]; exact ite_eq_left_of_eq_true _ _ (eq_true h)

theorem acx_magicR {M : Word → BitVec 8} {self ptr len pos : Word} (k : Word)
    (h1 : memLoad32 M self = ptr) (h2 : memLoad32 M (self + 4) = len) (h3 : memLoad32 M (self + 8) = pos)
    (h : pos.toNat + 4 ≤ len.toNat) :
    magicResult M self k = (if (memLoad32 M (ptr + pos) == k) = true then 0xFFFFFFFF else 2) ∧
      magicMem M self = memStore32 M (self + 8) (pos + 4) := by
  unfold magicResult magicMem; rw [h1, h2, h3, acx_br (n := 4) h]; exact ⟨rfl, rfl⟩

theorem acx_u16R {M : Word → BitVec 8} {self ptr len pos : Word}
    (h1 : memLoad32 M self = ptr) (h2 : memLoad32 M (self + 4) = len) (h3 : memLoad32 M (self + 8) = pos)
    (h : pos.toNat + 2 ≤ len.toNat) :
    u16Result M self = ((M (ptr + pos + 1)).zeroExtend 32 <<< 24 ||| (M (ptr + pos)).zeroExtend 32 <<< 16) ∧
      u16Mem M self = memStore32 M (self + 8) (pos + 2) := by
  unfold u16Result u16Mem; rw [h1, h2, h3, acx_br (n := 2) h]; exact ⟨rfl, rfl⟩

theorem acx_mag_bytes {M : Word → BitVec 8} {a : Word} (h : memLoad32 M a = 0x55543343) :
    (M a).toNat = 0x43 ∧ (M (a + 1)).toNat = 0x33 ∧ (M (a + 2)).toNat = 0x54 ∧ (M (a + 3)).toNat = 0x55 := by
  have e := memLoad32_toNat M a
  rw [h] at e
  have h0 : (M a).toNat < 256 := (M a).isLt
  have h1 : (M (a + 1)).toNat < 256 := (M (a + 1)).isLt
  have h2 : (M (a + 2)).toNat < 256 := (M (a + 2)).isLt
  have h3 : (M (a + 3)).toNat < 256 := (M (a + 3)).isLt
  have e' : 0x55543343 = (M a).toNat + 256 * ((M (a + 1)).toNat + 256 * ((M (a + 2)).toNat +
      256 * (M (a + 3)).toNat)) := e
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem acx_u16v (x y : BitVec 8) :
    aluEval .srl (y.zeroExtend 32 <<< 24 ||| x.zeroExtend 32 <<< 16 : Word) 0x10 =
      BitVec.ofNat 32 (x.toNat + 256 * y.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hx : x.toNat < 256 := x.isLt
  have hy : y.toNat < 256 := y.isLt
  rw [show aluEval .srl (y.zeroExtend 32 <<< 24 ||| x.zeroExtend 32 <<< 16 : Word) 0x10 =
      (y.zeroExtend 32 <<< 24 ||| x.zeroExtend 32 <<< 16 : Word) >>> 16 from rfl, version_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem acx_ofNat_ne {v c : Nat} (hv : v < 2 ^ 32) (hc : c < 2 ^ 32) (h : v ≠ c) :
    BitVec.ofNat 32 v ≠ BitVec.ofNat 32 c := fun e => by
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hc] at this
  exact h this

theorem acx_toNat_ofNat {v : Nat} (hv : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

/-- A straight-line block with no store that leaves the registers of
`acxL` alone. -/
theorem acx_blk {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) {o o' : Nat}
    (s : St n.mem AC n o (reg n)) (is : List BInstr) (he : blockEnd bootMainClosure0Code o is = some o')
    (hok : BlockOk AC bootMainClosure0Code.length is (n.mem, reg n))
    (hm : (runBlock is (n.mem, reg n)).1 = n.mem)
    (hw : ∀ q, acxL q = true → q ∉ is.filterMap BInstr.dst) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' o' (reg n') ∧ AcxC P n' ∧ n'.mem = n.mem ∧
      ∀ q, reg n' q = (runBlock is (n.mem, reg n)).2 q := by
  obtain ⟨n1, c1, u1⟩ := s.block is (A.code K) he hok
  have m1 : n1.mem = n.mem := u1.mem.trans hm
  exact ⟨n1, c1, ⟨u1.pc, rfl, fun _ => rfl⟩,
    A.next (fun q hq => by rw [u1.regs, runBlock_reg _ _ _ q s.zero (hw q hq)]) (fun x _ _ => by rw [m1]),
    m1, fun q => by rw [u1.regs]⟩

theorem acx_e4 (B : Word) : B + BitVec.ofNat 32 0x580C + 4 = B + BitVec.ofNat 32 0x5810 :=
  add_ofNat_assoc _ _ _

theorem acx_e8 (B : Word) : B + BitVec.ofNat 32 0x580C + 8 = B + BitVec.ofNat 32 0x5814 :=
  add_ofNat_assoc _ _ _

/-- The `Reader` over the header at `B + 0x580C`, at position `q`. -/
structure AcxRd (P : AcxP) (M : Word → BitVec 8) (q : Nat) : Prop where
  p : memLoad32 M (P.B + BitVec.ofNat 32 0x580C) = P.B + BitVec.ofNat 32 0x5800
  l : memLoad32 M (P.B + BitVec.ofNat 32 0x5810) = 8
  pos : memLoad32 M (P.B + BitVec.ofNat 32 0x5814) = BitVec.ofNat 32 q
  hdr : ∀ i, i < 8 → M (P.B + BitVec.ofNat 32 (0x5800 + i)) = P.flash ((reg P.n0 (24 : Fin 32)).toNat + i)

theorem acx_rd_step {P : AcxP} (K : AcxK P) {M M' g : Word → BitVec 8} {q q' lo : Nat} {v : Word}
    (R : AcxRd P M q) (hg : g = memStore32 M (P.B + BitVec.ofNat 32 0x580C + 8) v)
    (fr : ∀ x : Word, (x.toNat < P.B.toNat + lo ∨ P.B.toNat + 0x3A50 ≤ x.toNat) → M' x = g x)
    (_hlo : lo ≤ 0x3A50) (hv : v = BitVec.ofNat 32 q') : AcxRd P M' q' := by
  have F := K.F
  rw [acx_e8] at hg
  subst hg
  refine ⟨?_, ?_, ?_, fun i hi => ?_⟩
  · rw [← R.p]
    exact acx_wz F (by decide) fun x h1 h2 => by
      rw [fr x (.inr (by omega)), memStore32_get_sep (acx_sepR F (by decide) (.inl (by omega)))]
  · rw [← R.l]
    exact acx_wz F (by decide) fun x h1 h2 => by
      rw [fr x (.inr (by omega)), memStore32_get_sep (acx_sepR F (by decide) (.inl (by omega)))]
  · rw [← hv, ← memLoad32_store32_same M (P.B + BitVec.ofNat 32 0x5814) v]
    exact acx_wz F (by decide) fun x h1 h2 => by rw [fr x (.inr (by omega))]
  · have hx := F.at (0x5800 + i) (by omega)
    rw [fr _ (.inr (by omega)), memStore32_get_sep (acx_sepR F (by decide) (.inl (by omega)))]
    exact R.hdr i hi

/-- From 0x324 or 0x346: point `a0` at the reader. -/
def acxH4 : List BInstr := [.lui a0 0x2000, .aluImm .add a0 a0 0xFFFFFDBC, .alu .add a0 a0 sp]

theorem acxH4_end : blockEnd bootMainClosure0Code 0x324 acxH4 = some 0x32C := by decide

theorem acxH4_end' : blockEnd bootMainClosure0Code 0x346 acxH4 = some 0x34E := by decide

set_option maxHeartbeats 4000000 in
/-- From 0x324 or 0x346: read a `u16` of the header. -/
theorem acx_u16step {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) {ob : Nat} {imm o' : Word} {q : Nat}
    (hq : q + 2 ≤ 8) (s : St n.mem AC n ob (reg n)) (R : AcxRd P n.mem q)
    (hblk : blockEnd bootMainClosure0Code ob acxH4 = some (ob + 8))
    (h1 : fetchRel bootMainClosure0Code (ob + 8) = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (ob + 8 + 4) = some (.jalr ra ra o', 4))
    (hb : AC + BitVec.ofNat 32 (ob + 8) + imm + o' = (img% readerU16Address))
    (he : (AC + BitVec.ofNat 32 (ob + 8 + 8)).toNat % 2 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (ob + 8 + 8) (reg n') ∧ AcxC P n' ∧
      (∀ q, acxS q = true → reg n' q = reg n q) ∧ AcxRd P n'.mem (q + 2) ∧
      reg n' a0 = ((P.flash ((reg P.n0 (24 : Fin 32)).toNat + (q + 1))).zeroExtend 32 <<< 24 |||
        (P.flash ((reg P.n0 (24 : Fin 32)).toNat + q)).zeroExtend 32 <<< 16) := by
  have rsp := A.rsp K
  obtain ⟨n1, c1, t1, A1, m1, g1⟩ := acx_blk K A s acxH4 hblk ⟨trivial, trivial, trivial, trivial⟩ rfl
    (by decide)
  have a01 : reg n1 a0 = P.B + BitVec.ofNat 32 0x580C := by
    rw [g1]; simp +decide only [runBlock, BInstr.run, acxH4, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k' rsp _ (by decide)
  have R1 : AcxRd P n1.mem q := m1 ▸ R
  obtain ⟨n2, c2, t2, A2, kk2, a02, fr2⟩ := acx_cu16 K A1 t1 h1 h2 hb he a01 R1.p R1.l
  have hq32 : (BitVec.ofNat 32 q).toNat = q := acx_toNat_ofNat (by omega)
  obtain ⟨hres, hmm⟩ := acx_u16R (ptr := P.B + BitVec.ofNat 32 0x5800) (len := 8) (pos := BitVec.ofNat 32 q) R1.p (by rw [acx_e4]; exact R1.l) (by rw [acx_e8]; exact R1.pos) (by rw [hq32, show (8 : Word).toNat = 8 from rfl]; exact hq)
  refine ⟨n2, c1.trans c2, t2, A2, fun r hr => ?_, acx_rd_step K R1 hmm fr2 (by decide) ?_, ?_⟩
  · rw [kk2 r hr, g1, runBlock_reg _ _ _ r s.zero (by simp only [acxH4]; revert hr; revert r; decide)]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hq32, acx_toNat_ofNat (v := q + 2) (by omega), show (2 : Word).toNat = 2 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [a02, hres, add_ofNat_assoc, acx_fl (c := 0x5800 + q) 1 (by rw [show (1 : Word).toNat = 1 from rfl]; omega),
      show 0x5800 + q + (1 : Word).toNat = 0x5800 + (q + 1) from Nat.add_assoc _ _ _,
      R1.hdr q (by omega), R1.hdr (q + 1) (by omega)]

/-- From 0x2EC: point `s10` at the stack's middle, set up the reader over
the header, and load the magic. -/
def acxH2 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x310, .alu .add (26 : Fin 32) sp a0, .sw (8 : Fin 32) (19 : Fin 32) 0xC,
   .sw (8 : Fin 32) (9 : Fin 32) 0x10, .sw (8 : Fin 32) x0 0x14, .lui a1 0x55543000,
   .aluImm .add a1 a1 0x343, .lui a0 0x2000, .aluImm .add a0 a0 0xFFFFFDBC, .alu .add a0 a0 sp]

theorem acxH2_end : blockEnd bootMainClosure0Code 0x2EC acxH2 = some 0x310 := by decide

/-- From 0x318: the magic's result, less -1. -/
def acxH3 : List BInstr := [.aluImm .and a1 a0 0xFF, .aluImm .add a1 a1 0xFFFFFF01]

theorem acxH3_end : blockEnd bootMainClosure0Code 0x318 acxH3 = some 0x320 := by decide

/-- The state at 0x324: the magic matched. -/
structure AcxM1 (P : AcxP) (n : Machine) : Prop where
  st : St n.mem AC n 0x324 (reg n)
  c : AcxC P n
  rd : AcxRd P n.mem 4
  s10 : reg n (26 : Fin 32) = P.B + BitVec.ofNat 32 0x4D60
  hL : (reg P.n0 (23 : Fin 32)).toNat ≤ 0x60000
  hL8 : 8 ≤ (reg P.n0 (23 : Fin 32)).toNat
  f0 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 0)).toNat = 0x43
  f1 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 1)).toNat = 0x33
  f2 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 2)).toNat = 0x54
  f3 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 3)).toNat = 0x55

set_option maxHeartbeats 4000000 in
/-- From 0x2EC to 0x324: check the magic. -/
theorem acx_h2 {P : AcxP} (K : AcxK P) {n : Machine} (S : AcxS1 P n) : AcxTo P n (AcxM1 P) := by
  have F := K.F
  have hFl := F.lo; have hFh := F.hi
  have A := S.c
  have s := S.st
  have rsp := A.rsp K
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block acxH2 (A.code K) acxH2_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acxH2]
    simp +decide only [upd, ↓reduceIte, and_true, true_and]
    rw [S.s0]
    exact ⟨acx_swok' F _ (by decide) (by decide), acx_swok' F _ (by decide) (by decide),
      acx_swok' F _ (by decide) (by decide)⟩)
  have g1 : ∀ q, reg n1 q = (runBlock acxH2 (n.mem, reg n)).2 q := fun q => by rw [u1.regs]
  have m1 : n1.mem = memStore32 (memStore32 (memStore32 n.mem (P.B + BitVec.ofNat 32 0x580C)
      (P.B + BitVec.ofNat 32 0x5800)) (P.B + BitVec.ofNat 32 0x5810) 8) (P.B + BitVec.ofNat 32 0x5814) 0 := by
    rw [u1.mem]; simp only [runBlock, BInstr.run, acxH2]
    simp +decide only [upd, ↓reduceIte]
    rw [S.s0, S.s3, S.s1, acx_fl (0xC : Word) (by decide), acx_fl (0x10 : Word) (by decide),
      acx_fl (0x14 : Word) (by decide)]
    rfl
  have A1 : AcxC P n1 := A.next
    (fun q hq => by rw [g1, runBlock_reg _ _ _ q hz (by simp only [acxH2]; revert hq; revert q; decide)])
    (fun x _ h2 => by
      rw [m1, memStore32_get_sep (acx_sepR F (by decide) (by omega)),
        memStore32_get_sep (acx_sepR F (by decide) (by omega)),
        memStore32_get_sep (acx_sepR F (by decide) (by omega))])
  have t1 : St n1.mem AC n1 0x310 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have R0 : AcxRd P n1.mem 0 := by
    refine ⟨?_, ?_, ?_, fun i hi => ?_⟩
    · rw [m1, memLoad32_store32_sep (acx_ss (by decide) (by decide) (by decide)),
        memLoad32_store32_sep (acx_ss (by decide) (by decide) (by decide)), memLoad32_store32_same]
    · rw [m1, memLoad32_store32_sep (acx_ss (by decide) (by decide) (by decide)), memLoad32_store32_same]
    · rw [m1, memLoad32_store32_same]; rfl
    · have hx := F.at (0x5800 + i) (by omega)
      rw [m1, memStore32_get_sep (acx_sepR F (by decide) (.inl (by omega))),
        memStore32_get_sep (acx_sepR F (by decide) (.inl (by omega))),
        memStore32_get_sep (acx_sepR F (by decide) (.inl (by omega)))]
      exact S.hdr i hi
  have a01 : reg n1 a0 = P.B + BitVec.ofNat 32 0x580C := by
    rw [g1]; simp +decide only [runBlock, BInstr.run, acxH2, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k' rsp _ (by decide)
  have a11 : reg n1 a1 = 0x55543343 := by
    rw [g1]; simp +decide only [runBlock, BInstr.run, acxH2, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
  have s101 : reg n1 (26 : Fin 32) = P.B + BitVec.ofNat 32 0x4D60 := by
    rw [g1]; simp +decide only [runBlock, BInstr.run, acxH2, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k rsp _ (by decide)
  obtain ⟨n2, c2, t2, A2, kk2, a02, fr2⟩ := acx_cmagic K A1 t1 ac_at_310 ac_at_314 (by decide) (by decide)
    a01 a11 R0.p R0.l
  obtain ⟨hres, hmm⟩ := acx_magicR (ptr := P.B + BitVec.ofNat 32 0x5800) (len := 8) (pos := BitVec.ofNat 32 0) 0x55543343 R0.p (by rw [acx_e4]; exact R0.l) (by rw [acx_e8]; exact R0.pos) (by decide)
  have R2 : AcxRd P n2.mem 4 := acx_rd_step K R0 hmm fr2 (by decide) (by decide)
  rw [add_ofNat_zero] at hres
  obtain ⟨n3, c3, t3, A3, m3, g3⟩ := acx_blk K A2 t2 acxH3 acxH3_end ⟨trivial, trivial, trivial⟩ rfl (by decide)
  have a03 : reg n3 a0 = reg n2 a0 := by
    rw [g3, runBlock_reg _ _ _ a0 t2.zero (by decide)]
  have C3 := A3.code K
  by_cases hm : memLoad32 n1.mem (P.B + BitVec.ofNat 32 0x5800) = 0x55543343
  case neg =>
    have a02' : reg n2 a0 = 2 := by
      rw [a02, hres]; exact ite_eq_right_of_eq_false _ _ (eq_false fun h => hm (beq_iff_eq.mp h))
    have a13 : reg n3 a1 = 0xFFFFFF03 := by
      rw [g3]; simp +decide only [runBlock, BInstr.run, acxH3, upd, ↓reduceIte, aluEval, a02',
        BitVec.reduceAnd, BitVec.reduceAdd]
    obtain ⟨n4, e4, t4⟩ := t3.taken C3 0x434 ac_at_320 (by decide)
      (acx_bne_t (by rw [a13, t3.zero]; decide))
    exact AcxTo.pre (c1.trans (c2.trans (c3.trans (.single e4))))
      (acx_exit K (A3.st t4) (acx_st t4) (c := 2) (by rw [t4.regs, a03, a02']; rfl) (.inl (by decide)))
  have a02' : reg n2 a0 = 0xFFFFFFFF := by
    rw [a02, hres]; exact ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.mpr hm))
  have a13 : reg n3 a1 = 0 := by
    rw [g3]; simp +decide only [runBlock, BInstr.run, acxH3, upd, ↓reduceIte, aluEval, a02',
      BitVec.reduceAnd, BitVec.reduceAdd]
  obtain ⟨n4, e4, t4⟩ := t3.notTaken C3 0x324 ac_at_320 (by decide)
    (acx_bne_f (by rw [a13, t3.zero]))
  obtain ⟨b0, b1, b2, b3⟩ := acx_mag_bytes hm
  rw [acx_fl 1 (by decide)] at b1
  rw [acx_fl 2 (by decide)] at b2
  rw [acx_fl 3 (by decide)] at b3
  have h0 : n1.mem (P.B + BitVec.ofNat 32 0x5800) = _ := R0.hdr 0 (by decide)
  have h1 : n1.mem (P.B + BitVec.ofNat 32 (0x5800 + (1 : Word).toNat)) = _ := R0.hdr 1 (by decide)
  have h2 : n1.mem (P.B + BitVec.ofNat 32 (0x5800 + (2 : Word).toNat)) = _ := R0.hdr 2 (by decide)
  have h3 : n1.mem (P.B + BitVec.ofNat 32 (0x5800 + (3 : Word).toNat)) = _ := R0.hdr 3 (by decide)
  rw [h0] at b0; rw [h1] at b1; rw [h2] at b2; rw [h3] at b3
  refine AcxTo.done ?_ |> AcxTo.pre (c1.trans (c2.trans (c3.trans (.single e4))))
  exact ⟨acx_st t4, A3.st t4, by rw [t4.mem, m3]; exact R2,
    by rw [t4.regs, g3, runBlock_reg _ _ _ _ t2.zero (by decide), kk2 _ (by decide), s101],
    S.hL, S.hL8, b0, b1, b2, b3⟩

theorem acx_b8 (x : BitVec 8) : x.toNat < 256 := x.isLt

/-- From 0x334 or 0x356: the `u16`'s error bit. -/
def acxH6 : List BInstr := [.aluImm .and a1 a0 0x1]

theorem acxH6_end : blockEnd bootMainClosure0Code 0x334 acxH6 = some 0x338 := by decide

theorem acxH6_end' : blockEnd bootMainClosure0Code 0x356 acxH6 = some 0x35A := by decide

/-- From 0x33E: the version, and the version this code reads. -/
def acxH7 : List BInstr := [.aluImm .srl a0 a0 0x10, .aluImm .add a1 x0 0x2]

theorem acxH7_end : blockEnd bootMainClosure0Code 0x33E acxH7 = some 0x342 := by decide

/-- From 0x43C: error 3, a version other than 2. -/
def acxV3 : List BInstr := [.aluImm .add a0 x0 0x3]

theorem acxV3_end : blockEnd bootMainClosure0Code 0x43C acxV3 = some 0x43E := by decide

/-- From 0x35C: the count of roots, and the most this code takes. -/
def acxH8 : List BInstr := [.aluImm .srl (18 : Fin 32) a0 0x10, .aluImm .add a0 x0 0x40]

theorem acxH8_end : blockEnd bootMainClosure0Code 0x35C acxH8 = some 0x364 := by decide

/-- From 0x368: set up the call that clears the index's buffer. -/
def acxH9 : List BInstr :=
  [.lui a0 0x2000, .aluImm .add a0 a0 0xFFFFFDC8, .alu .add a0 a0 sp, .aluImm .add a2 x0 0x108,
   .aluImm .add a1 x0 0x0]

theorem acxH9_end : blockEnd bootMainClosure0Code 0x368 acxH9 = some 0x376 := by decide

/-- The state at 0x376: the header is good, and `s2` holds the count of
roots. -/
structure AcxS2 (P : AcxP) (n : Machine) : Prop where
  st : St n.mem AC n 0x376 (reg n)
  c : AcxC P n
  a0 : reg n a0 = P.B + BitVec.ofNat 32 0x5818
  a1 : reg n a1 = 0
  a2 : reg n a2 = 0x108
  s10 : reg n (26 : Fin 32) = P.B + BitVec.ofNat 32 0x4D60
  hc : (reg n (18 : Fin 32)).toNat ≤ 64
  hL : (reg P.n0 (23 : Fin 32)).toNat ≤ 0x60000
  hL8 : 8 ≤ (reg P.n0 (23 : Fin 32)).toNat
  f0 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 0)).toNat = 0x43
  f1 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 1)).toNat = 0x33
  f2 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 2)).toNat = 0x54
  f3 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 3)).toNat = 0x55
  fv : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 4)).toNat +
    256 * (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 5)).toNat = 2
  fc : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 6)).toNat +
    256 * (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 7)).toNat = (reg n (18 : Fin 32)).toNat

set_option maxHeartbeats 4000000 in
/-- From 0x324 to 0x376: check the version and the count of roots. -/
theorem acx_h3 {P : AcxP} (K : AcxK P) {n : Machine} (S : AcxM1 P n) : AcxTo P n (AcxS2 P) := by
  have A := S.c
  obtain ⟨n1, c1, t1, A1, kk1, R1, a01⟩ := acx_u16step K A (ob := 0x324) (q := 4) (by decide) S.st S.rd
    acxH4_end ac_at_32c ac_at_330 (by decide) (by decide)
  obtain ⟨n2, c2, t2, A2, m2, g2⟩ := acx_blk K A1 t1 acxH6 acxH6_end ⟨trivial, trivial⟩ rfl (by decide)
  have a12 : reg n2 a1 = 0 := by
    rw [g2]; simp +decide only [runBlock, BInstr.run, acxH6, upd, ↓reduceIte]; rw [a01]; exact u16_lo _ _
  obtain ⟨n3, e3, t3⟩ := t2.taken (A2.code K) 0x33E ac_at_338 (by decide) (acx_beq_t (by rw [a12, t2.zero]))
  have A3 := A2.st t3
  obtain ⟨n4, c4, t4, A4, m4, g4⟩ := acx_blk K A3 (acx_st t3) acxH7 acxH7_end ⟨trivial, trivial, trivial⟩ rfl
    (by decide)
  have a04 : reg n4 a0 = BitVec.ofNat 32 ((P.flash ((reg P.n0 (24 : Fin 32)).toNat + 4)).toNat +
      256 * (P.flash ((reg P.n0 (24 : Fin 32)).toNat + (4 + 1))).toNat) := by
    rw [g4]; simp +decide only [runBlock, BInstr.run, acxH7, upd, ↓reduceIte]
    rw [t3.regs, g2, runBlock_reg _ _ _ a0 t1.zero (by decide), a01, acx_u16v]
  have a14 : reg n4 a1 = 2 := by
    rw [g4]; simp +decide only [runBlock, BInstr.run, acxH7, upd, ↓reduceIte, aluEval]
  have C4 := A4.code K
  have hb4 := acx_b8 (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 4))
  have hb5 := acx_b8 (P.flash ((reg P.n0 (24 : Fin 32)).toNat + (4 + 1)))
  by_cases hv : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 4)).toNat +
      256 * (P.flash ((reg P.n0 (24 : Fin 32)).toNat + (4 + 1))).toNat = 2
  case neg =>
    obtain ⟨n5, e5, t5⟩ := t4.taken C4 0x43C ac_at_342 (by decide)
      (acx_bne_t (by rw [a04, a14]; exact (acx_ofNat_ne (c := 2) (by omega) (by decide) hv : _ ≠ (2 : Word))))
    have A5 := A4.st t5
    obtain ⟨n6, c6, t6, A6, m6, g6⟩ := acx_blk K A5 (acx_st t5) acxV3 acxV3_end ⟨trivial, trivial⟩ rfl
      (by decide)
    obtain ⟨n7, e7, t7⟩ := t6.jump (A6.code K) ac_at_43e (off' := 0x434) (by decide) (by rw [t6.pc]; decide)
    refine AcxTo.pre (c1.trans (c2.trans ((Steps.single e3).trans (c4.trans ((Steps.single e5).trans
      (c6.trans (.single e7))))))) (acx_exit K (A6.st t7) (acx_st t7) (c := 3) ?_ (.inl (by decide)))
    rw [t7.regs, g6]; simp +decide only [runBlock, BInstr.run, acxV3, upd, ↓reduceIte, aluEval]
    rw [t5.regs, t4.zero]; rfl
  obtain ⟨n5, e5, t5⟩ := t4.notTaken C4 0x346 ac_at_342 (by decide)
    (acx_bne_f (by rw [a04, a14, hv]; rfl))
  have A5 := A4.st t5
  have R5 : AcxRd P n5.mem 6 := by rw [t5.mem, m4, t3.mem, m2]; exact R1
  obtain ⟨n6, c6, t6, A6, kk6, R6, a06⟩ := acx_u16step K A5 (ob := 0x346) (q := 6) (by decide) (acx_st t5) R5
    acxH4_end' ac_at_34e ac_at_352 (by decide) (by decide)
  obtain ⟨n7, c7, t7, A7, m7, g7⟩ := acx_blk K A6 t6 acxH6 acxH6_end' ⟨trivial, trivial⟩ rfl (by decide)
  have a17 : reg n7 a1 = 0 := by
    rw [g7]; simp +decide only [runBlock, BInstr.run, acxH6, upd, ↓reduceIte]; rw [a06]; exact u16_lo _ _
  obtain ⟨n8, e8, t8⟩ := t7.notTaken (A7.code K) 0x35C ac_at_35a (by decide)
    (acx_bne_f (by rw [a17, t7.zero]))
  have A8 := A7.st t8
  obtain ⟨n9, c9, t9, A9, m9, g9⟩ := acx_blk K A8 (acx_st t8) acxH8 acxH8_end ⟨trivial, trivial, trivial⟩ rfl
    (by decide)
  have hb6 := acx_b8 (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 6))
  have hb7 := acx_b8 (P.flash ((reg P.n0 (24 : Fin 32)).toNat + (6 + 1)))
  have s29 : reg n9 (18 : Fin 32) = BitVec.ofNat 32 ((P.flash ((reg P.n0 (24 : Fin 32)).toNat + 6)).toNat +
      256 * (P.flash ((reg P.n0 (24 : Fin 32)).toNat + (6 + 1))).toNat) := by
    rw [g9]; simp +decide only [runBlock, BInstr.run, acxH8, upd, ↓reduceIte]
    rw [t8.regs, g7, runBlock_reg _ _ _ a0 t6.zero (by decide), a06, acx_u16v]
  have a09 : reg n9 a0 = 0x40 := by
    rw [g9]; simp +decide only [runBlock, BInstr.run, acxH8, upd, ↓reduceIte, aluEval]
  have hc32 := acx_toNat_ofNat (v := (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 6)).toNat +
      256 * (P.flash ((reg P.n0 (24 : Fin 32)).toNat + (6 + 1))).toNat) (by omega)
  have C9 := A9.code K
  by_cases hc : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 6)).toNat +
      256 * (P.flash ((reg P.n0 (24 : Fin 32)).toNat + (6 + 1))).toNat ≤ 64
  case neg =>
    obtain ⟨n10, e10, t10⟩ := t9.taken C9 0x2AE ac_at_364 (by decide)
      (acx_bltu_t (by rw [a09, s29, hc32]; show 64 < _; omega))
    exact AcxTo.pre (c1.trans (c2.trans ((Steps.single e3).trans (c4.trans ((Steps.single e5).trans
      (c6.trans (c7.trans ((Steps.single e8).trans (c9.trans (.single e10)))))))))) (acx_e5 K (A9.st t10) (acx_st t10))
  obtain ⟨n10, e10, t10⟩ := t9.notTaken C9 0x368 ac_at_364 (by decide)
    (acx_bltu_f (by rw [a09, s29, hc32]; exact hc))
  have A10 := A9.st t10
  have rsp := A10.rsp K
  obtain ⟨n11, c11, t11, A11, m11, g11⟩ := acx_blk K A10 (acx_st t10) acxH9 acxH9_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (by decide)
  refine AcxTo.done ?_ |> AcxTo.pre (c1.trans (c2.trans ((Steps.single e3).trans (c4.trans ((Steps.single e5).trans
      (c6.trans (c7.trans ((Steps.single e8).trans (c9.trans ((Steps.single e10).trans c11))))))))))
  have z10 := (acx_st t10).zero
  have s2e : reg n11 (18 : Fin 32) = reg n9 (18 : Fin 32) := by
    rw [g11, runBlock_reg _ _ _ _ z10 (by decide), t10.regs]
  have s10e : reg n11 (26 : Fin 32) = P.B + BitVec.ofNat 32 0x4D60 := by
    rw [g11, runBlock_reg _ _ _ _ z10 (by decide), t10.regs, g9, runBlock_reg _ _ _ _ (acx_st t8).zero (by decide),
      t8.regs, g7, runBlock_reg _ _ _ _ t6.zero (by decide), kk6 _ (by decide), t5.regs, g4,
      runBlock_reg _ _ _ _ (acx_st t3).zero (by decide), t3.regs, g2, runBlock_reg _ _ _ _ t1.zero (by decide),
      kk1 _ (by decide), S.s10]
  refine ⟨t11, A11, ?_, ?_, ?_, s10e, ?_, S.hL, S.hL8, S.f0, S.f1, S.f2, S.f3, hv, ?_⟩
  · rw [g11]; simp +decide only [runBlock, BInstr.run, acxH9, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k' rsp _ (by decide)
  · rw [g11]; simp +decide only [runBlock, BInstr.run, acxH9, upd, ↓reduceIte, aluEval]
  · rw [g11]; simp +decide only [runBlock, BInstr.run, acxH9, upd, ↓reduceIte, aluEval]
  · rw [s2e, s29, hc32]; exact hc
  · rw [s2e, s29, hc32]

end C3.RV32.Ac
