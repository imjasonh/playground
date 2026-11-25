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

end C3.RV32.Ac
