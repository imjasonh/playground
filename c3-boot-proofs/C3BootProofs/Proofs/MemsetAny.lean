import C3BootProofs.Proofs.Memset
import C3BootProofs.Proofs.ShaSpec

/-!
# `memset`, for any buffer

`memset_aligned` covers the word-aligned buffers that the field
multiplication zeroes. Most callers pass byte buffers of any alignment and
length, so `memset_correct` covers every call: the compiled function sets
the first `n` bytes from `dst` to the fill byte and leaves every other byte
alone.

The compiled code has two paths. Below 16 bytes it stores one byte at a
time. Otherwise it stores bytes up to the first 4-byte boundary, then words,
then the bytes left over. The proof follows each loop with `fillBytes`,
which says how many bytes from `dst` are filled so far.
-/

namespace C3.RV32

open C3.ImageV0

/-- `M` with the `k` bytes from `dst` set to `v`. -/
def fillBytes (M : Word → BitVec 8) (dst : Word) (v : BitVec 8) (k : Nat) : Word → BitVec 8 :=
  fun x => if (x - dst).toNat < k then v else M x

theorem fillBytes_zero (M : Word → BitVec 8) (dst : Word) (v : BitVec 8) :
    fillBytes M dst v 0 = M := by
  funext x; simp [fillBytes]

theorem sub_eq_ofNat {x dst : Word} {k : Nat} (hk : k < 2 ^ 32) (h : (x - dst).toNat = k) :
    x = dst + BitVec.ofNat 32 k := by
  have e : x - dst = BitVec.ofNat 32 k := BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hk])
  rw [← e, BitVec.add_comm, BitVec.sub_add_cancel]

theorem add_sub_toNat (dst : Word) {k : Nat} (hk : k < 2 ^ 32) :
    (dst + BitVec.ofNat 32 k - dst).toNat = k := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- Storing `v` at the next byte fills one more byte. -/
theorem fillBytes_succ {M : Word → BitVec 8} {dst : Word} {v : BitVec 8} {k : Nat}
    (hk : k < 2 ^ 32) :
    memStore8 (fillBytes M dst v k) (dst + BitVec.ofNat 32 k) v = fillBytes M dst v (k + 1) := by
  funext x
  unfold memStore8 fillBytes
  by_cases hx : x = dst + BitVec.ofNat 32 k
  · subst hx
    rw [ite_eq_left rfl, add_sub_toNat dst hk, ite_eq_left (Nat.lt_succ_self k)]
  · rw [ite_eq_right hx]
    have hne : (x - dst).toNat ≠ k := fun h => hx (sub_eq_ofNat hk h)
    by_cases hlt : (x - dst).toNat < k
    · rw [ite_eq_left hlt, ite_eq_left (by omega)]
    · rw [ite_eq_right hlt, ite_eq_right (by omega)]

/-- A byte apart from the `n` bytes at `dst` keeps its value. -/
theorem fillBytes_sep {M : Word → BitVec 8} {dst y : Word} {v : BitVec 8} {n k : Nat}
    (hs : Sep dst n y 1) (hk : k ≤ n) : fillBytes M dst v k y = M y := by
  unfold fillBytes
  rw [ite_eq_right]
  intro hlt
  have e := sub_eq_ofNat (k := (y - dst).toNat) (y - dst).isLt rfl
  have := hs (y - dst).toNat (by omega) 0 (by decide)
  rw [add_ofNat_zero] at this
  exact this e.symm

theorem CodeIn.fillBytes {M : Word → BitVec 8} {dst base : Word} {v : BitVec 8} {n k : Nat}
    {code : List Nat} (hc : CodeIn M base code) (hs : Sep dst n base code.length) (hk : k ≤ n)
    : CodeIn (C3.RV32.fillBytes M dst v k) base code := fun i hi => by
  rw [fillBytes_sep (hs.subR (c := i) (l := 1) (by omega)) hk]
  exact hc i hi

/-- Storing a word whose four bytes are `v` at the next 4 bytes fills them. -/
theorem fillBytes_word {M : Word → BitVec 8} {dst w : Word} {v : BitVec 8} {k : Nat}
    (hk : k + 4 ≤ 2 ^ 32) (hw : ∀ i, i < 4 → w.extractLsb' (8 * i) 8 = v) :
    memStore32 (fillBytes M dst v k) (dst + BitVec.ofNat 32 k) w = fillBytes M dst v (k + 4) := by
  unfold memStore32
  have e : ∀ j : Nat, dst + BitVec.ofNat 32 k + BitVec.ofNat 32 j = dst + BitVec.ofNat 32 (k + j) :=
    fun j => add_ofNat_assoc dst k j
  rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, show (2 : Word) = BitVec.ofNat 32 2 from rfl,
    show (3 : Word) = BitVec.ofNat 32 3 from rfl, e, e, e,
    show w.extractLsb' 0 8 = v from hw 0 (by decide), show w.extractLsb' 8 8 = v from hw 1 (by decide),
    show w.extractLsb' 16 8 = v from hw 2 (by decide), show w.extractLsb' 24 8 = v from hw 3 (by decide),
    fillBytes_succ (by omega), fillBytes_succ (by omega), fillBytes_succ (by omega),
    fillBytes_succ (by omega)]

set_option maxRecDepth 200000 in
theorem fillWord_byte_nat : ∀ n, n < 256 → ∀ i, i < 4 →
    (aluEval .mul (BitVec.ofNat 32 n) (0x1010000 + 0x101)).extractLsb' (8 * i) 8 =
      BitVec.ofNat 8 n := by decide

set_option maxRecDepth 100000 in
theorem and255_small : ∀ r, r < 256 → r &&& 255 = r := by decide

theorem and255 (n : Nat) : n &&& 255 = n % 256 := by
  have h1 : n &&& 255 ≤ 255 := Nat.and_le_right
  rw [← Nat.mod_eq_of_lt (show n &&& 255 < 256 by omega), show (256 : Nat) = 2 ^ 8 from rfl,
    Nat.and_mod_two_pow]
  exact and255_small _ (Nat.mod_lt _ (by decide))

theorem and_ff_eq (b : Word) : aluEval .and b 0xFF = BitVec.ofNat 32 (b.extractLsb' 0 8).toNat := by
  apply BitVec.eq_of_toNat_eq
  show (b &&& 0xFF).toNat = _
  rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_and,
    show (0xFF : Word).toNat = 255 from rfl, and255]
  have := Nat.mod_lt b.toNat (show 2 ^ 8 > 0 by decide)
  rw [Nat.mod_eq_of_lt (a := b.toNat % 2 ^ 8) (by omega)]

/-- Each byte of `fillWord b` is the low byte of `b`. -/
theorem fillWord_byte (b : Word) : ∀ i, i < 4 → (fillWord b).extractLsb' (8 * i) 8 = b.extractLsb' 0 8 :=
  fun i hi => by
  unfold fillWord
  rw [and_ff_eq, fillWord_byte_nat _ (b.extractLsb' 0 8).isLt i hi, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]


theorem ofNat_add_lit (o j : Nat) : BitVec.ofNat 32 o + BitVec.ofNat 32 j = BitVec.ofNat 32 (o + j) :=
  BitVec.ofNat_add_ofNat ..

theorem back8 {o : Nat} (h : o + 8 < 2 ^ 32) :
    BitVec.ofNat 32 (o + 8) + 0xFFFFFFF8 = BitVec.ofNat 32 o := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFF8 : Word).toNat = 2 ^ 32 - 8
    from rfl]
  have := h
  omega

theorem dec_ofNat_succ {k : Nat} (hk : k + 1 < 2 ^ 32) :
    aluEval .add (BitVec.ofNat 32 (k + 1)) 0xFFFFFFFF = BitVec.ofNat 32 k := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1
    from rfl]
  have := hk
  omega

/-- A byte loop of the form `addi cnt, cnt, -1; sb src, 0(ptr); addi ptr, ptr, 1;
bnez cnt` at offset `o`. With `q` bytes from `dst` filled, `k` left, and
`ptr` at `dst + q`, it fills the rest and leaves the loop at `o + 10`.
`memset` has two of them. -/
theorem fill_loop {M0 : Word → BitVec 8} {B dst : Word} {v : BitVec 8} {code : List Nat}
    {o e : Nat} {cnt ptr src : Fin 32}
    (hc : ∀ j, j ≤ e → CodeIn (fillBytes M0 dst v j) B code) (he : e < 2 ^ 32)
    (ho : o + 10 < 2 ^ 32)
    (f0 : fetchRel code o = some (.aluImm .add cnt cnt 0xFFFFFFFF, 2))
    (f1 : fetchRel code (o + 2) = some (.store .sb ptr src 0, 4))
    (f2 : fetchRel code (o + 6) = some (.aluImm .add ptr ptr 1, 2))
    (f3 : fetchRel code (o + 8) = some (.branch .bne cnt x0 0xFFFFFFF8, 2))
    (hcp : cnt ≠ ptr) (hcs : cnt ≠ src) (hps : ptr ≠ src) (hc0 : cnt.val ≠ 0) (hp0 : ptr.val ≠ 0)
    (hs0 : src.val ≠ 0) :
    ∀ k q (n : Machine), q + k = e → 0 < k →
      St (fillBytes M0 dst v q) B n o (reg n) → reg n cnt = BitVec.ofNat 32 k →
      reg n ptr = dst + BitVec.ofNat 32 q → (reg n src).extractLsb' 0 8 = v →
      ∃ n', Steps n n' ∧ St (fillBytes M0 dst v e) B n' (o + 10) (reg n') ∧
        reg n' cnt = 0 ∧ reg n' ptr = dst + BitVec.ofNat 32 e ∧
        ∀ r, r ≠ cnt → r ≠ ptr → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro q n hqe _ s hcnt hptr hsrc
    have hcq := hc q (by omega)
    have hcq1 := hc (q + 1) (by omega)
    obtain ⟨n1, d1, u1⟩ := s.aluImm hcq f0 (off' := o + 2) (ofNat_add_lit o 2)
    obtain ⟨n2, d2, u2⟩ := u1.sb hcq f1 (off' := o + 6) (by rw [show o + 6 = o + 2 + 4 by omega]; exact ofNat_add_lit _ _)
    have hm : memStore8 (fillBytes M0 dst v q)
        (upd (reg n) cnt (aluEval .add (reg n cnt) 0xFFFFFFFF) ptr + 0)
        ((upd (reg n) cnt (aluEval .add (reg n cnt) 0xFFFFFFFF) src).extractLsb' 0 8) =
        fillBytes M0 dst v (q + 1) := by
      simp only [upd, hp0, hs0, hcp.symm, hcs.symm, ite_false, add_lit_zero, hptr, hsrc]
      exact fillBytes_succ (by omega)
    rw [hm] at u2
    obtain ⟨n3, d3, u3⟩ := u2.aluImm hcq1 f2 (off' := o + 8) (by rw [show o + 8 = o + 6 + 2 by omega]; exact ofNat_add_lit _ _)
    have r3 : ∀ r, reg n3 r = upd (upd (reg n) cnt (BitVec.ofNat 32 k)) ptr
        (dst + BitVec.ofNat 32 (q + 1)) r := fun r => by
      have e1 : aluEval .add (dst + BitVec.ofNat 32 q) 1 = dst + BitVec.ofNat 32 (q + 1) :=
        add_ofNat_assoc dst q 1
      rw [u3.regs]
      simp only [upd, hp0, hcp.symm, ite_false, hcnt, dec_ofNat_succ (show k + 1 < 2 ^ 32 by omega), hptr,
        e1]
    have frame : ∀ r, r ≠ cnt → r ≠ ptr → reg n3 r = reg n r := fun r h1 h2 => by
      rw [r3]; simp only [upd, h1, h2, ite_false]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp; exact s.zero.symm
      · simp [h0]
    have c3 : reg n3 cnt = BitVec.ofNat 32 k := by rw [r3]; simp [upd, hc0, hcp]
    have p3 : reg n3 ptr = dst + BitVec.ofNat 32 (q + 1) := by rw [r3]; simp [upd, hp0]
    have z3 : reg n3 x0 = 0 := u3.self.zero
    have u3' : St (fillBytes M0 dst v (q + 1)) B n3 (o + 8) (reg n3) := u3.self
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n4, d4, u4⟩ := u3'.notTaken hcq1 (o + 10) f3 (by rw [show o + 10 = o + 8 + 2 by omega]; exact ofNat_add_lit _ _) (by
        simp [branchTaken, c3, z3])
      have hq : q + 1 = e := by omega
      rw [hq] at u4 p3
      refine ⟨n4, .cons d1 (.cons d2 (.cons d3 (.single d4))), u4.self, ?_, ?_, ?_⟩
      · rw [u4.regs, c3]; rfl
      · rw [u4.regs, p3]
      · intro r h1 h2; rw [u4.regs, frame r h1 h2]
    · obtain ⟨n4, d4, u4⟩ := u3'.taken hcq1 o f3 (back8 (by omega)) (by
        simp only [branchTaken, c3, z3, bne_iff_ne, ne_eq]
        intro h; exact hk (ofNat_inj (by omega) (by decide) h))
      obtain ⟨n5, c5, u5, c5', p5, f5⟩ := ih (q + 1) n4 (by omega) (by omega) u4.self
        (by rw [u4.regs, c3]) (by rw [u4.regs, p3])
        (by rw [u4.regs, frame src hcs.symm hps.symm, hsrc])
      refine ⟨n5, .cons d1 (.cons d2 (.cons d3 (.cons d4 c5))), u5, c5', p5, fun r h1 h2 => ?_⟩
      rw [f5 r h1 h2, u4.regs, frame r h1 h2]

theorem ult_ofNat {dst : Word} {a b : Nat} (ha : dst.toNat + a < 2 ^ 32) (hb : dst.toNat + b < 2 ^ 32) :
    (dst + BitVec.ofNat 32 a).ult (dst + BitVec.ofNat 32 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat]
  apply decide_eq_decide.mpr
  rw [Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := b) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  constructor <;> intro h <;> omega

/-- The word loop at 0x3E: with `h + 4 * j` bytes filled, `ptr` at the next
byte, which is 4-byte aligned, and `w - j` words left, it fills them and
leaves the loop at 0x46. -/
theorem fillw_loop {B dst wv : Word} {M0 : Word → BitVec 8} {v : BitVec 8} {h w : Nat}
    (hc : ∀ j, j ≤ w → CodeIn (fillBytes M0 dst v (h + 4 * j)) B memsetCode)
    (hal : (dst + BitVec.ofNat 32 h).toNat % 4 = 0) (hwrap : dst.toNat + h + 4 * w < 2 ^ 32)
    (hwv : ∀ i, i < 4 → wv.extractLsb' (8 * i) 8 = v) :
    ∀ k j (n : Machine), j + k = w → 0 < k →
      St (fillBytes M0 dst v (h + 4 * j)) B n 0x3E (reg n) →
      reg n a4 = dst + BitVec.ofNat 32 (h + 4 * j) → reg n a5 = wv →
      reg n a3 = dst + BitVec.ofNat 32 (h + 4 * w) →
      ∃ n', Steps n n' ∧ St (fillBytes M0 dst v (h + 4 * w)) B n' 0x46 (reg n') ∧
        reg n' a4 = dst + BitVec.ofNat 32 (h + 4 * w) ∧ (∀ r, r ≠ a4 → reg n' r = reg n r) := by
  intro k
  induction k with
  | zero => intro _ _ _ hz; exact absurd hz (Nat.lt_irrefl 0)
  | succ k ih =>
    intro j n hjk _ s h4 h5 h3
    have hcj := hc j (by omega)
    have hal' : (dst + BitVec.ofNat 32 (h + 4 * j)).toNat % 4 = 0 := by
      rw [← add_ofNat_assoc]; exact aligned_add hal (k := 4 * j) (by omega)
    obtain ⟨n1, d1, u1⟩ := s.sw hcj mz_at_3e (off' := 0x40) (by decide)
      (by rw [h4, add_lit_zero]; exact hal')
    rw [h4, h5, add_lit_zero, fillBytes_word (by omega) hwv,
      show h + 4 * j + 4 = h + 4 * (j + 1) by omega] at u1
    have hcj1 := hc (j + 1) (by omega)
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hcj1 mz_at_40 (off' := 0x42) (by decide)
    have e4 : aluEval .add (dst + BitVec.ofNat 32 (h + 4 * j)) 4 = dst + BitVec.ofNat 32 (h + 4 * (j + 1)) := by
      show dst + BitVec.ofNat 32 (h + 4 * j) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc]; congr 2
    have r2 : ∀ r, reg n2 r = upd (reg n) a4 (dst + BitVec.ofNat 32 (h + 4 * (j + 1))) r := fun r => by
      rw [u2.regs]; simp +decide only [upd, h4, e4]
    have u2' : St (fillBytes M0 dst v (h + 4 * (j + 1))) B n2 0x42 (reg n2) := u2.self
    have ult := ult_ofNat (dst := dst) (a := h + 4 * (j + 1)) (b := h + 4 * w) (by omega) (by omega)
    by_cases hlt : j + 1 < w
    · obtain ⟨n3, d3, u3⟩ := u2'.taken hcj1 0x3E mz_at_42 (by decide) (by
        rw [r2, r2]; simp +decide only [upd, ite_false, ite_true, branchTaken]
        rw [h3, ult]; exact decide_eq_true (by omega))
      obtain ⟨n4, c4, u4, h44, f4⟩ := ih (j + 1) n3 (by omega) (by omega) u3.self
        (by rw [u3.regs, r2]; simp +decide [upd]) (by rw [u3.regs, r2]; simp +decide [upd, h5])
        (by rw [u3.regs, r2]; simp +decide [upd, h3])
      refine ⟨n4, .cons d1 (.cons d2 (.cons d3 c4)), u4, h44, fun r q4 => ?_⟩
      rw [f4 r q4, u3.regs, r2]; simp [upd, q4]
      by_cases h0 : r = 0
      · subst h0; exact fun _ => s.zero.symm
      · simp [h0]
    · have hj : j + 1 = w := by omega
      obtain ⟨n3, d3, u3⟩ := u2'.notTaken hcj1 0x46 mz_at_42 (by decide) (by
        rw [r2, r2]; simp +decide only [upd, ite_false, ite_true, branchTaken]
        rw [h3, ult]; exact decide_eq_false (by omega))
      rw [hj] at u3
      refine ⟨n3, .cons d1 (.cons d2 (.single d3)), u3.self, ?_, fun r q4 => ?_⟩
      · rw [u3.regs, r2]; simp +decide [upd, hj]
      · rw [u3.regs, r2]; simp [upd, q4]
        by_cases h0 : r = 0
        · subst h0; exact fun _ => s.zero.symm
        · simp [h0]

theorem fc_bits : ∀ i : Fin 32, ((0xFFFFFFFC : Word).getLsbD i.val && (3 : Word).getLsbD i.val) = false ∧
    ((0xFFFFFFFC : Word).getLsbD i.val || (3 : Word).getLsbD i.val) = true := by decide

theorem and_fc (b : Word) : b &&& 0xFFFFFFFC = b - (b &&& 3) := by
  have hd : (b &&& 0xFFFFFFFC) + (b &&& 3) = b := by
    rw [Sha256.add_disj]
    · apply Sha256.bitw; intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
      have := (fc_bits ⟨i, hi⟩).2
      cases hb : b.getLsbD i <;> simp_all
    · intro i hi
      simp only [BitVec.getLsbD_and]
      have := (fc_bits ⟨i, hi⟩).1
      cases b.getLsbD i <;> simp_all
  calc b &&& 0xFFFFFFFC = (b &&& 0xFFFFFFFC) + (b &&& 3) - (b &&& 3) := (BitVec.add_sub_cancel ..).symm
    _ = b - (b &&& 3) := by rw [hd]

/-- The bytes up to the first 4-byte boundary at or after `dst`. -/
def headLen (dst : Word) : Nat := (4 - dst.toNat % 4) % 4

theorem head_val (dst : Word) : aluEval .and (aluEval .sub 0 dst) 3 = BitVec.ofNat 32 (headLen dst) := by
  apply BitVec.eq_of_toNat_eq
  show ((0 - dst) &&& 3).toNat = _
  rw [BitVec.toNat_and, show (3 : Word).toNat = 3 from rfl, and3, BitVec.toNat_sub, BitVec.toNat_ofNat,
    show (0 : Word).toNat = 0 from rfl]
  unfold headLen
  have := dst.isLt
  omega

theorem and3_val {x : Nat} (hx : x < 2 ^ 32) : aluEval .and (BitVec.ofNat 32 x) 3 = BitVec.ofNat 32 (x % 4) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 x &&& 3).toNat = _
  rw [BitVec.toNat_and, show (3 : Word).toNat = 3 from rfl, and3, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx]
  omega

theorem mask_val {x : Nat} (hx : x < 2 ^ 32) :
    aluEval .and (BitVec.ofNat 32 x) 0xFFFFFFFC = BitVec.ofNat 32 (4 * (x / 4)) := by
  show BitVec.ofNat 32 x &&& 0xFFFFFFFC = _
  rw [and_fc]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_and, show (3 : Word).toNat = 3 from rfl, and3, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  omega

theorem sub_val {x y : Nat} (hy : y ≤ x) (hx : x < 2 ^ 32) :
    aluEval .sub (BitVec.ofNat 32 x) (BitVec.ofNat 32 y) = BitVec.ofNat 32 (x - y) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 x - BitVec.ofNat 32 y).toNat = _
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

section

set_option maxRecDepth 20000

theorem ms_at_14 : fetchRel memsetCode 0x14 = some (.alu .add a5 x0 a3, 2) := by decide
theorem ms_at_16 : fetchRel memsetCode 0x16 = some (.alu .add a6 x0 a0, 2) := by decide
theorem ms_at_18 : fetchRel memsetCode 0x18 = some (.aluImm .add a5 a5 0xFFFFFFFF, 2) := by decide
theorem ms_at_1a : fetchRel memsetCode 0x1A = some (.store .sb a6 a1 0x0, 4) := by decide
theorem ms_at_1e : fetchRel memsetCode 0x1E = some (.aluImm .add a6 a6 0x1, 2) := by decide
theorem ms_at_20 : fetchRel memsetCode 0x20 = some (.branch .bne a5 x0 0xFFFFFFF8, 2) := by decide
theorem ms_at_52 : fetchRel memsetCode 0x52 = some (.alu .add a3 x0 a0, 2) := by decide
theorem ms_at_54 : fetchRel memsetCode 0x54 = some (.alu .add a4 a0 a2, 4) := by decide
theorem ms_at_58 : fetchRel memsetCode 0x58 = some (.branch .bgeu a0 a4 0xE, 4) := by decide
theorem ms_at_5c : fetchRel memsetCode 0x5C = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem ms_at_5e : fetchRel memsetCode 0x5E = some (.store .sb a3 a1 0x0, 4) := by decide
theorem ms_at_62 : fetchRel memsetCode 0x62 = some (.aluImm .add a3 a3 0x1, 2) := by decide
theorem ms_at_64 : fetchRel memsetCode 0x64 = some (.branch .bne a2 x0 0xFFFFFFF8, 2) := by decide

end


theorem St.upd_eq {M : Word → BitVec 8} {base : Word} {n : Machine} {off : Nat} {f : Fin 32 → Word}
    {rd : Fin 32} {x : Word} (s : St M base n off (upd f rd x)) (h : rd.val ≠ 0) : reg n rd = x := by
  rw [s.regs]; simp [upd, h]

theorem St.upd_ne {M : Word → BitVec 8} {base : Word} {n : Machine} {off : Nat} {f : Fin 32 → Word}
    {rd : Fin 32} {x : Word} (s : St M base n off (upd f rd x)) (hz : f 0 = 0) (r : Fin 32)
    (hr : r ≠ rd) : reg n r = f r := by
  rw [s.regs]; unfold upd
  by_cases h0 : r.val = 0
  · have : r = 0 := Fin.ext h0
    subst this; simp [hz]
  · simp [h0, hr]

theorem ult_lit {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x).ult (BitVec.ofNat 32 y) = decide (x < y) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-- **The compiled `memset` is correct for any buffer.** Called with `dst`,
the fill value `b`, and a length of `n` bytes that doesn't run past the top
of memory, it sets the `n` bytes from `dst` to the low byte of `b`, leaves
every other byte as it was, returns `dst` in `a0`, and changes only `a2`
through `a6` among the other registers. It uses no stack. -/
theorem memset_correct (m : Machine) (base retAddr dst b : Word) (n : Nat)
    (hcode : CodeAt m base memsetCode) (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = dst) (ha1 : reg m a1 = b) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hwrap : dst.toNat + n < 2 ^ 32) (hDC : Sep dst n base memsetCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = fillBytes m.mem dst (b.extractLsb' 0 8) n ∧
      reg m' a0 = dst ∧ ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → reg m' r = reg m r := by
  let v := b.extractLsb' 0 8
  have hcB : ∀ j, j ≤ n → CodeIn (fillBytes m.mem dst v j) base memsetCode :=
    fun j hj => CodeIn.fillBytes (fun i hi => hcode i hi) hDC hj
  have hcn := hcB n (Nat.le_refl n)
  have hv : (reg m a1).extractLsb' 0 8 = v := by rw [ha1]
  have hn32 : n < 2 ^ 32 := by omega
  -- Every path ends at the `ret` at 0x66 with the buffer filled.
  have fin : ∀ nf, Steps m nf → St (fillBytes m.mem dst v n) base nf 0x66 (reg nf) →
      (∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → reg nf r = reg m r) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = fillBytes m.mem dst v n ∧
        reg m' a0 = dst ∧ ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → reg m' r = reg m r := by
    intro nf cf sf kf
    obtain ⟨n1, d1, pc1, mem1, regs1⟩ := sf.jalr hcn mz_at_66
    refine ⟨n1, cf.trans (.single d1), ?_, mem1, ?_, fun r q2 q3 q4 q5 q6 => ?_⟩
    · rw [pc1, kf ra (by decide) (by decide) (by decide) (by decide) (by decide), hra, add_lit_zero, hret]
    · rw [regs1, kf a0 (by decide) (by decide) (by decide) (by decide) (by decide), ha0]
    · rw [regs1, kf r q2 q3 q4 q5 q6]
  have u0 : St (fillBytes m.mem dst v 0) base m 0 (reg m) :=
    ⟨by rw [hpc]; simp, by rw [fillBytes_zero], fun _ => rfl⟩
  have hc0 := hcB 0 (Nat.zero_le n)
  have hz : reg m x0 = 0 := u0.zero
  obtain ⟨n1, d1, v1⟩ := u0.aluImm hc0 mz_at_0 (off' := 0x2) (by decide)
  have g1 : reg n1 a3 = BitVec.ofNat 32 16 := by rw [v1.upd_eq (by decide), hz]; rfl
  have K1 : ∀ r, r ≠ a3 → reg n1 r = reg m r := v1.upd_ne hz
  have z1 : reg n1 x0 = 0 := v1.self.zero
  have v1' : St (fillBytes m.mem dst v 0) base n1 0x2 (reg n1) := v1.self
  by_cases hshort : n < 16
  · -- Fewer than 16 bytes: one byte at a time.
    obtain ⟨n2, d2, v2⟩ := v1'.taken hc0 0x52 mz_at_2 (by decide) (by
      simp only [branchTaken]; rw [K1 a2 (by decide), ha2, g1, ult_lit hn32 (by decide)]
      exact decide_eq_true hshort)
    obtain ⟨n3, d3, v3⟩ := v2.alu hc0 ms_at_52 (off' := 0x54) (by decide)
    have g3 : reg n3 a3 = dst := by
      rw [v3.upd_eq (by decide), z1, K1 a0 (by decide), ha0]; exact BitVec.zero_add _
    have K3 := v3.upd_ne z1
    have v3' : St (fillBytes m.mem dst v 0) base n3 0x54 (reg n3) := v3.self
    obtain ⟨n4, d4, v4⟩ := v3'.alu hc0 ms_at_54 (off' := 0x58) (by decide)
    have g4 : reg n4 a4 = dst + BitVec.ofNat 32 n := by
      rw [v4.upd_eq (by decide), K3 a0 (by decide), K3 a2 (by decide), K1 a0 (by decide),
        K1 a2 (by decide), ha0, ha2]; rfl
    have K4 := v4.upd_ne v3'.zero
    have v4' : St (fillBytes m.mem dst v 0) base n4 0x58 (reg n4) := v4.self
    have ga0 : reg n4 a0 = dst := by
      rw [K4 a0 (by decide), K3 a0 (by decide), K1 a0 (by decide), ha0]
    have ult0 := ult_ofNat (dst := dst) (a := 0) (b := n) (by omega) (by omega)
    rw [add_ofNat_zero] at ult0
    have Kf : ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → reg n4 r = reg m r :=
      fun r _ q3 q4 _ _ => by rw [K4 r q4, K3 r q3, K1 r q3]
    by_cases hn0 : n = 0
    · obtain ⟨n5, d5, v5⟩ := v4'.taken hc0 0x66 ms_at_58 (by decide) (by
        simp only [branchTaken]; rw [ga0, g4, ult0, hn0]; rfl)
      have e0 : fillBytes m.mem dst v 0 = fillBytes m.mem dst v n := by rw [hn0]
      rw [e0] at v5
      exact fin n5 (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5))))) v5.self
        (fun r q2 q3 q4 q5 q6 => by rw [v5.regs, Kf r q2 q3 q4 q5 q6])
    · obtain ⟨n5, d5, v5⟩ := v4'.notTaken hc0 0x5C ms_at_58 (by decide) (by
        simp only [branchTaken]; rw [ga0, g4, ult0]; simp only [Bool.not_eq_false']
        exact decide_eq_true (by omega))
      obtain ⟨n6, c6, v6, _, _, f6⟩ := fill_loop (o := 0x5C) (cnt := a2) (ptr := a3) (src := a1) hcB
        hn32 (by decide) ms_at_5c ms_at_5e ms_at_62 ms_at_64 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) n 0 n5 (by omega) (by omega) v5.self
        (by rw [v5.regs, K4 a2 (by decide), K3 a2 (by decide), K1 a2 (by decide), ha2])
        (by rw [v5.regs, K4 a3 (by decide), g3, add_ofNat_zero])
        (by rw [v5.regs, K4 a1 (by decide), K3 a1 (by decide), K1 a1 (by decide)]; exact hv)
      exact fin n6 (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 c6))))) v6
        (fun r q2 q3 q4 q5 q6 => by rw [f6 r q2 q3, v5.regs, Kf r q2 q3 q4 q5 q6])
  · -- At least 16 bytes: bytes to a 4-byte boundary, words, then the rest.
    have h16 : 16 ≤ n := by omega
    let h := headLen dst
    have hh : h ≤ 3 := by show (4 - dst.toNat % 4) % 4 ≤ 3; omega
    have hal : (dst + BitVec.ofNat 32 h).toNat % 4 = 0 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := h) (by omega),
        Nat.mod_eq_of_lt (a := dst.toNat + h) (by omega)]
      show (dst.toNat + (4 - dst.toNat % 4) % 4) % 4 = 0; omega
    obtain ⟨n2, d2, v2⟩ := v1'.notTaken hc0 0x6 mz_at_2 (by decide) (by
      simp only [branchTaken]; rw [K1 a2 (by decide), ha2, g1, ult_lit hn32 (by decide)]
      exact decide_eq_false hshort)
    obtain ⟨n3, d3, v3⟩ := v2.alu hc0 mz_at_6 (off' := 0xA) (by decide)
    have g3 : reg n3 a3 = aluEval .sub 0 dst := by
      rw [v3.upd_eq (by decide), z1, K1 a0 (by decide), ha0]
    have K3 := v3.upd_ne z1
    have v3' : St (fillBytes m.mem dst v 0) base n3 0xA (reg n3) := v3.self
    obtain ⟨n4, d4, v4⟩ := v3'.aluImm hc0 mz_at_a (off' := 0xC) (by decide)
    have g4 : reg n4 a3 = BitVec.ofNat 32 h := by rw [v4.upd_eq (by decide), g3, head_val]
    have K4 := v4.upd_ne v3'.zero
    have v4' : St (fillBytes m.mem dst v 0) base n4 0xC (reg n4) := v4.self
    obtain ⟨n5, d5, v5⟩ := v4'.alu hc0 mz_at_c (off' := 0x10) (by decide)
    have ga0 : ∀ r, r ≠ a3 → reg n4 r = reg m r := fun r q => by rw [K4 r q, K3 r q, K1 r q]
    have g5 : reg n5 a4 = dst + BitVec.ofNat 32 h := by
      rw [v5.upd_eq (by decide), ga0 a0 (by decide), ha0, g4]; rfl
    have K5 := v5.upd_ne v4'.zero
    have v5' : St (fillBytes m.mem dst v 0) base n5 0x10 (reg n5) := v5.self
    have a0_5 : reg n5 a0 = dst := by rw [K5 a0 (by decide), ga0 a0 (by decide), ha0]
    have ulth := ult_ofNat (dst := dst) (a := 0) (b := h) (by omega) (by omega)
    rw [add_ofNat_zero] at ulth
    -- The bytes before the first 4-byte boundary.
    have H : ∃ n22, Steps m n22 ∧ St (fillBytes m.mem dst v h) base n22 0x22 (reg n22) ∧
        reg n22 a2 = BitVec.ofNat 32 n ∧ reg n22 a3 = BitVec.ofNat 32 h ∧
        reg n22 a4 = dst + BitVec.ofNat 32 h ∧
        ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → reg n22 r = reg m r := by
      have Kf : ∀ r, r ≠ a3 → r ≠ a4 → reg n5 r = reg m r := fun r q3 q4 => by
        rw [K5 r q4, ga0 r q3]
      have c5 : Steps m n5 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5))))
      by_cases hh0 : h = 0
      · obtain ⟨n6, d6, v6⟩ := v5'.taken hc0 0x22 mz_at_10 (by decide) (by
          simp only [branchTaken]; rw [a0_5, g5, ulth, hh0]; rfl)
        have e0 : fillBytes m.mem dst v 0 = fillBytes m.mem dst v h := by rw [hh0]
        rw [e0] at v6
        refine ⟨n6, c5.trans (.single d6), v6.self, ?_, ?_, ?_, fun r q2 q3 q4 _ _ => ?_⟩
        · rw [v6.regs, Kf a2 (by decide) (by decide), ha2]
        · rw [v6.regs, K5 a3 (by decide), g4]
        · rw [v6.regs, g5]
        · rw [v6.regs, Kf r q3 q4]
      · obtain ⟨n6, d6, v6⟩ := v5'.notTaken hc0 0x14 mz_at_10 (by decide) (by
          simp only [branchTaken]; rw [a0_5, g5, ulth]; simp only [Bool.not_eq_false']
          exact decide_eq_true (by omega))
        obtain ⟨n7, d7, v7⟩ := v6.alu hc0 ms_at_14 (off' := 0x16) (by decide)
        have g7 : reg n7 a5 = BitVec.ofNat 32 h := by
          rw [v7.upd_eq (by decide), v5'.zero, K5 a3 (by decide), g4]; exact BitVec.zero_add _
        have K7 := v7.upd_ne v5'.zero
        have v7' : St (fillBytes m.mem dst v 0) base n7 0x16 (reg n7) := v7.self
        obtain ⟨n8, d8, v8⟩ := v7'.alu hc0 ms_at_16 (off' := 0x18) (by decide)
        have g8 : reg n8 a6 = dst + BitVec.ofNat 32 0 := by
          rw [v8.upd_eq (by decide), v7'.zero, K7 a0 (by decide), a0_5, add_ofNat_zero]
          exact BitVec.zero_add _
        have K8 := v8.upd_ne v7'.zero
        obtain ⟨n9, c9, v9, _, _, f9⟩ := fill_loop (o := 0x18) (e := h) (cnt := a5) (ptr := a6)
          (src := a1) (fun j hj => hcB j (by omega)) (by omega) (by decide) ms_at_18 ms_at_1a ms_at_1e
          ms_at_20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h 0 n8
          (by omega) (by omega) v8.self
          (by rw [K8 a5 (by decide), g7]) g8
          (by rw [K8 a1 (by decide), K7 a1 (by decide), Kf a1 (by decide) (by decide)]; exact hv)
        have Kg : ∀ r, r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → reg n9 r = reg m r := fun r q3 q4 q5 q6 => by
          rw [f9 r q5 q6, K8 r q6, K7 r q5, Kf r q3 q4]
        refine ⟨n9, c5.trans (.cons d6 (.cons d7 (.cons d8 c9))), v9, ?_, ?_, ?_,
          fun r _ q3 q4 q5 q6 => Kg r q3 q4 q5 q6⟩
        · rw [Kg a2 (by decide) (by decide) (by decide) (by decide), ha2]
        · rw [f9 a3 (by decide) (by decide), K8 a3 (by decide), K7 a3 (by decide), K5 a3 (by decide), g4]
        · rw [f9 a4 (by decide) (by decide), K8 a4 (by decide), K7 a4 (by decide), g5]
    obtain ⟨n22, c22, v22, g22a2, g22a3, g22a4, K22⟩ := H
    have hc22 := hcB h (by omega)
    -- The words.
    let w := (n - h) / 4
    have hw : 3 ≤ w := by show 3 ≤ (n - h) / 4; omega
    obtain ⟨m1, e1, u1⟩ := v22.alu hc22 mz_at_22 (off' := 0x24) (by decide)
    have q1 : reg m1 a2 = BitVec.ofNat 32 (n - h) := by
      rw [u1.upd_eq (by decide), g22a2, g22a3, sub_val (by omega) hn32]
    have L1 := u1.upd_ne v22.zero
    have u1' : St (fillBytes m.mem dst v h) base m1 0x24 (reg m1) := u1.self
    obtain ⟨m2, e2, u2⟩ := u1'.aluImm hc22 mz_at_24 (off' := 0x28) (by decide)
    have q2 : reg m2 a3 = BitVec.ofNat 32 (4 * w) := by
      rw [u2.upd_eq (by decide), q1, mask_val (by omega)]
    have L2 := u2.upd_ne u1'.zero
    have u2' : St (fillBytes m.mem dst v h) base m2 0x28 (reg m2) := u2.self
    obtain ⟨m3, e3, u3⟩ := u2'.alu hc22 mz_at_28 (off' := 0x2A) (by decide)
    have q3 : reg m3 a3 = dst + BitVec.ofNat 32 (h + 4 * w) := by
      rw [u3.upd_eq (by decide), q2, L2 a4 (by decide), L1 a4 (by decide), g22a4]
      show BitVec.ofNat 32 (4 * w) + (dst + BitVec.ofNat 32 h) = _
      rw [BitVec.add_comm, add_ofNat_assoc]
    have L3 := u3.upd_ne u2'.zero
    have u3' : St (fillBytes m.mem dst v h) base m3 0x2A (reg m3) := u3.self
    have a4_3 : reg m3 a4 = dst + BitVec.ofNat 32 h := by
      rw [L3 a4 (by decide), L2 a4 (by decide), L1 a4 (by decide), g22a4]
    obtain ⟨m4, e4, u4⟩ := u3'.notTaken hc22 0x2E mz_at_2a (by decide) (by
      simp only [branchTaken]
      rw [a4_3, q3, ult_ofNat (by omega) (by omega)]
      simp only [Bool.not_eq_false']; exact decide_eq_true (by omega))
    obtain ⟨m5, e5, u5⟩ := u4.lui hc22 mz_at_2e (off' := 0x32) (by decide)
    have L5 := u5.upd_ne u3'.zero
    have u5' : St (fillBytes m.mem dst v h) base m5 0x32 (reg m5) := u5.self
    obtain ⟨m6, e6, u6⟩ := u5'.aluImm hc22 mz_at_32 (off' := 0x36) (by decide)
    have L6 := u6.upd_ne u5'.zero
    have u6' : St (fillBytes m.mem dst v h) base m6 0x36 (reg m6) := u6.self
    obtain ⟨m7, e7, u7⟩ := u6'.aluImm hc22 mz_at_36 (off' := 0x3A) (by decide)
    have L7 := u7.upd_ne u6'.zero
    have u7' : St (fillBytes m.mem dst v h) base m7 0x3A (reg m7) := u7.self
    obtain ⟨m8, e8, u8⟩ := u7'.alu hc22 mz_at_3a (off' := 0x3E) (by decide)
    have L8 := u8.upd_ne u7'.zero
    have a1_5 : reg m5 a1 = b := by
      rw [L5 a1 (by decide), L3 a1 (by decide), L2 a1 (by decide), L1 a1 (by decide),
        K22 a1 (by decide) (by decide) (by decide) (by decide) (by decide), ha1]
    have q8 : reg m8 a5 = fillWord b := by
      have h6 : reg m6 a6 = aluEval .and b 0xFF := by rw [u6.upd_eq (by decide), a1_5]
      have h7 : reg m7 a5 = aluEval .add 0x1010000 0x101 := by
        rw [u7.upd_eq (by decide), L6 a5 (by decide), u5.upd_eq (by decide)]
      rw [u8.upd_eq (by decide), L7 a6 (by decide), h6, h7]; rfl
    have L8' : ∀ r, r ≠ a5 → r ≠ a6 → reg m8 r = reg m3 r := fun r q5 q6 => by
      rw [L8 r q5, L7 r q5, L6 r q6, L5 r q5]
    have hcw : ∀ j, j ≤ w → CodeIn (fillBytes m.mem dst v (h + 4 * j)) base memsetCode :=
      fun j hj => hcB (h + 4 * j) (by omega)
    obtain ⟨m9, c9, u9, q9, L9⟩ := fillw_loop (h := h) (w := w) hcw hal (by omega) (fillWord_byte b) w 0 m8
      (by omega) (by omega) u8.self (by rw [L8' a4 (by decide) (by decide), a4_3]; rfl) q8
      (by rw [L8' a3 (by decide) (by decide), q3])
    have hcn' : CodeIn (fillBytes m.mem dst v (h + 4 * w)) base memsetCode := hcw w (Nat.le_refl w)
    -- The bytes left over.
    let t := (n - h) % 4
    have hsum : h + 4 * w + t = n := by show h + 4 * ((n - h) / 4) + (n - h) % 4 = n; omega
    obtain ⟨m10, e10, u10⟩ := u9.aluImm hcn' mz_at_46 (off' := 0x48) (by decide)
    have q10 : reg m10 a2 = BitVec.ofNat 32 t := by
      rw [u10.upd_eq (by decide), L9 a2 (by decide), L8' a2 (by decide) (by decide), L3 a2 (by decide),
        L2 a2 (by decide), q1, and3_val (by omega)]
    have L10 := u10.upd_ne u9.zero
    have u10' : St (fillBytes m.mem dst v (h + 4 * w)) base m10 0x48 (reg m10) := u10.self
    have a3_10 : reg m10 a3 = dst + BitVec.ofNat 32 (h + 4 * w) := by
      rw [L10 a3 (by decide), L9 a3 (by decide), L8' a3 (by decide) (by decide), q3]
    obtain ⟨m11, e11, u11⟩ := u10'.alu hcn' mz_at_48 (off' := 0x4C) (by decide)
    have q11 : reg m11 a4 = dst + BitVec.ofNat 32 n := by
      rw [u11.upd_eq (by decide), a3_10, q10]
      show dst + BitVec.ofNat 32 (h + 4 * w) + BitVec.ofNat 32 t = _
      rw [add_ofNat_assoc, hsum]
    have L11 := u11.upd_ne u10'.zero
    have u11' : St (fillBytes m.mem dst v (h + 4 * w)) base m11 0x4C (reg m11) := u11.self
    have a3_11 : reg m11 a3 = dst + BitVec.ofNat 32 (h + 4 * w) := by rw [L11 a3 (by decide), a3_10]
    have K11 : ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → reg m11 r = reg m r :=
      fun r q2 q3 q4 q5 q6 => by
        rw [L11 r q4, L10 r q2, L9 r q4, L8' r q5 q6, L3 r q3, L2 r q3, L1 r q2, K22 r q2 q3 q4 q5 q6]
    have c11 : Steps m m11 := c22.trans (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6
      (.cons e7 (.cons e8 (c9.trans (.cons e10 (.single e11)))))))))))
    have ultt := ult_ofNat (dst := dst) (a := h + 4 * w) (b := n) (by omega) (by omega)
    by_cases ht : t = 0
    · have e : h + 4 * w = n := by omega
      obtain ⟨m12, e12, u12⟩ := u11'.notTaken hcn' 0x50 mz_at_4c (by decide) (by
        simp only [branchTaken]; rw [a3_11, q11, ultt]; exact decide_eq_false (by omega))
      obtain ⟨m13, e13, u13⟩ := u12.jump hcn' mz_at_50 (off' := 0x66) (by decide)
        (by rw [u12.pc, BitVec.add_assoc]; exact even_bit0 (even_at _ hbase 0x66 (by decide)))
      rw [e] at u13
      exact fin m13 (c11.trans (.cons e12 (.single e13))) u13.self
        (fun r q2 q3 q4 q5 q6 => by rw [u13.regs, K11 r q2 q3 q4 q5 q6])
    · obtain ⟨m12, e12, u12⟩ := u11'.taken hcn' 0x5C mz_at_4c (by decide) (by
        simp only [branchTaken]; rw [a3_11, q11, ultt]; exact decide_eq_true (by omega))
      obtain ⟨m13, c13, u13, _, _, f13⟩ := fill_loop (o := 0x5C) (e := n) (cnt := a2) (ptr := a3)
        (src := a1) hcB hn32 (by decide) ms_at_5c ms_at_5e ms_at_62 ms_at_64 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) t (h + 4 * w) m12 hsum (by omega) u12.self
        (by rw [u12.regs, L11 a2 (by decide), q10]) (by rw [u12.regs, a3_11])
        (by rw [u12.regs, K11 a1 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hv)
      exact fin m13 (c11.trans (.cons e12 c13)) u13
        (fun r q2 q3 q4 q5 q6 => by rw [f13 r q2 q3, u12.regs, K11 r q2 q3 q4 q5 q6])

end C3.RV32
