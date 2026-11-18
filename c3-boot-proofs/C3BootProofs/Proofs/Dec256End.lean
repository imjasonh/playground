import C3BootProofs.Proofs.Dec256Fin

/-!
# P-256 point decompression: after the final squaring

From the end of the final squaring at 0x6CA to `decompress`'s return:
compare `β²` with `α`, pick `y = ±β` by the parity it should have, and
write the point.
-/

namespace C3.RV32.Gd

open C3.Image C3.RV32.Dq C3.RV32.P3 C3.RV32.P2 C3.RV32.Fs C3.RV32.Gs

set_option maxRecDepth 20000

/-- `α^((p + 1) / 4)` in Montgomery form: a square root of `α` when one exists. -/
def gdSqrt (A : Nat) : Nat := mpow2 A sqrtExp2

/-- The square root `decompress` keeps: `β` when it squares to `α`, else 0. -/
def gdY0 (A : Nat) : Nat := if p2fm (gdSqrt A) (gdSqrt A) = A then gdSqrt A else 0

/-- The `y` `decompress` returns for `α` and the requested parity: `y₀` when
its value is odd exactly when `yodd` is, else `-y₀`. -/
def gdY (A : Nat) (yodd : Word) : Nat :=
  if p2fm (gdY0 A) 1 % 2 = yodd.toNat % 2 then gdY0 A else subGen 0 (gdY0 A)

def gdG1 : List BInstr :=
  [.aluImm .add a0 sp 0x45C, .lui a1 0x3FCC5000, .aluImm .add a1 a1 0xFFFFFB38, .aluImm .add a2 x0 0x6C]
def gdG2 : List BInstr := [.aluImm .add a0 sp 0x43C, .aluImm .add a1 sp 0xC4]
def gdG3 : List BInstr := [.aluImm .and a0 a0 0xFF]
def gdG4 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a0, .aluImm .add a0 sp 0x43C, .aluImm .add a1 sp 0x150, .aluImm .add a2 x0 0x20]
def gdG5 : List BInstr := [.sb sp (8 : Fin 32) 0x45C, .aluImm .add a0 sp 0x21C, .aluImm .add a1 sp 0x43C]
def gdG6 : List BInstr := [.aluImm .add a0 sp 0x1DC, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0]

theorem gdG1_end : blockEnd p256DecompressCode 0x6CA gdG1 = some 0x6DA := by decide
theorem gdG2_end : blockEnd p256DecompressCode 0x6E2 gdG2 = some 0x6E8 := by decide
theorem gdG3_end : blockEnd p256DecompressCode 0x6F0 gdG3 = some 0x6F4 := by decide
theorem gdG4_end : blockEnd p256DecompressCode 0x6FC gdG4 = some 0x708 := by decide
theorem gdG5_end : blockEnd p256DecompressCode 0x710 gdG5 = some 0x71A := by decide
theorem gdG6_end : blockEnd p256DecompressCode 0x722 gdG6 = some 0x72A := by decide

theorem p2params_zero : ∀ k, k < 3 → byteAt p256ParamsData (0x21 + k) = 0 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **Checking the square root**, from 0x6CA to 0x710: compare `β²` with
`α`, keep the answer in `s0`, and copy `β` to `S + 0x43C` with the
parameters behind it. -/
theorem gd_stG {M : Word → BitVec 8} {n : Machine} {S : Word} {A B : Nat} (C : GdCode M) (D : GdData M)
    (F : Fr S 0x710) (s : St M GD n 0x6CA (reg n)) (rsp : reg n sp = S)
    (hSq : accV M (S + BitVec.ofNat 32 0x43C) 8 = p2fm B B) (hB : accV M (S + BitVec.ofNat 32 0x150) 8 = B)
    (hA : accV M (S + BitVec.ofNat 32 0xC4) 8 = A) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x710 (reg n') ∧ GdCode n'.mem ∧ GdData n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x43C) 8 = B ∧
      reg n' (8 : Fin 32) = (if p2fm B B = A then 1 else 0) ∧ reg n' sp = S ∧
      (∀ k, k < 3 → n'.mem (S + BitVec.ofNat 32 (0x47D + k)) = BitVec.ofNat 8 0) ∧
      (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x43C) 0x8C x 1 → n'.mem x = M x) ∧
      ∀ q : Fin 32, q.val ∈ [3, 4, 25, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨fA, fW, hFC⟩ := F.mc
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have hb4 : (S + 0xFFFFFFFC).toNat = S.toNat - 4 := F.below 4 (by decide) (by decide)
  have hb1 : (S + 0xFFFFFFFF).toNat = S.toNat - 1 := F.below 1 (by decide) (by decide)
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have l16b : ∀ d, d + 1 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 1 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have l16 : ∀ d, d + 4 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have below : ∀ {k : Nat} {B' : Word} {x : Word}, B'.toNat = S.toNat - k → 0 < k → k ≤ 0x1A0 →
      Sep (S + 0xFFFFFE60) 0x8B0 x 1 → Sep B' k x 1 := fun {k B' x} hB' hk hk' hx => by
    have hb1A : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := hx.sub (c := 0x1A0 - k) (l := k) (by omega)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 - k) = B' by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hb1A, hB']; omega] at this
  have loK : ∀ {k : Nat} {B' : Word}, B'.toNat = S.toNat - k → k ≤ 0x1A0 → ∀ x : Word, 0x40000000 ≤ x.toNat →
      Sep B' k x 1 := fun {k B'} hB' hk x hx => sep_of_le (by rw [hB']; omega) (by have := x.isLt; omega)
  have sq : ∀ c l d, c + l ≤ 0x710 → d + 1 ≤ 0x710 → (c + l ≤ d ∨ d + 1 ≤ c) →
      Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 d) 1 := fun c l d h1 h2 h3 => sepS S h3 (by omega) (by omega)
  have al : ∀ c, c + 4 ≤ 0x710 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  have kc : ∀ {m m' : Machine}, (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg m' q = reg m q) →
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q :=
    fun h q hq => h q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  -- copy the parameters to `S + 0x45C`
  obtain ⟨n1, c1, u1⟩ := s.block gdG1 C.self gdG1_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock gdG1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, fr2, k2⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x45C) (src := P2N) (S := S) (N := 0x6C)
    (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M GD n1 0x6DA (reg n1)) C.self C.K.K gd_at_6da gd_at_6de (by decide) (by decide)
    (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdG1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdG1, upd, ↓reduceIte]; try rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdG1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    ⟨C.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide),
      (F.lowData (c := 16) (by decide) rfl (by decide) (by decide)).symm, F.bufData (by decide) (by decide) (by decide),
      fA, fW, by rw [F.at _ (by decide)]; omega, by decide⟩
  have fr2' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x45C) 0x6C x 1 → n2.mem x = M x :=
    fun x a b => by rw [fr2 x a, copyBytes_sep b (Nat.le_refl _)]
  have C2 := C.hi fun x hx => fr2' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D2 : GdData n2.mem := D.of F fun x hx => fr2' x (below hb16 (by decide) (by decide) hx) (fr_inFrame (by decide) hx)
  have hZ2 : ∀ k, k < 3 → n2.mem (S + BitVec.ofNat 32 (0x47D + k)) = BitVec.ofNat 8 0 := fun k hk => by
    rw [fr2 _ (l16b _ (by omega)), show 0x47D + k = 0x45C + (0x21 + k) by omega, ← add_ofNat_assoc S 0x45C,
      cp_at (by omega) (by decide), D.D.params (0x21 + k) (by have : p256ParamsData.length = 0x6C := rfl; omega)]
    exact p2params_zero k hk
  have k2' := kc k2
  have sp2 : reg n2 sp = S := by rw [k2' sp (by decide), r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp
  -- compare the square with `α`
  obtain ⟨n3, c3, u3⟩ := u2.block gdG2 C2.self gdG2_end ⟨trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock gdG2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, e4, fr4, k4⟩ := c2_eq8 (p := S + BitVec.ofNat 32 0x43C) (q := S + BitVec.ofNat 32 0xC4)
    (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem GD n3 0x6E8 (reg n3)) C2.self C2 F gd_at_6e8 gd_at_6ec (by decide) (by decide)
    (by rw [r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdG2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdG2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (al 0x43C (by decide) (by decide)) (al 0xC4 (by decide) (by decide))
  have C4 := C2.hi fun x hx => fr4 x (loK hb4 (by decide) x hx)
  have D4 : GdData n4.mem := D2.of F fun x hx => fr4 x (below hb4 (by decide) (by decide) hx)
  obtain ⟨n5, c5, u5⟩ := u4.block gdG3 C4.self gdG3_end ⟨trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock gdG3 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have sp5 : reg n5 sp = S := by
    rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide), k4 sp (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2
  obtain ⟨n6, c6, u6, e6, fr6, k6⟩ := c_bb
    (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem GD n5 0x6F4 (reg n5)) C4.self C4.K.K F gd_at_6f4 gd_at_6f8 (by decide)
    (by decide) sp5
  have C6 := C4.hi fun x hx => fr6 x (loK hb1 (by decide) x hx)
  have D6 : GdData n6.mem := D4.of F fun x hx => fr6 x (below hb1 (by decide) (by decide) hx)
  -- keep the answer, and copy `β` to `S + 0x43C`
  obtain ⟨n7, c7, u7⟩ := u6.block gdG4 C6.self gdG4_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r7 : ∀ q, reg n7 q = (runBlock gdG4 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  have sp6 : reg n6 sp = S := by rw [k6 sp (by decide) (by decide)]; exact sp5
  obtain ⟨n8, c8, u8, fr8, k8⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x43C) (src := S + BitVec.ofNat 32 0x150)
    (S := S) (N := 32) (⟨u7.pc, u7.mem, fun _ => rfl⟩ : St n6.mem GD n7 0x708 (reg n7)) C6.self C6.K.K gd_at_708 gd_at_70c
    (by decide) (by decide) (by rw [r7, runBlock_reg _ _ _ sp u6.zero (by decide)]; exact sp6)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, gdG4, upd, ↓reduceIte]; rw [sp6]; rfl)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, gdG4, upd, ↓reduceIte]; rw [sp6]; rfl)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, gdG4, upd, ↓reduceIte]; (try rw [u6.zero]); try rfl)
    ⟨C6.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr8' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 → n8.mem x = n6.mem x :=
    fun x a b => by rw [fr8 x a, copyBytes_sep b (Nat.le_refl _)]
  have C8 := C6.hi fun x hx => fr8' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D8 : GdData n8.mem := D6.of F fun x hx => fr8' x (below hb16 (by decide) (by decide) hx) (fr_inFrame (by decide) hx)
  have k8' := kc k8
  -- the values
  have back : ∀ d, d + 1 ≤ 0x710 → n6.mem (S + BitVec.ofNat 32 d) = n2.mem (S + BitVec.ofNat 32 d) := fun d h1 => by
    rw [fr6 _ (F.lowB hb1 (by decide) h1), fr4 _ (F.lowB hb4 (by decide) h1)]
  have hB6 : accV n6.mem (S + BitVec.ofNat 32 0x150) 8 = B := by
    rw [← hB]; exact accV_keep8 fun q hq => by
      rw [back _ (by omega), fr2' _ (l16b _ (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))]
  have hSq2 : accV n2.mem (S + BitVec.ofNat 32 0x43C) 8 = p2fm B B := by
    rw [← hSq]; exact accV_keep8 fun q hq => fr2' _ (l16b _ (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
  have hA2 : accV n2.mem (S + BitVec.ofNat 32 0xC4) 8 = A := by
    rw [← hA]; exact accV_keep8 fun q hq => fr2' _ (l16b _ (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
  have hc : (∀ i : Nat, i < 8 → memLoad32 n2.mem (S + BitVec.ofNat 32 0x43C + BitVec.ofNat 32 (4 * i)) =
      memLoad32 n2.mem (S + BitVec.ofNat 32 0xC4 + BitVec.ofNat 32 (4 * i))) ↔ p2fm B B = A := by
    rw [eq8_iff, hSq2, hA2]
  have a5 : reg n5 a0 = aluEval .and (reg n4 a0) 0xFF := by
    rw [r5]; simp +decide only [runBlock, BInstr.run, gdG3, upd, ↓reduceIte]
  have a7 : reg n7 (8 : Fin 32) = reg n6 a0 := by
    rw [r7]; simp +decide only [runBlock, BInstr.run, gdG4, upd, ↓reduceIte]; exact BitVec.zero_add _
  have KK : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 25, 26, 27] → reg n8 q = reg n q := fun q hq => by
    rw [k8' q (by revert hq; revert q; decide), r7, runBlock_reg _ _ _ q u6.zero (by simp only [gdG4]; revert hq; revert q; decide),
      k6 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), r5,
      runBlock_reg _ _ _ q u4.zero (by simp only [gdG3]; revert hq; revert q; decide),
      k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide), r3,
      runBlock_reg _ _ _ q u2.zero (by simp only [gdG2]; revert hq; revert q; decide),
      k2' q (by revert hq; revert q; decide), r1, runBlock_reg _ _ _ q hz (by simp only [gdG1]; revert hq; revert q; decide)]
  refine ⟨n8, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans c8)))))), u8, C8, D8, ?_, ?_,
    by rw [KK sp (by decide)]; exact rsp, ?_, ?_, fun q hq => KK q (by revert hq; revert q; decide)⟩
  · rw [← hB6]; exact cp_accV8 (by decide) (by decide) fun i hi => by
      rw [load_frame fr8 (l16 _ (by omega)), ← add_ofNat_assoc S 0x43C, cp_word (by omega) (by decide), add_ofNat_assoc]
  · rw [k8' 8 (by decide), a7, e6, a5, e4]
    by_cases h : p2fm B B = A
    · rw [ite_eq_left (hc.2 h), ite_eq_left h]; rfl
    · rw [ite_eq_right (fun h' => h (hc.1 h')), ite_eq_right h]; rfl
  · intro k hk
    rw [fr8' _ (l16b _ (by omega)) (sq _ _ _ (by decide) (by omega) (.inl (by omega))), back _ (by omega)]
    exact hZ2 k hk
  · intro x hx h43C
    have h45C : Sep (S + BitVec.ofNat 32 0x45C) 0x6C x 1 := by
      have := h43C.sub (c := 0x20) (l := 0x6C) (by decide); rwa [add_ofNat_assoc] at this
    have h43C' : Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 := by
      have := h43C.sub (c := 0) (l := 32) (by decide); rwa [add_ofNat_zero] at this
    have hx4 : Sep (S + 0xFFFFFFFC) 4 x 1 := by
      have := hx.sub (c := 12) (l := 4) (by decide)
      rwa [show S + 0xFFFFFFF0 + BitVec.ofNat 32 12 = S + 0xFFFFFFFC by rw [BitVec.add_assoc]; rfl] at this
    have hx1 : Sep (S + 0xFFFFFFFF) 1 x 1 := by
      have := hx.sub (c := 15) (l := 1) (by decide)
      rwa [show S + 0xFFFFFFF0 + BitVec.ofNat 32 15 = S + 0xFFFFFFFF by rw [BitVec.add_assoc]; rfl] at this
    rw [fr8' x hx h43C', fr6 x hx1, fr4 x hx4, fr2' x hx h45C]

/-! ## Choosing the root -/

def gdK2 : List BInstr :=
  [.lbu (8 : Fin 32) sp 0x23C, .aluImm .add a0 sp 0xA4, .aluImm .add a1 sp 0x1DC, .aluImm .add a2 sp 0x21C,
   .alu .add a3 x0 (8 : Fin 32)]
def gdK3 : List BInstr := [.aluImm .add a0 sp 0xC4, .aluImm .add a1 sp 0xA4]
def gdK4 : List BInstr := [.aluImm .add a0 sp 0x43C, .aluImm .add a1 sp 0xA4]
def gdK5 : List BInstr := [.lw a0 sp 0x43C, .aluImm .and a0 a0 0x1]
def gdK6 : List BInstr := [.alu .add a1 x0 (27 : Fin 32)]

theorem gdK2_end : blockEnd p256DecompressCode 0x732 gdK2 = some 0x73E := by decide
theorem gdK3_end : blockEnd p256DecompressCode 0x746 gdK3 = some 0x74A := by decide
theorem gdK4_end : blockEnd p256DecompressCode 0x752 gdK4 = some 0x758 := by decide
theorem gdK5_end : blockEnd p256DecompressCode 0x760 gdK5 = some 0x766 := by decide
theorem gdK6_end : blockEnd p256DecompressCode 0x76E gdK6 = some 0x770 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **Choosing the root**, from 0x710 to 0x778: `y₀ = β` when `c = 1`
(else 0) at `S + 0xA4`, `-y₀` at `S + 0xC4`, and in `a0` whether `y₀`'s
value has the parity `s5` asks for. -/
theorem gd_stH {M : Word → BitVec 8} {n : Machine} {S c : Word} {B : Nat} (C : GdCode M) (D : GdData M)
    (F : Fr S 0x710) (s : St M GD n 0x710 (reg n)) (rsp : reg n sp = S) (r8 : reg n (8 : Fin 32) = c)
    (hc : c = 0 ∨ c = 1) (hB : accV M (S + BitVec.ofNat 32 0x43C) 8 = B) (hBp : B < p256) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x778 (reg n') ∧ GdCode n'.mem ∧ GdData n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0xA4) 8 = (if c = 1 then B else 0) ∧
      accV n'.mem (S + BitVec.ofNat 32 0xC4) 8 = subGen 0 (if c = 1 then B else 0) ∧
      reg n' a0 = (if p2fm (if c = 1 then B else 0) 1 % 2 = (reg n (27 : Fin 32)).toNat % 2 then 1 else 0) ∧
      reg n' (8 : Fin 32) = c ∧ reg n' sp = S ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 25, 26, 27] → reg n' q = reg n q) ∧
      (∀ x, Sep (S + 0xFFFFFF4C) 0xB4 x 1 → Sep (S + BitVec.ofNat 32 0xA4) 0x40 x 1 →
        Sep (S + BitVec.ofNat 32 0x1DC) 0x61 x 1 → Sep (S + BitVec.ofNat 32 0x43C) 0x21 x 1 → n'.mem x = M x) := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hbA : (S + 0xFFFFFF4C).toNat = S.toNat - 0xB4 := F.below 0xB4 (by decide) (by decide)
  have hb80 : (S + 0xFFFFFF80).toNat = S.toNat - 0x80 := F.below 0x80 (by decide) (by decide)
  have hb60 : (S + 0xFFFFFFB0).toNat = S.toNat - 0x50 := F.below 0x50 (by decide) (by decide)
  have hb50 : (S + 0xFFFFFFC0).toNat = S.toNat - 0x40 := F.below 0x40 (by decide) (by decide)
  have hb1 : (S + 0xFFFFFFFF).toNat = S.toNat - 1 := F.below 1 (by decide) (by decide)
  have hb11 : (S + 0xFFFFFFEF).toNat = S.toNat - 0x11 := F.below 0x11 (by decide) (by decide)
  have loK : ∀ {k : Nat} {B' : Word}, B'.toNat = S.toNat - k → k ≤ 0x1A0 → ∀ x : Word, 0x40000000 ≤ x.toNat →
      Sep B' k x 1 := fun {k B'} hB' hk x hx => sep_of_le (by rw [hB']; omega) (by have := x.isLt; omega)
  have below : ∀ {k : Nat} {B' : Word} {x : Word}, B'.toNat = S.toNat - k → 0 < k → k ≤ 0x1A0 →
      Sep (S + 0xFFFFFE60) 0x8B0 x 1 → Sep B' k x 1 := fun {k B' x} hB' hk hk' hx => by
    have hb1A : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := hx.sub (c := 0x1A0 - k) (l := k) (by omega)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 - k) = B' by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hb1A, hB']; omega] at this
  have lowSub : ∀ {k : Nat} {B' : Word} {x : Word}, B'.toNat = S.toNat - k → 0 < k → k ≤ 0xB4 →
      Sep (S + 0xFFFFFF4C) 0xB4 x 1 → Sep B' k x 1 := fun {k B' x} hB' hk hk' hx => by
    have := hx.sub (c := 0xB4 - k) (l := k) (by omega)
    rwa [show S + 0xFFFFFF4C + BitVec.ofNat 32 (0xB4 - k) = B' by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hbA, hB']; omega] at this
  have inFrame : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x710 → Sep (S + 0xFFFFFE60) 0x8B0 x 1 →
      Sep (S + BitVec.ofNat 32 c) l x 1 := fun {c l x} h hx => by
    have := hx.sub (c := 0x1A0 + c) (l := l) (by omega)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
      omega] at this
  have sq : ∀ c l d, c + l ≤ 0x710 → d + 1 ≤ 0x710 → (c + l ≤ d ∨ d + 1 ≤ c) →
      Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 d) 1 := fun c l d h1 h2 h3 => sepS S h3 (by omega) (by omega)
  have al : ∀ c, c + 4 ≤ 0x710 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  -- store `c` after `β`
  obtain ⟨n1, c1, u1⟩ := s.block gdG5 C.self gdG5_end (by
    simp only [BlockOk, BInstr.ok, gdG5]; simp +decide only [and_true]
    rw [rsp]; exact F.sepHi (by decide) (by decide) (by decide))
  have r1 : ∀ q, reg n1 q = (runBlock gdG5 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore8 M (S + BitVec.ofNat 32 0x45C) (c.extractLsb' 0 8) = M1 := ⟨_, rfl⟩
  have m1 : n1.mem = M1 := by
    rw [u1.mem, ← hM1]; simp +decide only [runBlock, BInstr.run, gdG5, upd, ↓reduceIte]; rw [rsp, r8]; rfl
  have h1 : ∀ x, Sep (S + BitVec.ofNat 32 0x45C) 1 x 1 → M1 x = M x := fun x hx => by rw [← hM1]; exact dq_st8 hx
  have C1 := C.hi fun x hx => h1 x (F.hiOut (by decide) hx)
  have D1 : GdData M1 := D.of F fun x hx => h1 x (inFrame (by decide) hx)
  have t1 : St M1 GD n1 0x71A (reg n1) := ⟨u1.pc, m1, fun _ => rfl⟩
  have sp1 : reg n1 sp = S := by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp
  have e65C : S + BitVec.ofNat 32 0x43C + 0x20 = S + BitVec.ofNat 32 0x45C := by rw [BitVec.add_assoc]; rfl
  have hcb : M1 (S + BitVec.ofNat 32 0x43C + 0x20) = c.extractLsb' 0 8 := by rw [e65C, ← hM1]; exact memStore8_same _ _ _
  have hcb01 : M1 (S + BitVec.ofNat 32 0x43C + 0x20) = 0 ∨ M1 (S + BitVec.ofNat 32 0x43C + 0x20) = 1 := by
    rw [hcb]; rcases hc with h | h <;> rw [h] <;> decide
  -- the root as a `CtOption`
  obtain ⟨n2, c2, u2, w2, b2, fr2, sp2, k2⟩ := c2_cmap (out := S + BitVec.ofNat 32 0x21C) (x := S + BitVec.ofNat 32 0x43C)
    (co := 0x21C) (cx := 0x43C) t1 C1.self C1.K C1 F gd_at_71a gd_at_71e (by decide) (by decide) sp1
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdG5, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdG5, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by decide) (by decide) rfl rfl (by decide) hcb01
  have C2 := C1.hi fun x hx => fr2 x (loK hb80 (by decide) x hx) (F.hiOut (by decide) hx)
  have D2 : GdData n2.mem := D1.of F fun x hx => fr2 x (below hb80 (by decide) (by decide) hx) (inFrame (by decide) hx)
  -- zero
  obtain ⟨n3, c3, u3⟩ := u2.block gdG6 C2.self gdG6_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock gdG6 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, m4, k4⟩ := c_memset (dst := S + BitVec.ofNat 32 0x1DC) (b := 0) (N := 32)
    (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem GD n3 0x72A (reg n3)) C2.self C2.K.K gd_at_72a gd_at_72e (by decide) (by decide)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdG6, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdG6, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdG6, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [F.at _ (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  have fr4 : ∀ x, Sep (S + BitVec.ofNat 32 0x1DC) 32 x 1 → n4.mem x = n2.mem x := fun x hx => by
    rw [m4]; exact fillBytes_sep hx (Nat.le_refl _)
  have C4 := C2.hi fun x hx => fr4 x (F.hiOut (by decide) hx)
  have D4 : GdData n4.mem := D2.of F fun x hx => fr4 x (inFrame (by decide) hx)
  have k4' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n2 q := fun q hq => by
    rw [k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r3, runBlock_reg _ _ _ q u2.zero (by simp only [gdG6]; revert hq; revert q; decide)]
  have sp4 : reg n4 sp = S := by rw [k4' sp (by decide)]; exact sp2
  -- select `y₀`
  obtain ⟨n5, c5, u5⟩ := u4.block gdK2 C4.self gdK2_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock gdK2 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have e58 : reg n5 (8 : Fin 32) = c := by
    rw [r5]; simp +decide only [runBlock, BInstr.run, gdK2, upd, ↓reduceIte]; rw [sp4]
    show (n4.mem (S + BitVec.ofNat 32 0x23C)).zeroExtend 32 = c
    rw [fr4 _ (sq _ _ _ (by decide) (by decide) (.inl (by decide))),
      show S + BitVec.ofNat 32 0x23C = S + BitVec.ofNat 32 0x21C + 0x20 by rw [BitVec.add_assoc]; rfl, b2, hcb]
    rcases hc with h | h <;> rw [h] <;> decide
  obtain ⟨n6, c6, u6, w6, fr6, sp6, k6⟩ := c2_csel (out := S + BitVec.ofNat 32 0xA4) (a := S + BitVec.ofNat 32 0x1DC)
    (b := S + BitVec.ofNat 32 0x21C) (c := c) (co := 0xA4) (ca := 0x1DC) (cb := 0x21C)
    (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem GD n5 0x73E (reg n5)) C4.self C4.K F gd_at_73e gd_at_742 (by decide) (by decide)
    (by rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gdK2, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gdK2, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gdK2, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, gdK2, upd, ↓reduceIte]; rw [← e58, r5]
        simp +decide only [runBlock, BInstr.run, gdK2, upd, ↓reduceIte]; exact BitVec.zero_add _)
    hc (by decide) (by decide) (by decide) rfl rfl rfl (by decide)
  have C6 := C4.hi fun x hx => fr6 x (loK hb60 (by decide) x hx) (F.hiOut (by decide) hx)
  have D6 : GdData n6.mem := D4.of F fun x hx => fr6 x (below hb60 (by decide) (by decide) hx) (inFrame (by decide) hx)
  have hY : accV n6.mem (S + BitVec.ofNat 32 0xA4) 8 = (if c = 1 then B else 0) := by
    rcases hc with h0 | h0
    · rw [ite_eq_right (by rw [h0]; decide)]
      exact accV_zero 8 fun i hi => by
        rw [w6 i hi, ite_eq_right (by rw [h0]; decide), m4, fill_word0 (by omega) (by decide)]
    · rw [ite_eq_left h0, ← hB]
      have hcb1 : M1 (S + BitVec.ofNat 32 0x43C + 0x20) = 1 := by rw [hcb, h0]; decide
      refine accV_congr2 8 fun i hi => ?_
      rw [w6 i hi, ite_eq_left h0, add_ofNat_assoc, m4,
        fill_word_out (sepS S (.inl (by omega)) (by decide) (by omega)), ← add_ofNat_assoc, w2 i hi, ite_eq_left hcb1,
        add_ofNat_assoc]
      exact load_frame h1 (sepS S (.inr (by omega)) (by decide) (by omega))
  have hYp : (if c = 1 then B else 0) < p256 := by
    rcases hc with h0 | h0
    · rw [ite_eq_right (by rw [h0]; decide)]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hBp
    · rw [ite_eq_left h0]; exact hBp
  have K6 : ∀ q : Fin 32, q.val ∈ [3, 4, 25, 26, 27] → reg n6 q = reg n q := fun q hq => by
    rw [k6 q (by revert hq; revert q; decide), r5, runBlock_reg _ _ _ q u4.zero (by simp only [gdK2]; revert hq; revert q; decide),
      k4' q (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide), r1, runBlock_reg _ _ _ q hz (by simp only [gdG5]; revert hq; revert q; decide)]
  have e68 : reg n6 (8 : Fin 32) = c := by rw [k6 8 (by decide), e58]
  -- negate
  obtain ⟨n7, c7, u7⟩ := u6.block gdK3 C6.self gdK3_end ⟨trivial, trivial, trivial⟩
  have r7 : ∀ q, reg n7 q = (runBlock gdK3 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  obtain ⟨n8, c8, u8, e8, fr8, sp8, k8⟩ := c2_neg (out := S + BitVec.ofNat 32 0xC4) (xp := S + BitVec.ofNat 32 0xA4)
    (co := 0xC4) (cx := 0xA4) (⟨u7.pc, u7.mem, fun _ => rfl⟩ : St n6.mem GD n7 0x74A (reg n7)) C6.self C6.K C6 D6 F gd_at_74a gd_at_74e
    (by decide) (by decide) (by rw [r7, runBlock_reg _ _ _ sp u6.zero (by decide)]; exact sp6)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, gdK3, upd, ↓reduceIte]; rw [sp6]; rfl)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, gdK3, upd, ↓reduceIte]; rw [sp6]; rfl)
    (by decide) (by decide) rfl rfl (by decide) (by decide)
  have C8 := C6.hi fun x hx => fr8 x (loK hbA (by decide) x hx) (F.hiOut (by decide) hx)
  have D8 : GdData n8.mem := D6.of F fun x hx => fr8 x (below hbA (by decide) (by decide) hx) (inFrame (by decide) hx)
  have hN8 : accV n8.mem (S + BitVec.ofNat 32 0xC4) 8 = subGen 0 (if c = 1 then B else 0) := by rw [e8, hY]
  have hY8 : accV n8.mem (S + BitVec.ofNat 32 0xA4) 8 = (if c = 1 then B else 0) := by
    rw [← hY]; exact accV_keep8 fun q hq =>
      fr8 _ (F.lowB hbA (by decide) (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
  -- out of Montgomery form
  obtain ⟨n9, c9, u9⟩ := u8.block gdK4 C8.self gdK4_end ⟨trivial, trivial, trivial⟩
  have r9 : ∀ q, reg n9 q = (runBlock gdK4 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
  obtain ⟨n10, c10, u10, e10, fr10, sp10, k10⟩ := c2_rt (out := S + BitVec.ofNat 32 0x43C) (xp := S + BitVec.ofNat 32 0xA4)
    (co := 0x43C) (cx := 0xA4) (⟨u9.pc, u9.mem, fun _ => rfl⟩ : St n8.mem GD n9 0x758 (reg n9)) C8.self C8.K C8 D8.D F gd_at_758 gd_at_75c
    (by decide) (by decide) (by rw [r9, runBlock_reg _ _ _ sp u8.zero (by decide)]; exact sp8)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, gdK4, upd, ↓reduceIte]; rw [sp8]; rfl)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, gdK4, upd, ↓reduceIte]; rw [sp8]; rfl)
    (by decide) (by decide) rfl rfl (by decide) (by decide) (by rw [hY8]; exact hYp)
  have C10 := C8.hi fun x hx => fr10 x (loK hb50 (by decide) x hx) (F.hiOut (by decide) hx)
  have D10 : GdData n10.mem := D8.of F fun x hx => fr10 x (below hb50 (by decide) (by decide) hx) (inFrame (by decide) hx)
  -- the parity
  obtain ⟨n11, c11, u11⟩ := u10.block gdK5 C10.self gdK5_end (by
    simp only [BlockOk, BInstr.ok, gdK5]; simp +decide only [and_true]
    rw [sp10]; exact al 0x43C (by decide) (by decide))
  have r11 : ∀ q, reg n11 q = (runBlock gdK5 (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
  have a11 : reg n11 a0 = memLoad32 n10.mem (S + BitVec.ofNat 32 0x43C) &&& 1 := by
    rw [r11]; simp +decide only [runBlock, BInstr.run, gdK5, upd, ↓reduceIte]; rw [sp10]; rfl
  have sp11 : reg n11 sp = S := by rw [r11, runBlock_reg _ _ _ sp u10.zero (by decide)]; exact sp10
  obtain ⟨n12, c12, u12, e12, fr12, k12⟩ := c_bb
    (⟨u11.pc, u11.mem, fun _ => rfl⟩ : St n10.mem GD n11 0x766 (reg n11)) C10.self C10.K.K F gd_at_766 gd_at_76a (by decide) (by decide) sp11
  have C12 := C10.hi fun x hx => fr12 x (loK hb1 (by decide) x hx)
  have D12 : GdData n12.mem := D10.of F fun x hx => fr12 x (below hb1 (by decide) (by decide) hx)
  obtain ⟨n13, c13, u13⟩ := u12.block gdK6 C12.self gdK6_end ⟨trivial, trivial⟩
  have r13 : ∀ q, reg n13 q = (runBlock gdK6 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
  have KB : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 25, 26, 27] → reg n12 q = reg n6 q := fun q hq => by
    rw [k12 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), r11, runBlock_reg _ _ _ q u10.zero (by simp only [gdK5]; revert hq; revert q; decide),
      k10 q (by revert hq; revert q; decide), r9, runBlock_reg _ _ _ q u8.zero (by simp only [gdK4]; revert hq; revert q; decide),
      k8 q (by revert hq; revert q; decide), r7, runBlock_reg _ _ _ q u6.zero (by simp only [gdK3]; revert hq; revert q; decide)]
  have sp12 : reg n12 sp = S := by rw [k12 sp (by decide) (by decide)]; exact sp11
  obtain ⟨n14, c14, u14, e14, fr14, k14⟩ := c2_cte
    (a := ((memLoad32 n10.mem (S + BitVec.ofNat 32 0x43C) &&& 1).extractLsb' 0 8).zeroExtend 32) (b := reg n (27 : Fin 32))
    (⟨u13.pc, u13.mem, fun _ => rfl⟩ : St n12.mem GD n13 0x770 (reg n13)) C12.self C12.K C12 F gd_at_770 gd_at_774 (by decide) (by decide)
    (by rw [r13, runBlock_reg _ _ _ sp u12.zero (by decide)]; exact sp12)
    (by rw [r13, runBlock_reg _ _ _ a0 u12.zero (by decide), e12, a11])
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, gdK6, upd, ↓reduceIte]
        rw [KB 27 (by decide), K6 27 (by decide)]; exact BitVec.zero_add _)
  have C14 := C12.hi fun x hx => fr14 x (loK hb11 (by decide) x hx)
  have D14 : GdData n14.mem := D12.of F fun x hx => fr14 x (below hb11 (by decide) (by decide) hx)
  have back : ∀ d, d + 1 ≤ 0x710 → (d + 1 ≤ 0x43C ∨ 0x45C ≤ d) → n14.mem (S + BitVec.ofNat 32 d) = n8.mem (S + BitVec.ofNat 32 d) :=
    fun d h1 h2 => by
      rw [fr14 _ (F.lowB hb11 (by decide) h1), fr12 _ (F.lowB hb1 (by decide) h1),
        fr10 _ (F.lowB hb50 (by decide) h1) (sq _ _ _ (by decide) h1 (by rcases h2 with h | h; exact .inr h; exact .inl h))]
  have hpar : (memLoad32 n10.mem (S + BitVec.ofNat 32 0x43C)).toNat % 2 = p2fm (if c = 1 then B else 0) 1 % 2 := by
    have := Dq.accV_low (M := n10.mem) (b := S + BitVec.ofNat 32 0x43C) 7
    rw [show 7 + 1 = 8 from rfl, e10, hY8] at this
    rw [← this, Nat.mod_mod_of_dvd _ (by decide)]
  refine ⟨n14, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans
    (c11.trans (c12.trans (c13.trans c14)))))))))))), u14, C14, D14, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hY8]; exact accV_keep8 fun q hq => back _ (by omega) (.inl (by omega))
  · rw [← hN8]; exact accV_keep8 fun q hq => back _ (by omega) (.inl (by omega))
  · rw [e14]
    by_cases h : p2fm (if c = 1 then B else 0) 1 % 2 = (reg n (27 : Fin 32)).toNat % 2
    · rw [ite_eq_left ((par_iff _ _).2 (by rw [hpar]; exact h)), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (by rw [← hpar]; exact (par_iff _ _).1 h')), ite_eq_right h]
  · rw [k14 8 (by decide) (by decide) (by decide), r13, runBlock_reg _ _ _ 8 u12.zero (by decide), KB 8 (by decide), e68]
  · rw [k14 sp (by decide) (by decide) (by decide), r13, runBlock_reg _ _ _ sp u12.zero (by decide)]; exact sp12
  · intro q hq
    rw [k14 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r13, runBlock_reg _ _ _ q u12.zero (by simp only [gdK6]; revert hq; revert q; decide),
      KB q (by revert hq; revert q; decide), K6 q hq]
  · intro x hx hD4 h29C h62C
    have sub0 : ∀ {b : Word} {l l' : Nat}, l' ≤ l → Sep b l x 1 → Sep b l' x 1 := fun {b l l'} hl h => by
      have := h.sub (c := 0) (l := l') (by omega); rwa [add_ofNat_zero] at this
    have hD104 : Sep (S + BitVec.ofNat 32 0xC4) 32 x 1 := by
      have := hD4.sub (c := 0x20) (l := 32) (by decide); rwa [add_ofNat_assoc] at this
    have h2FC : Sep (S + BitVec.ofNat 32 0x21C) 0x21 x 1 := by
      have := h29C.sub (c := 0x40) (l := 0x21) (by decide); rwa [add_ofNat_assoc] at this
    have h65C : Sep (S + BitVec.ofNat 32 0x45C) 1 x 1 := by
      have := h62C.sub (c := 0x20) (l := 1) (by decide); rwa [add_ofNat_assoc] at this
    rw [fr14 x (lowSub hb11 (by decide) (by decide) hx), fr12 x (lowSub hb1 (by decide) (by decide) hx),
      fr10 x (lowSub hb50 (by decide) (by decide) hx) (sub0 (by decide) h62C),
      fr8 x (lowSub hbA (by decide) (by decide) hx) hD104, fr6 x (lowSub hb60 (by decide) (by decide) hx) (sub0 (by decide) hD4),
      fr4 x (sub0 (by decide) h29C), fr2 x (lowSub hb80 (by decide) (by decide) hx) h2FC]
    exact h1 x h65C

/-! ## Writing the point -/

def gdI0 : List BInstr :=
  [.aluImm .add a4 sp 0x45C, .aluImm .and a3 a0 0xFF, .aluImm .add a1 sp 0xC4, .aluImm .add a2 sp 0xA4, .alu .add a0 x0 a4]
def gdI1 : List BInstr := [.aluImm .add a0 sp 0x43C, .aluImm .add a1 sp 0x84, .aluImm .add a2 x0 0x20]
def gdI2 : List BInstr := [.sb sp x0 0x47C, .alu .and a0 (8 : Fin 32) (26 : Fin 32)]
def gdI3 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a0, .aluImm .add a1 sp 0x43C, .aluImm .add a2 x0 0x44, .alu .add a0 x0 (25 : Fin 32)]
def gdI4a : List BInstr := [.sb (25 : Fin 32) (8 : Fin 32) 0x44]
def gdI4b : List BInstr :=
  [.aluImm .add a0 sp 0x700, .lw ra a0 0xC, .lw (8 : Fin 32) a0 0x8, .lw (9 : Fin 32) a0 0x4, .lw (18 : Fin 32) a0 0x0,
   .aluImm .add a0 sp 0x680, .lw (19 : Fin 32) a0 0x7C, .lw (20 : Fin 32) a0 0x78, .lw (21 : Fin 32) a0 0x74,
   .lw (22 : Fin 32) a0 0x70, .lw (23 : Fin 32) a0 0x6C, .lw (24 : Fin 32) a0 0x68, .lw (25 : Fin 32) a0 0x64,
   .lw (26 : Fin 32) a0 0x60, .lw (27 : Fin 32) a0 0x5C, .aluImm .add sp sp 0x710]

theorem gdI0_end : blockEnd p256DecompressCode 0x778 gdI0 = some 0x786 := by decide
theorem gdI1_end : blockEnd p256DecompressCode 0x78E gdI1 = some 0x798 := by decide
theorem gdI2_end : blockEnd p256DecompressCode 0x7A0 gdI2 = some 0x7A8 := by decide
theorem gdI3_end : blockEnd p256DecompressCode 0x7B0 gdI3 = some 0x7BC := by decide
theorem gdI4a_end : blockEnd p256DecompressCode 0x7C4 gdI4a = some 0x7C8 := by decide
theorem gdI4b_end : blockEnd p256DecompressCode 0x7C8 gdI4b = some 0x804 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **Writing the point**, from 0x696 to the return: `y` is `y₀` or `-y₀`
by the parity test, and `decompress` writes `x`, `y`, the identity flag 0,
and `c ∧ ok` as the choice to `out`, then restores the saved registers. -/
theorem gd_stI {M : Word → BitVec 8} {n : Machine} {S out par c ok : Word} {X Y0 N0 : Nat} {v : Nat → Word}
    (C : GdCode M) (D : GdData M) (F : Fr S 0x710) (s : St M GD n 0x778 (reg n)) (rsp : reg n sp = S)
    (ra0 : reg n a0 = par) (hpar : par = 0 ∨ par = 1) (r8 : reg n (8 : Fin 32) = c) (hc : c = 0 ∨ c = 1)
    (r19 : reg n (25 : Fin 32) = out) (r20 : reg n (26 : Fin 32) = ok) (hok : ok = 0 ∨ ok = 1)
    (sO : Sep out 0x45 (S + 0xFFFFFE60) 0x8B0) (hO : out.toNat + 0x45 ≤ 0x40000000)
    (hX : accV M (S + BitVec.ofNat 32 0x84) 8 = X) (hY : accV M (S + BitVec.ofNat 32 0xA4) 8 = Y0)
    (hN : accV M (S + BitVec.ofNat 32 0xC4) 8 = N0)
    (hZ : ∀ k, k < 3 → M (S + BitVec.ofNat 32 (0x47D + k)) = BitVec.ofNat 8 0)
    (hS : ∀ k, k < 13 → memLoad32 M (S + BitVec.ofNat 32 (0x70C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0) :
    ∃ n', Steps n n' ∧ n'.pc = v 0 ∧ reg n' sp = S + 0x710 ∧ (∀ k, k < 13 → reg n' (savedReg k) = v k) ∧
      accV n'.mem out 8 = X ∧ accV n'.mem (out + BitVec.ofNat 32 0x20) 8 = (if par = 1 then Y0 else N0) ∧
      (∀ k, k < 4 → n'.mem (out + BitVec.ofNat 32 (0x40 + k)) = BitVec.ofNat 8 0) ∧
      n'.mem (out + BitVec.ofNat 32 0x44) = (if c = 1 ∧ ok = 1 then 1 else 0) ∧
      reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) ∧
      ∀ x, Sep (S + 0xFFFFFE60) 0x8B0 x 1 → Sep out 0x45 x 1 → n'.mem x = M x := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨fA, fW, hFC⟩ := F.mc
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have hb60 : (S + 0xFFFFFFB0).toNat = S.toNat - 0x50 := F.below 0x50 (by decide) (by decide)
  have hb1 : (S + 0xFFFFFFFF).toNat = S.toNat - 1 := F.below 1 (by decide) (by decide)
  have loK : ∀ {k : Nat} {B' : Word}, B'.toNat = S.toNat - k → k ≤ 0x1A0 → ∀ x : Word, 0x40000000 ≤ x.toNat →
      Sep B' k x 1 := fun {k B'} hB' hk x hx => sep_of_le (by rw [hB']; omega) (by have := x.isLt; omega)
  have below : ∀ {k : Nat} {B' : Word} {x : Word}, B'.toNat = S.toNat - k → 0 < k → k ≤ 0x1A0 →
      Sep (S + 0xFFFFFE60) 0x8B0 x 1 → Sep B' k x 1 := fun {k B' x} hB' hk hk' hx => by
    have hb1A : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := hx.sub (c := 0x1A0 - k) (l := k) (by omega)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 - k) = B' by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hb1A, hB']; omega] at this
  have inFrame : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x710 → Sep (S + 0xFFFFFE60) 0x8B0 x 1 →
      Sep (S + BitVec.ofNat 32 c) l x 1 := fun {c l x} h hx => by
    have := hx.sub (c := 0x1A0 + c) (l := l) (by omega)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
      omega] at this
  have l16b : ∀ d, d + 1 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 1 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have l16 : ∀ d, d + 4 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have sq : ∀ c l d, c + l ≤ 0x710 → d + 1 ≤ 0x710 → (c + l ≤ d ∨ d + 1 ≤ c) →
      Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 d) 1 := fun c l d h1 h2 h3 => sepS S h3 (by omega) (by omega)
  have oF : ∀ j, j < 0x45 → Sep (S + 0xFFFFFE60) 0x8B0 (out + BitVec.ofNat 32 j) 1 := fun j hj =>
    (sO.sub (c := j) (l := 1) (by omega)).symm
  have oAt : ∀ j, j ≤ 0x45 → (out + BitVec.ofNat 32 j).toNat = out.toNat + j := fun j hj => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have oLow : ∀ {k : Nat} {B' : Word}, B'.toNat = S.toNat - k → 0 < k → k ≤ 0x1A0 → Sep out 0x45 B' k :=
    fun {k B'} hB' hk hk' => by
      have hb1A : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
      have := sO.subR (c := 0x1A0 - k) (l := k) (by omega)
      rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 - k) = B' by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hb1A, hB']; omega] at this
  have oBuf : ∀ {c l : Nat}, c + l ≤ 0x710 → Sep out 0x45 (S + BitVec.ofNat 32 c) l := fun {c l} h => by
    have := sO.subR (c := 0x1A0 + c) (l := l) (by omega)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
      omega] at this
  have shr : ∀ {a b : Word} {l l' k : Nat}, l' ≤ l → Sep a l b k → Sep a l' b k := fun {a b l l' k} hl h => by
    have := h.sub (c := 0) (l := l') (by omega); rwa [add_ofNat_zero] at this
  have oHi : ∀ {x : Word}, 0x40000000 ≤ x.toNat → Sep out 0x45 x 1 := fun {x} hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have kc : ∀ {m m' : Machine}, (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg m' q = reg m q) →
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q :=
    fun h q hq => h q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  -- select `y`
  obtain ⟨n1, c1, u1⟩ := s.block gdI0 C.self gdI0_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock gdI0 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have hpar' : aluEval .and par 0xFF = par := by rcases hpar with h | h <;> rw [h] <;> decide
  obtain ⟨n2, c2, u2, w2, fr2, sp2, k2⟩ := c2_csel (out := S + BitVec.ofNat 32 0x45C) (a := S + BitVec.ofNat 32 0xC4)
    (b := S + BitVec.ofNat 32 0xA4) (c := par) (co := 0x45C) (ca := 0xC4) (cb := 0xA4)
    (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M GD n1 0x786 (reg n1)) C.self C.K F gd_at_786 gd_at_78a (by decide) (by decide)
    (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdI0, upd, ↓reduceIte]; rw [rsp]; exact BitVec.zero_add _)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdI0, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdI0, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdI0, upd, ↓reduceIte]; rw [ra0]; exact hpar')
    hpar (by decide) (by decide) (by decide) rfl rfl rfl (by decide)
  have C2 := C.hi fun x hx => fr2 x (loK hb60 (by decide) x hx) (F.hiOut (by decide) hx)
  have D2 : GdData n2.mem := D.of F fun x hx => fr2 x (below hb60 (by decide) (by decide) hx) (inFrame (by decide) hx)
  have K2 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 25, 26] → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1, runBlock_reg _ _ _ q hz (by simp only [gdI0]; revert hq; revert q; decide)]
  -- copy `x`
  obtain ⟨n3, c3, u3⟩ := u2.block gdI1 C2.self gdI1_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock gdI1 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, fr4, k4⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x43C) (src := S + BitVec.ofNat 32 0x84)
    (S := S) (N := 32) (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem GD n3 0x798 (reg n3)) C2.self C2.K.K gd_at_798 gd_at_79c
    (by decide) (by decide) (by rw [r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdI1, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdI1, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdI1, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    ⟨C2.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr4' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 → n4.mem x = n2.mem x :=
    fun x a b => by rw [fr4 x a, copyBytes_sep b (Nat.le_refl _)]
  have C4 := C2.hi fun x hx => fr4' x (loK hb16 (by decide) x hx) (F.hiOut (by decide) hx)
  have k4' := kc k4
  have sp4 : reg n4 sp = S := by rw [k4' sp (by decide), r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2
  -- the identity flag, and the choice
  obtain ⟨n5, c5, u5⟩ := u4.block gdI2 C4.self gdI2_end (by
    simp only [BlockOk, BInstr.ok, gdI2]; simp +decide only [and_true]
    rw [sp4]; exact F.sepHi (by decide) (by decide) (by decide))
  have r5 : ∀ q, reg n5 q = (runBlock gdI2 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  obtain ⟨M5, hM5⟩ : ∃ M5, memStore8 n4.mem (S + BitVec.ofNat 32 0x47C) ((0 : Word).extractLsb' 0 8) = M5 := ⟨_, rfl⟩
  have m5 : n5.mem = M5 := by
    rw [u5.mem, ← hM5]; simp +decide only [runBlock, BInstr.run, gdI2, upd, ↓reduceIte]; rw [sp4, u4.zero]; rfl
  have h5 : ∀ x, Sep (S + BitVec.ofNat 32 0x47C) 1 x 1 → M5 x = n4.mem x := fun x hx => by rw [← hM5]; exact dq_st8 hx
  have C5 := C4.hi fun x hx => h5 x (F.hiOut (by decide) hx)
  have sp5 : reg n5 sp = S := by rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4
  obtain ⟨n6, c6, u6, e6, fr6, k6⟩ := c_bb (⟨u5.pc, m5, fun _ => rfl⟩ : St M5 GD n5 0x7A8 (reg n5)) C5.self C5.K.K F gd_at_7a8 gd_at_7ac
    (by decide) (by decide) sp5
  have C6 := C5.hi fun x hx => fr6 x (loK hb1 (by decide) x hx)
  -- copy the point to `out`
  obtain ⟨n7, c7, u7⟩ := u6.block gdI3 C6.self gdI3_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r7 : ∀ q, reg n7 q = (runBlock gdI3 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  have sp6 : reg n6 sp = S := by rw [k6 sp (by decide) (by decide)]; exact sp5
  have K6 : ∀ q : Fin 32, q.val ∈ [3, 4, 25, 26] → reg n6 q = reg n q := fun q hq => by
    rw [k6 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), r5, runBlock_reg _ _ _ q u4.zero (by simp only [gdI2]; revert hq; revert q; decide),
      k4' q (by revert hq; revert q; decide), r3, runBlock_reg _ _ _ q u2.zero (by simp only [gdI1]; revert hq; revert q; decide), K2 q (by revert hq; revert q; decide)]
  have e78 : reg n7 (8 : Fin 32) = ((c &&& ok).extractLsb' 0 8).zeroExtend 32 := by
    rw [r7]; simp +decide only [runBlock, BInstr.run, gdI3, upd, ↓reduceIte]
    rw [e6, r5]; simp +decide only [runBlock, BInstr.run, gdI2, upd, ↓reduceIte]
    rw [k4' 8 (by decide), r3, runBlock_reg _ _ _ 8 u2.zero (by decide), K2 8 (by decide), r8,
      k4' 26 (by decide), r3, runBlock_reg _ _ _ 26 u2.zero (by decide), K2 26 (by decide), r20]
    exact BitVec.zero_add _
  have hMC : Sep out 0x44 (MCS + 8) memcpyBodyCode.length := by
    have : 0x40000000 ≤ (MCS + 8 : Word).toNat := by decide
    exact sep_of_le (by omega) (by decide)
  obtain ⟨n8, c8, u8, fr8, k8⟩ := c_memcpy (dst := out) (src := S + BitVec.ofNat 32 0x43C) (S := S) (N := 0x44)
    (⟨u7.pc, u7.mem, fun _ => rfl⟩ : St n6.mem GD n7 0x7BC (reg n7)) C6.self C6.K.K gd_at_7bc gd_at_7c0 (by decide) (by decide)
    (by rw [r7, runBlock_reg _ _ _ sp u6.zero (by decide)]; exact sp6)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, gdI3, upd, ↓reduceIte]; rw [K6 25 (by decide), r19]
        exact BitVec.zero_add _)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, gdI3, upd, ↓reduceIte]; rw [sp6]; rfl)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, gdI3, upd, ↓reduceIte]; (try rw [u6.zero]); try rfl)
    ⟨C6.K.K.body, hMC, hFC, shr (by decide) (oLow hb16 (by decide) (by decide)),
      F.mcN (by decide), shr (by decide) (oBuf (by decide)), fA, fW, by omega, by rw [F.at _ (by decide)]; omega⟩
  have fr8' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep out 0x44 x 1 → n8.mem x = n6.mem x :=
    fun x a b => by rw [fr8 x a, copyBytes_sep b (Nat.le_refl _)]
  have C8 := C6.hi fun x hx => fr8' x (loK hb16 (by decide) x hx) (shr (by decide) (oHi hx))
  have k8' := kc k8
  have sp8 : reg n8 sp = S := by rw [k8' sp (by decide), r7, runBlock_reg _ _ _ sp u6.zero (by decide)]; exact sp6
  have K8 : ∀ q : Fin 32, q.val ∈ [3, 4, 25] → reg n8 q = reg n q := fun q hq => by
    rw [k8' q (by revert hq; revert q; decide), r7, runBlock_reg _ _ _ q u6.zero (by simp only [gdI3]; revert hq; revert q; decide), K6 q (by revert hq; revert q; decide)]
  -- store the choice
  have hO64 : Sep (out + 0x44) 1 GD p256DecompressCode.length := by
    have : 0x40000000 ≤ GD.toNat := by decide
    exact sep_of_le (by rw [show (out + 0x44 : Word) = out + BitVec.ofNat 32 0x44 from rfl, oAt 0x44 (by decide)]; omega)
      (by decide)
  obtain ⟨n9, c9, u9⟩ := u8.block gdI4a C8.self gdI4a_end (by
    simp only [BlockOk, BInstr.ok, gdI4a]; simp +decide only [and_true]
    rw [K8 25 (by decide), r19]; exact hO64)
  obtain ⟨M9, hM9⟩ : ∃ M9, memStore8 n8.mem (out + BitVec.ofNat 32 0x44)
      ((((c &&& ok).extractLsb' 0 8).zeroExtend 32 : Word).extractLsb' 0 8) = M9 := ⟨_, rfl⟩
  have m9 : n9.mem = M9 := by
    rw [u9.mem, ← hM9]; simp +decide only [runBlock, BInstr.run, gdI4a, upd, ↓reduceIte]
    rw [K8 25 (by decide), r19, k8' 8 (by decide), e78]; rfl
  have h9 : ∀ x, Sep (out + BitVec.ofNat 32 0x44) 1 x 1 → M9 x = n8.mem x := fun x hx => by rw [← hM9]; exact dq_st8 hx
  have C9 := C8.hi fun x hx => h9 x ((oHi hx).sub (c := 0x44) (l := 1) (by decide))
  have r9 : ∀ q, reg n9 q = reg n8 q := fun q => by rw [u9.regs]; rfl
  have sp9 : reg n9 sp = S := by rw [r9]; exact sp8
  -- what memory holds now
  have sub60 : ∀ {k : Nat} {B' : Word} {x : Word}, B'.toNat = S.toNat - k → 0 < k → k ≤ 0x50 →
      Sep (S + 0xFFFFFFB0) 0x50 x 1 → Sep B' k x 1 := fun {k B' x} hB' hk hk' hx => by
    have := hx.sub (c := 0x50 - k) (l := k) (by omega)
    rwa [show S + 0xFFFFFFB0 + BitVec.ofNat 32 (0x50 - k) = B' by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hb60, hB']; omega] at this
  have fin : ∀ x, Sep (S + 0xFFFFFFB0) 0x50 x 1 → Sep (S + BitVec.ofNat 32 0x43C) 0x41 x 1 → Sep out 0x45 x 1 →
      M9 x = M x := fun x hl hb ho => by
    have hb48 : Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 := shr (by decide) hb
    have h65C : Sep (S + BitVec.ofNat 32 0x45C) 32 x 1 := by
      have := hb.sub (c := 0x20) (l := 32) (by decide); rwa [add_ofNat_assoc] at this
    have h68C : Sep (S + BitVec.ofNat 32 0x47C) 1 x 1 := by
      have := hb.sub (c := 0x40) (l := 1) (by decide); rwa [add_ofNat_assoc] at this
    rw [h9 x (ho.sub (c := 0x44) (l := 1) (by decide)), fr8' x (sub60 hb16 (by decide) (by decide) hl) (shr (by decide) ho),
      fr6 x (sub60 hb1 (by decide) (by decide) hl), h5 x h68C, fr4' x (sub60 hb16 (by decide) (by decide) hl) hb48,
      fr2 x hl h65C]
  have lowOut : ∀ j, j < 0x45 → Sep (S + 0xFFFFFFF0) 16 (out + BitVec.ofNat 32 j) 1 := fun j hj =>
    below hb16 (by decide) (by decide) (oF j hj)
  have sepO : ∀ j, j + 1 ≤ 0x44 → Sep (out + BitVec.ofNat 32 0x44) 1 (out + BitVec.ofNat 32 j) 1 := fun j hj =>
    sep_offsets out (.inr (by omega)) (by omega) (by omega)
  have byB : ∀ k, k < 0x44 → M9 (out + BitVec.ofNat 32 k) = n6.mem (S + BitVec.ofNat 32 (0x43C + k)) := fun k hk => by
    rw [h9 _ (sepO k (by omega)), fr8 _ (lowOut k (by omega)), cp_at hk (by decide), add_ofNat_assoc]
  have ldB : ∀ k, k + 4 ≤ 0x44 → memLoad32 M9 (out + BitVec.ofNat 32 k) = memLoad32 n6.mem (S + BitVec.ofNat 32 (0x43C + k)) :=
    fun k hk => by
      rw [memLoad32_congr (M := copyBytes n6.mem out (S + BitVec.ofNat 32 0x43C) 0x44) fun j hj => by
        rw [add_ofNat_assoc, h9 _ (sepO _ (by omega)), fr8 _ (lowOut _ (by omega))], cp_word (by omega) (by decide),
        add_ofNat_assoc]
  have back6 : ∀ d, d + 1 ≤ 0x710 → (d + 1 ≤ 0x47C ∨ 0x47D ≤ d) → (d + 1 ≤ 0x43C ∨ 0x45C ≤ d) →
      n6.mem (S + BitVec.ofNat 32 d) = n2.mem (S + BitVec.ofNat 32 d) := fun d h1 h2 h3 => by
    rw [fr6 _ (F.lowB hb1 (by decide) h1), h5 _ (sq _ _ _ (by decide) h1 (by rcases h2 with h | h; exact .inr h; exact .inl h)),
      fr4' _ (l16b _ h1) (sq _ _ _ (by decide) h1 (by rcases h3 with h | h; exact .inr h; exact .inl h))]
  have hS9 : ∀ k, k < 13 → memLoad32 M9 (S + BitVec.ofNat 32 (0x70C - 4 * k)) = v k := fun k hk => by
    rw [← hS k hk]
    exact memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      exact fin _ (F.lowB hb60 (by decide) (by omega)) (sq _ _ _ (by decide) (by omega) (.inl (by omega)))
        (oBuf (by omega))
  -- restore the saved registers and return
  have hA : aluEval .add S 0x700 = S + BitVec.ofNat 32 0x700 := rfl
  have hB : aluEval .add S 0x680 = S + BitVec.ofNat 32 0x680 := rfl
  have alB : ∀ (c : Nat) (k : Word), c + k.toNat + 4 ≤ 0x710 → (c + k.toNat) % 4 = 0 →
      (S + BitVec.ofNat 32 c + k).toNat % 4 = 0 := fun c k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  obtain ⟨n10, c10, u10⟩ := (⟨u9.pc, m9, fun _ => rfl⟩ : St M9 GD n9 0x7C8 (reg n9)).block gdI4b C9.self gdI4b_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gdI4b]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp9, hA, hB]
    exact ⟨alB 0x700 0xC (by decide) (by decide), alB 0x700 0x8 (by decide) (by decide),
      alB 0x700 0x4 (by decide) (by decide), alB 0x700 0x0 (by decide) (by decide),
      alB 0x680 0x7C (by decide) (by decide), alB 0x680 0x78 (by decide) (by decide),
      alB 0x680 0x74 (by decide) (by decide), alB 0x680 0x70 (by decide) (by decide),
      alB 0x680 0x6C (by decide) (by decide), alB 0x680 0x68 (by decide) (by decide),
      alB 0x680 0x64 (by decide) (by decide), alB 0x680 0x60 (by decide) (by decide),
      alB 0x680 0x5C (by decide) (by decide)⟩)
  have m10 : (runBlock gdI4b (M9, reg n9)).1 = M9 := rfl
  have C10 : GdCode (runBlock gdI4b (M9, reg n9)).1 := by rw [m10]; exact C9
  obtain ⟨n11, st11, pc11, mem11, regs11⟩ := u10.jalr C10.self gd_at_804
  have ra10 : (runBlock gdI4b (M9, reg n9)).2 ra = v 0 := by
    simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte]
    rw [sp9, hA, frame_lit _ (by decide)]; exact hS9 0 (by decide)
  have mem11' : n11.mem = M9 := mem11.trans m10
  refine ⟨n11, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans
    (c10.trans (.single st11)))))))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc11, ra10]; exact (congrArg (· &&& ~~~1) (BitVec.add_zero _)).trans hret
  · rw [regs11]; simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte]; rw [sp9]; rfl
  · intro k hk
    rw [regs11]
    match k, hk with
    | 0, _ =>
      simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA, frame_lit _ (by decide)]; exact hS9 0 (by decide)
    | 1, _ =>
      simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA, frame_lit _ (by decide)]; exact hS9 1 (by decide)
    | 2, _ =>
      simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA, frame_lit _ (by decide)]; exact hS9 2 (by decide)
    | 3, _ =>
      simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA, frame_lit _ (by decide)]; exact hS9 3 (by decide)
    | 4, _ =>
      simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hB, frame_lit _ (by decide)]; exact hS9 4 (by decide)
    | 5, _ =>
      simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hB, frame_lit _ (by decide)]; exact hS9 5 (by decide)
    | 6, _ =>
      simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hB, frame_lit _ (by decide)]; exact hS9 6 (by decide)
    | 7, _ =>
      simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hB, frame_lit _ (by decide)]; exact hS9 7 (by decide)
    | 8, _ =>
      simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hB, frame_lit _ (by decide)]; exact hS9 8 (by decide)
    | 9, _ =>
      simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hB, frame_lit _ (by decide)]; exact hS9 9 (by decide)
    | 10, _ =>
      simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hB, frame_lit _ (by decide)]; exact hS9 10 (by decide)
    | 11, _ =>
      simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hB, frame_lit _ (by decide)]; exact hS9 11 (by decide)
    | 12, _ =>
      simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hB, frame_lit _ (by decide)]; exact hS9 12 (by decide)
    | _ + 13, h => exact absurd h (by omega)
  · rw [mem11', ← hX]
    exact accV_congr2 8 fun i hi => by
      rw [ldB _ (by omega), ← add_ofNat_assoc S 0x43C,
        show memLoad32 n6.mem (S + BitVec.ofNat 32 0x43C + BitVec.ofNat 32 (4 * i)) =
          memLoad32 n4.mem (S + BitVec.ofNat 32 0x43C + BitVec.ofNat 32 (4 * i)) from memLoad32_congr fun j hj => by
            rw [add_ofNat_assoc, add_ofNat_assoc, fr6 _ (F.lowB hb1 (by decide) (by omega)),
              h5 _ (sq _ _ _ (by decide) (by omega) (.inr (by omega)))],
        load_frame fr4 (by rw [add_ofNat_assoc]; exact l16 _ (by omega)), cp_word (by omega) (by decide)]
      exact memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc, add_ofNat_assoc]
        exact fr2 _ (F.lowB hb60 (by decide) (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
  · rw [mem11']
    have hw : ∀ i, i < 8 → memLoad32 M9 (out + BitVec.ofNat 32 0x20 + BitVec.ofNat 32 (4 * i)) =
        memLoad32 n2.mem (S + BitVec.ofNat 32 0x45C + BitVec.ofNat 32 (4 * i)) := fun i hi => by
      rw [add_ofNat_assoc, ldB _ (by omega), add_ofNat_assoc, show 0x43C + (0x20 + 4 * i) = 0x45C + 4 * i by omega]
      exact memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact back6 _ (by omega) (.inl (by omega)) (.inr (by omega))
    rcases hpar with h | h
    · rw [ite_eq_right (by rw [h]; decide), ← hN]
      exact accV_congr2 8 fun i hi => by rw [hw i hi, w2 i hi, ite_eq_right (by rw [h]; decide)]
    · rw [ite_eq_left h, ← hY]
      exact accV_congr2 8 fun i hi => by rw [hw i hi, w2 i hi, ite_eq_left h]
  · intro k hk
    rw [mem11', byB _ (by omega)]
    rcases Nat.lt_or_ge k 1 with h | h
    · obtain rfl : k = 0 := by omega
      rw [fr6 _ (F.lowB hb1 (by decide) (by decide)), ← m5, u5.mem]
      simp +decide only [runBlock, BInstr.run, gdI2, upd, ↓reduceIte]
      rw [sp4, u4.zero]; exact memStore8_same _ _ _
    · rw [show 0x43C + (0x40 + k) = 0x47D + (k - 1) by omega, back6 _ (by omega) (.inr (by omega)) (.inr (by omega)),
        fr2 _ (F.lowB hb60 (by decide) (by omega)) (sq _ _ _ (by decide) (by omega) (.inl (by omega)))]
      exact hZ _ (by omega)
  · rw [mem11', ← hM9, memStore8_same]
    rcases hc with h | h <;> rcases hok with h' | h' <;> (rw [h, h']; decide)
  · rw [regs11]; simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte]; rw [r9, K8 3 (by decide)]
  · rw [regs11]; simp +decide only [runBlock, BInstr.run, gdI4b, upd, ↓reduceIte]; rw [r9, K8 4 (by decide)]
  · intro x hx ho
    rw [mem11']
    exact fin x (below hb60 (by decide) (by decide) hx) (inFrame (by decide) hx) ho

end C3.RV32.Gd
