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

end C3.RV32.Gd
