import C3BootProofs.Proofs.AcceptExtractDupLib

/-!
# A no-duplicates check over byte slices

Three of the checks (Fulcio subjects, log origins, TSA signer ids) compare
each entry's first two words, a pointer and a length, with `sliceEq`. From
its loop head `o`, a check runs the enumerator's `next`, leaves at
`o + 0xA` past the last entry, and otherwise sets the iterator to the
entry after the current one and compares each later entry with it. Equal
entries leave at `o + 0x72`.

`AcedpCmpN` is the compare at `o + 0x66`, which each check proves for its
list. `acedp_nCheck` runs the whole check.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

/-- The instructions of a check over byte slices, from its loop head `o`. -/
structure AcedpNI (o : Nat) (hE lE xE hT lT bo : Word) : Prop where
  c00 : fetchRel bootMainClosure0Code o = some (.aluImm .add a0 sp 0x244, 2)
  c02 : fetchRel bootMainClosure0Code (o + 2) = some (.auipc ra hE, 4)
  c06 : fetchRel bootMainClosure0Code (o + 2 + 4) = some (.jalr ra ra lE, 4)
  c0A : fetchRel bootMainClosure0Code (o + 0xA) = some (.branch .beq a1 x0 xE, 2)
  c0C : fetchRel bootMainClosure0Code (o + 0xC) = some (.aluImm .add a0 a0 0x1, 2)
  c0E : fetchRel bootMainClosure0Code (o + 0xE) = some (.alu .sltu a2 x0 a0, 4)
  c12 : fetchRel bootMainClosure0Code (o + 0x12) = some (.load .lw (19 : Fin 32) a1 0x0, 4)
  c16 : fetchRel bootMainClosure0Code (o + 0x16) = some (.load .lw (22 : Fin 32) a1 0x4, 4)
  c1A : fetchRel bootMainClosure0Code (o + 0x1A) = some (.aluImm .add a2 a2 0xFFFFFFFF, 2)
  c1C : fetchRel bootMainClosure0Code (o + 0x1C) = some (.alu .or a0 a0 a2, 2)
  b00 : fetchRel bootMainClosure0Code (o + 0x1E) = some (.lui a1 0x1000, 2)
  b02 : fetchRel bootMainClosure0Code (o + 0x1E + 2) = some (.aluImm .add a1 a1 0x310, 4)
  b06 : fetchRel bootMainClosure0Code (o + 0x1E + 6) = some (.alu .add a1 a1 sp, 2)
  b08 : fetchRel bootMainClosure0Code (o + 0x1E + 8) = some (.store .sw a1 (18 : Fin 32) 0x10, 4)
  b0C : fetchRel bootMainClosure0Code (o + 0x1E + 0xC) = some (.store .sw a1 (20 : Fin 32) 0x14, 4)
  b10 : fetchRel bootMainClosure0Code (o + 0x1E + 0x10) = some (.store .sw a1 x0 0x18, 4)
  b14 : fetchRel bootMainClosure0Code (o + 0x1E + 0x14) = some (.aluImm .add a1 a0 0xFFFFFFFF, 4)
  b18 : fetchRel bootMainClosure0Code (o + 0x1E + 0x18) = some (.lui a0 0x1000, 2)
  b1A : fetchRel bootMainClosure0Code (o + 0x1E + 0x1A) = some (.aluImm .add a0 a0 0x320, 4)
  b1E : fetchRel bootMainClosure0Code (o + 0x1E + 0x1E) = some (.alu .add a0 a0 sp, 2)
  b20 : fetchRel bootMainClosure0Code (o + 0x1E + 0x20) = some (.auipc ra hT, 4)
  b24 : fetchRel bootMainClosure0Code (o + 0x1E + 0x20 + 4) = some (.jalr ra ra lT, 4)
  b28 : fetchRel bootMainClosure0Code (o + 0x1E + 0x28) = some (.branch .beq a0 x0 bo, 2)
  b2A : fetchRel bootMainClosure0Code (o + 0x1E + 0x2A) = some (.lui a0 0x1000, 2)
  b2C : fetchRel bootMainClosure0Code (o + 0x1E + 0x2C) = some (.aluImm .add a0 a0 0x310, 4)
  b30 : fetchRel bootMainClosure0Code (o + 0x1E + 0x30) = some (.alu .add a0 a0 sp, 2)
  c50 : fetchRel bootMainClosure0Code (o + 0x50) = some (.load .lw a2 a0 0x10, 2)
  c52 : fetchRel bootMainClosure0Code (o + 0x52) = some (.load .lw (8 : Fin 32) a0 0x14, 2)
  c54 : fetchRel bootMainClosure0Code (o + 0x54) = some (.branch .beq a2 (8 : Fin 32) 0xFFFFFFAC, 4)
  c58 : fetchRel bootMainClosure0Code (o + 0x58) = some (.load .lw a0 a2 0x0, 2)
  c5A : fetchRel bootMainClosure0Code (o + 0x5A) = some (.branch .beq a0 x0 0xFFFFFFA6, 2)
  c5C : fetchRel bootMainClosure0Code (o + 0x5C) = some (.load .lw a1 a2 0x4, 2)
  c5E : fetchRel bootMainClosure0Code (o + 0x5E) = some (.aluImm .add (9 : Fin 32) a2 0x20, 4)
  c62 : fetchRel bootMainClosure0Code (o + 0x62) = some (.alu .add a2 x0 (19 : Fin 32), 2)
  c64 : fetchRel bootMainClosure0Code (o + 0x64) = some (.alu .add a3 x0 (22 : Fin 32), 2)
  c6E : fetchRel bootMainClosure0Code (o + 0x6E) = some (.alu .add a2 x0 (9 : Fin 32), 2)
  c70 : fetchRel bootMainClosure0Code (o + 0x70) = some (.branch .beq a0 x0 0xFFFFFFE4, 2)

/-- The compare at `o + 0x66` of entry `j`'s slice (`a0`, `a1`) with entry
`i`'s (`a2`, `a3`): `a0` is 1 when the list's entries `j` and `i` are equal. -/
def AcedpCmpN (X : AceCtx) (N : Word → BitVec 8) (Q : Post) (o a len : Nat) (xs : List Bytes) : Prop :=
  ∀ (M : Word → BitVec 8) (f : Fin 32 → Word) (i j : Nat), i < len → j < len → AcedpM X N M → AcedpR X f →
    f a0 = memLoad32 N (acedpE X.B a j) → f a1 = memLoad32 N (acedpE X.B a j + BitVec.ofNat 32 4) →
    f a2 = memLoad32 N (acedpE X.B a i) → f a3 = memLoad32 N (acedpE X.B a i + BitVec.ofNat 32 4) →
    (∀ (M2 : Word → BitVec 8) (g : Fin 32 → Word), Out M M2 (X.B + BitVec.ofNat 32 0x3A40) 16 →
      (∀ x, x ∉ jClob → x ≠ ra → g x = f x) → g a0 = (if xs[j]? = xs[i]? then 1 else 0) →
      WP bootMainClosure0Code AC Q M2 (o + 0x6E) g) →
    WP bootMainClosure0Code AC Q M (o + 0x66) f

section
variable {X : AceCtx} {N : Word → BitVec 8} {fp : Word} {Q : Post} {o a cap len T : Nat} {xs : List Bytes}
  {hE lE xE hT lT bo : Word}

/-- One step of the inner loop, at `o + 0x54` with the iterator's entry `j`. -/
theorem acedp_nIn1 (S : AcedpS X N fp) (A : AcedpArr X N a cap len) (I : AcedpNI o hE lE xE hT lT bo)
    (ho : o + 0x80 < 2 ^ 32) (cmp : AcedpCmpN X N Q o a len xs)
    {i j : Nat} (hi : i < len) (_hij : i < j) (hj : j ≤ len) (hk : ∀ k, i < k → k < j → xs[k]? ≠ xs[i]?)
    (kd : ∀ M f, AcedpM X N M → AcedpR X f → WP bootMainClosure0Code AC Q M (o + 0x72) f)
    (kout : ∀ M f, AcedpOut X N M f a cap (i + 1) → (∀ k, i < k → k < len → xs[k]? ≠ xs[i]?) →
      WP bootMainClosure0Code AC Q M o f)
    (knext : j < len → ∀ M f, AcedpOut X N M f a cap (i + 1) → f a2 = acedpE X.B a (j + 1) →
      f 8 = acedpE X.B a cap → f 19 = memLoad32 N (acedpE X.B a i) →
      f 22 = memLoad32 N (acedpE X.B a i + BitVec.ofNat 32 4) → (∀ k, i < k → k < j + 1 → xs[k]? ≠ xs[i]?) →
      WP bootMainClosure0Code AC Q M (o + 0x54) f)
    {M : Word → BitVec 8} {f : Fin 32 → Word} (H : AcedpOut X N M f a cap (i + 1))
    (h2 : f a2 = acedpE X.B a j) (h8 : f 8 = acedpE X.B a cap) (h19 : f 19 = memLoad32 N (acedpE X.B a i))
    (h22 : f 22 = memLoad32 N (acedpE X.B a i + BitVec.ofNat 32 4)) :
    WP bootMainClosure0Code AC Q M (o + 0x54) f := by
  have F := S.ok.lay.fr
  have R := H.regs
  have hz := R.rz
  have hcap : a + 0x20 * cap ≤ 0x2020 := A.hi (Nat.le_refl _)
  have hlc := A.hlen
  refine WP.branch I.c54 (fun ht => ?_) fun hf => ?_
  · rw [h2, h8] at ht
    have e := acedp_beq ht
    have hjc : j = cap := by
      refine Decidable.byContradiction fun hne => ?_
      exact acedpE_ne (A.hi (by omega)) hcap hne e
    exact acedp_wpOff (by simp only [BitVec.reduceToNat]; omega) (kout M f H fun k h1 h3 => hk k h1 (by omega))
  rw [h2, h8] at hf
  have hjc : j < cap := by
    have := acedp_bne hf
    refine Decidable.byContradiction fun hc => ?_
    exact this (by rw [show j = cap by omega])
  acedp_wo
  refine acedp_lw I.c58 (a := acedpE X.B a j) (by rw [h2]; exact BitVec.add_zero _)
    (acedpE_al F A.al (A.hi (by omega))) ?_
  acedp_wo
  rw [acedp_ldE0 S H.mem A hjc]
  refine WP.branch I.c5A (fun ht => ?_) fun hf => ?_
  · rsimp at ht
    have e := acedp_beqT ht
    have hjl : j = len := by
      refine Decidable.byContradiction fun hne => ?_
      exact A.tag j (by omega) e
    exact acedp_wpOff (by simp only [BitVec.reduceToNat]; omega)
      (kout M _ (H.mv F acedp_outId (by acedp_hr) (by rsimp) (by rsimp)) fun k h1 h3 => hk k h1 (by omega))
  rsimp at hf
  have hjl : j < len := by
    refine Decidable.byContradiction fun hne => ?_
    exact acedp_beqF hf (A.zero j (by omega) hjc)
  acedp_wo
  refine acedp_lw I.c5C (a := acedpE X.B a j + BitVec.ofNat 32 4) (by rsimp; rw [h2]; rfl)
    (by
      rw [acedpE_add]
      have := A.al
      have := A.hi (i := j) (by omega)
      exact ace_al4 F (c := 0x3A50 + (a + 0x20 * j + 4)) (by omega) (by omega)) ?_
  acedp_wo
  rw [acedp_ldE S H.mem A hjc (k := 4) (by decide)]
  refine WP.aluImm I.c5E ?_; acedp_wo
  refine WP.alu I.c62 ?_; acedp_wo
  refine WP.alu I.c64 ?_; acedp_wo
  refine cmp _ _ i j hi hjl H.mem (by acedp_hr) (by rsimp) (by rsimp) (by rsimp; rw [ev_add, acedp_zadd, h19])
    (by rsimp; rw [ev_add, acedp_zadd, h22]) fun M2 g hO hK ha0 => ?_
  have R2 : AcedpR X g := AcedpR.keep (by acedp_hr) hK
  have hz2 := R2.rz
  refine WP.alu I.c6E ?_
  refine WP.branch I.c70 (fun ht => ?_) fun _ => ?_
  · rsimp at ht
    have e := acedp_beqT ht
    have hne : xs[j]? ≠ xs[i]? := fun e' => by rw [ha0, if_pos e'] at e; exact absurd e (by decide)
    refine acedp_wpOff (by simp only [BitVec.reduceToNat]; omega) (knext hjl M2 _ ?_ ?_ ?_ ?_ ?_ ?_)
    · refine H.mv F hO (by acedp_hr) ?_ ?_
      · rsimp; rw [hK 18 (by decide) (by decide)]; rsimp
      · rsimp; rw [hK 20 (by decide) (by decide)]; rsimp
    · rsimp; rw [hz2, hK 9 (by decide) (by decide)]; rsimp
      rw [ev_add, ev_add, acedp_zadd, h2, acedpE_succ]
    · rsimp; rw [hK 8 (by decide) (by decide)]; rsimp; exact h8
    · rsimp; rw [hK 19 (by decide) (by decide)]; rsimp; exact h19
    · rsimp; rw [hK 22 (by decide) (by decide)]; rsimp; exact h22
    · intro k h1 h3
      by_cases e2 : k = j
      · rw [e2]; exact hne
      · exact hk k h1 (by omega)
  acedp_wo
  exact kd M2 _ (fun x hx => (hO x (AcedpW.frame F hx)).trans (H.mem x hx)) (by acedp_hr)

theorem acedp_nInner (S : AcedpS X N fp) (A : AcedpArr X N a cap len) (I : AcedpNI o hE lE xE hT lT bo)
    (ho : o + 0x80 < 2 ^ 32) (cmp : AcedpCmpN X N Q o a len xs) {i : Nat} (hi : i < len)
    (kd : ∀ M f, AcedpM X N M → AcedpR X f → WP bootMainClosure0Code AC Q M (o + 0x72) f)
    (kout : ∀ M f, AcedpOut X N M f a cap (i + 1) → (∀ k, i < k → k < len → xs[k]? ≠ xs[i]?) →
      WP bootMainClosure0Code AC Q M o f) :
    ∀ d j, j + d = len → i < j → (∀ k, i < k → k < j → xs[k]? ≠ xs[i]?) →
      ∀ M f, AcedpOut X N M f a cap (i + 1) → f a2 = acedpE X.B a j → f 8 = acedpE X.B a cap →
        f 19 = memLoad32 N (acedpE X.B a i) → f 22 = memLoad32 N (acedpE X.B a i + BitVec.ofNat 32 4) →
        WP bootMainClosure0Code AC Q M (o + 0x54) f := by
  intro d
  induction d with
  | zero =>
    intro j hd hij hk M f H h2 h8 h19 h22
    exact acedp_nIn1 S A I ho cmp hi hij (by omega) hk kd kout (fun hj => absurd hj (by omega)) H h2 h8 h19 h22
  | succ d ih =>
    intro j hd hij hk M f H h2 h8 h19 h22
    exact acedp_nIn1 S A I ho cmp hi hij (by omega) hk kd kout
      (fun _ M f H h2 h8 h19 h22 hk' => ih (j + 1) (by omega) (by omega) hk' M f H h2 h8 h19 h22) H h2 h8 h19 h22

/-- One step of the outer loop, at `o` with the enumerator's entry `i`. -/
theorem acedp_nStep (S : AcedpS X N fp) (A : AcedpArr X N a cap len) (I : AcedpNI o hE lE xE hT lT bo)
    (ho : o + 0x80 < 2 ^ 32) (hev : o % 2 = 0)
    (tE : AC + BitVec.ofNat 32 (o + 2) + hE + lE = BitVec.ofNat 32 fulcioEnumNextAddress)
    (tT : AC + BitVec.ofNat 32 (o + 0x1E + 0x20) + hT + lT = BitVec.ofNat 32 fulcioIterNthAddress)
    (tX : (o + 0xA + xE.toNat) % 2 ^ 32 = T) (cmp : AcedpCmpN X N Q o a len xs)
    {i : Nat} (hi : i ≤ len) (hP : AcedpProg xs len i)
    (kx : ∀ M f, AcedpM X N M → AcedpR X f → f 20 = acedpE X.B a cap → AcedpProg xs len len →
      WP bootMainClosure0Code AC Q M T f)
    (kd : ∀ M f, AcedpM X N M → AcedpR X f → WP bootMainClosure0Code AC Q M (o + 0x72) f)
    (kout : i < len → ∀ M f, AcedpOut X N M f a cap (i + 1) → AcedpProg xs len (i + 1) →
      WP bootMainClosure0Code AC Q M o f)
    {M : Word → BitVec 8} {f : Fin 32 → Word} (H : AcedpOut X N M f a cap i) :
    WP bootMainClosure0Code AC Q M o f := by
  have F := S.ok.lay.fr
  have hlc := A.hlen
  have hc16 := A.hcap
  refine acedp_enumStep S A I.c00 I.c02 I.c06 tE hev hi H fun M2 g hW hK ha1 hgo => ?_
  have R := H.regs.keep hK
  have hz := R.rz
  refine WP.branch I.c0A (fun ht => ?_) fun hf => ?_
  · rw [hz] at ht
    have e := acedp_beqT ht
    rw [ha1] at e
    have hil : ¬ i < len := fun hl => by rw [if_pos hl] at e; exact acedpE_nz F (A.hi (by omega)) e
    obtain rfl : i = len := by omega
    rw [tX]
    exact kx M2 g hW R (by rw [hK 20 (by decide) (by decide)]; exact H.s4) hP
  rw [hz] at hf
  have hl : i < len := by
    refine Decidable.byContradiction fun hl => ?_
    have := acedp_beqF hf
    rw [ha1, if_neg hl] at this
    exact this rfl
  obtain ⟨ga0, e0, e4, e8⟩ := hgo hl
  acedp_wo
  refine WP.aluImm I.c0C ?_; acedp_wo
  refine WP.alu I.c0E ?_; acedp_wo
  refine acedp_lw I.c12 (a := acedpE X.B a i) (by rsimp; rw [ha1, if_pos hl]; exact BitVec.add_zero _)
    (acedpE_al F A.al (A.hi (by omega))) ?_
  acedp_wo
  rw [acedp_ldE0 S hW A (by omega)]
  refine acedp_lw I.c16 (a := acedpE X.B a i + BitVec.ofNat 32 4) (by rsimp; rw [ha1, if_pos hl]; rfl)
    (by
      rw [acedpE_add]
      have := A.al
      have := A.hi4 (i := i) (by omega)
      exact ace_al4 F (c := 0x3A50 + (a + 0x20 * i + 4)) (by omega) (by omega)) ?_
  acedp_wo
  rw [acedp_ldE S hW A (by omega) (k := 4) (by decide)]
  refine WP.aluImm I.c1A ?_; acedp_wo
  refine WP.alu I.c1C ?_; acedp_wo
  refine acedp_nthBlock S A I.b00 I.b02 I.b06 I.b08 I.b0C I.b10 I.b14 I.b18 I.b1A I.b1E I.b20 I.b24 I.b28
    I.b2A I.b2C I.b30 tT (by omega) hl hW (by acedp_hr)
    (by rsimp; rw [hK 18 (by decide) (by decide)]; exact H.s2)
    (by rsimp; rw [hK 20 (by decide) (by decide)]; exact H.s4)
    (by rsimp; rw [ga0]; exact acedp_cnt i (by omega)) fun M3 g3 hO3 hW3 hK3 hI0 hI4 l0 l4 => ?_
  have R3 : AcedpR X g3 := AcedpR.keep (by acedp_hr) hK3
  acedp_wo
  refine acedp_lw I.c50 (a := acSlot X.B 0x1320) hI0 (ace_al4 F (c := 0x4D70) (by decide) (by decide)) ?_
  acedp_wo
  refine acedp_lw I.c52 (a := acSlot X.B 0x1324) (by rsimp; exact hI4)
    (ace_al4 F (c := 0x4D74) (by decide) (by decide)) ?_
  acedp_wo
  rw [l0, l4]
  have sE0 : Sep (acSlot X.B 0x1320) 12 (acSlot X.B 0x244) 4 := acedp_sepS F (.inr (by decide)) (by decide) (by decide)
  have sE4 : Sep (acSlot X.B 0x1320) 12 (acSlot X.B 0x248) 4 := acedp_sepS F (.inr (by decide)) (by decide) (by decide)
  have sE8 : Sep (acSlot X.B 0x1320) 12 (acSlot X.B 0x24C) 4 := acedp_sepS F (.inr (by decide)) (by decide) (by decide)
  refine acedp_nInner S A I ho cmp hl kd (fun M f H hk => kout hl M f H (acedp_prog_succ hP hk))
    (len - (i + 1)) (i + 1) (by omega) (by omega) (fun k h1 h2 => absurd h2 (by omega)) M3 _
    ⟨hW3, by acedp_hr, ?_, ?_, (hO3.load32 sE0).trans e0, (hO3.load32 sE4).trans e4, (hO3.load32 sE8).trans e8⟩
    (by rsimp) (by rsimp) ?_ ?_
  · rsimp; rw [hK3 18 (by decide) (by decide)]; rsimp; rw [hK 18 (by decide) (by decide)]; exact H.s2
  · rsimp; rw [hK3 20 (by decide) (by decide)]; rsimp; rw [hK 20 (by decide) (by decide)]; exact H.s4
  · rsimp; rw [hK3 19 (by decide) (by decide)]; rsimp
  · rsimp; rw [hK3 22 (by decide) (by decide)]; rsimp

theorem acedp_nLoop (S : AcedpS X N fp) (A : AcedpArr X N a cap len) (I : AcedpNI o hE lE xE hT lT bo)
    (ho : o + 0x80 < 2 ^ 32) (hev : o % 2 = 0)
    (tE : AC + BitVec.ofNat 32 (o + 2) + hE + lE = BitVec.ofNat 32 fulcioEnumNextAddress)
    (tT : AC + BitVec.ofNat 32 (o + 0x1E + 0x20) + hT + lT = BitVec.ofNat 32 fulcioIterNthAddress)
    (tX : (o + 0xA + xE.toNat) % 2 ^ 32 = T) (cmp : AcedpCmpN X N Q o a len xs)
    (kx : ∀ M f, AcedpM X N M → AcedpR X f → f 20 = acedpE X.B a cap → AcedpProg xs len len →
      WP bootMainClosure0Code AC Q M T f)
    (kd : ∀ M f, AcedpM X N M → AcedpR X f → WP bootMainClosure0Code AC Q M (o + 0x72) f) :
    ∀ d i, i + d = len → AcedpProg xs len i → ∀ M f, AcedpOut X N M f a cap i →
      WP bootMainClosure0Code AC Q M o f := by
  intro d
  induction d with
  | zero =>
    intro i hd hP M f H
    exact acedp_nStep S A I ho hev tE tT tX cmp (by omega) hP kx kd (fun hl => absurd hl (by omega)) H
  | succ d ih =>
    intro i hd hP M f H
    exact acedp_nStep S A I ho hev tE tT tX cmp (by omega) hP kx kd
      (fun _ M f H hP' => ih (i + 1) (by omega) hP' M f H) H

/-- A whole check over byte slices: past the last entry it leaves for `T`
with the list `distinct`. -/
theorem acedp_nCheck (S : AcedpS X N fp) (A : AcedpArr X N a cap len) (I : AcedpNI o hE lE xE hT lT bo)
    (ho : o + 0x80 < 2 ^ 32) (hev : o % 2 = 0)
    (tE : AC + BitVec.ofNat 32 (o + 2) + hE + lE = BitVec.ofNat 32 fulcioEnumNextAddress)
    (tT : AC + BitVec.ofNat 32 (o + 0x1E + 0x20) + hT + lT = BitVec.ofNat 32 fulcioIterNthAddress)
    (tX : (o + 0xA + xE.toNat) % 2 ^ 32 = T) (cmp : AcedpCmpN X N Q o a len xs) (hl : xs.length = len)
    (kx : ∀ M f, AcedpM X N M → AcedpR X f → f 20 = acedpE X.B a cap → distinct xs = true →
      WP bootMainClosure0Code AC Q M T f)
    (kd : ∀ M f, AcedpM X N M → AcedpR X f → WP bootMainClosure0Code AC Q M (o + 0x72) f)
    {M : Word → BitVec 8} {f : Fin 32 → Word} (H : AcedpOut X N M f a cap 0) :
    WP bootMainClosure0Code AC Q M o f :=
  acedp_nLoop S A I ho hev tE tT tX cmp (fun M f hM R h20 hP => kx M f hM R h20 (acedp_prog_distinct hl hP)) kd
    len 0 (by omega) (fun _ _ h => absurd h (Nat.not_lt_zero _)) M f H

end

end C3.RV32.Ac
