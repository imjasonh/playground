import C3BootProofs.Proofs.TufRoleKeysLoop

/-!
# `tufRoleKeysRead`: the head and the contract

`RoleKeys::read` from its entry to the `keyids` loop at 0x1E6: the
prologue, the `roles`, role, and `threshold` lookups, the threshold, the
`keys` object, the empty `RoleKeys` it builds at `F + 0x18`, and the
`keyids` array. `tufRoleKeysRead_correct` is the function's contract.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

/-- The registers the head changes, besides the saved ones it sets for
the loop. -/
abbrev rkhL : List (Fin 32) := jClob ++ [ra, 8, 9, 19, 20]

/-- The registers the two loops at 0x104 and 0x126 change. -/
abbrev rkhM : List (Fin 32) := jClob ++ [ra, 8, 9]

theorem rkh_ld0 {M : Word → BitVec 8} {a : Word} (h : ∀ j < 4, M (a + BitVec.ofNat 32 j) = 0) :
    memLoad32 M a = 0 := by
  rw [memLoad32_congr (M := fun _ => 0) h]
  unfold memLoad32
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append]
  rfl

theorem rkh_sub : ∀ x, x ∉ rkhL → x ∉ rkhM := by decide

theorem rkh_dec {j : Nat} (h : j < 2 ^ 32 - 1) :
    aluEval .add (BitVec.ofNat 32 (j + 1)) 0xFFFFFFFF = BitVec.ofNat 32 j := by
  rw [ev_add]; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl, Nat.mod_eq_of_lt (show j + 1 < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show j < 2 ^ 32 by omega)]
  omega

theorem rkh_fill {M : Word → BitVec 8} {dst : Word} {v : BitVec 8} {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) :
    fillBytes M dst v N (dst + BitVec.ofNat 32 i) = v := by
  unfold fillBytes
  rw [BitVec.add_comm dst, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ite_eq_left hi]

section
variable {M0 M1 : Word → BitVec 8} {s out F P : Word} {N : Nat} {g0 gS : Fin 32 → Word} {Q : Post}

/-- The loop at 0x104 that zeroes eight 64-byte key IDs at `F + 0x55C`,
with `j` passes left. -/
theorem rkh_ms (E : RkEnv M0 M1 s out F P N g0) {Ms : Word → BitVec 8} (hzS : gS 0 = 0)
    (K : ∀ M' g', g' sp = F → g' 0 = 0 → (∀ x, x ∉ rkhM → g' x = gS x) → Out M1 M' s 3004 →
      Out Ms M' (F + BitVec.ofNat 32 0x55C) 0x200 → (∀ i < 0x200, M' (F + BitVec.ofNat 32 (0x55C + i)) = 0) →
      WP tufRoleKeysReadCode TRK Q M' 0x11C g') :
    ∀ j, 0 < j → j ≤ 8 → ∀ M g, g 8 = F + BitVec.ofNat 32 (0x55C + 64 * (8 - j)) → g 9 = BitVec.ofNat 32 j →
      g sp = F → g 0 = 0 → (∀ x, x ∉ rkhM → g x = gS x) → Out M1 M s 3004 →
      Out Ms M (F + BitVec.ofNat 32 0x55C) 0x200 → (∀ i < 64 * (8 - j), M (F + BitVec.ofNat 32 (0x55C + i)) = 0) →
      WP tufRoleKeysReadCode TRK Q M 0x104 g := by
  intro j
  induction j with
  | zero => intro h; exact absurd h (by decide)
  | succ j ih =>
    intro _ hj M g h8 h9 hsp hz hfr hO hOs hZ
    have hc := E.code hO
    refine WP.aluImm rkr_at_104 ?_; wn
    refine WP.alu rkr_at_108 ?_; wn
    refine WP.aluImm rkr_at_10a ?_; wn
    refine WP.callMemsetT (tb := TPS_MS) (dst := F + BitVec.ofNat 32 (0x55C + 64 * (8 - (j + 1)))) (b := 0)
      (n := 64) rkr_at_10c rkr_at_110 (by decide) (by decide) (by decide) hc.tps.ms
      (by rsimp; rw [ev0]; exact h8) (by rsimp; try rfl) (by rsimp; rw [hz]; rfl)
      (Nat.lt_of_le_of_lt (E.wF (c := 0x55C + 64 * (8 - (j + 1))) (k := 64) (by omega)) (by decide))
      (E.lowF (by omega) (by decide) (by decide)) (E.cF (by omega)) fun m2 hm => ?_
    wn
    have hO2 : Out M m2.mem (F + BitVec.ofNat 32 (0x55C + 64 * (8 - (j + 1)))) 64 := by
      rw [hm]; exact fun x hx => fillBytes_sep hx.symm (Nat.le_refl _)
    have hO2s : Out M1 m2.mem s 3004 := hO.trans fun x hx => hO2 x
      (by have := hx.subR (c := 304 + (0x55C + 64 * (8 - (j + 1)))) (l := 64) (by omega)
          rwa [← E.Fc] at this)
    have hO2c : Out Ms m2.mem (F + BitVec.ofNat 32 0x55C) 0x200 := hOs.trans fun x hx => hO2 x
      (by have := hx.subR (c := 64 * (8 - (j + 1))) (l := 64) (by omega)
          rwa [add_ofNat_assoc] at this)
    have hZ2 : ∀ i < 64 * (8 - j), m2.mem (F + BitVec.ofNat 32 (0x55C + i)) = 0 := by
      intro i hi
      by_cases hi' : i < 64 * (8 - (j + 1))
      · rw [hO2 _ (rk_ff F (c := 0x55C + i) (n := 1) (d := 0x55C + 64 * (8 - (j + 1))) (k := 64)
          (Or.inl (by omega)) (by omega) (by omega))]
        exact hZ i hi'
      · rw [hm, show F + BitVec.ofNat 32 (0x55C + i) = F + BitVec.ofNat 32 (0x55C + 64 * (8 - (j + 1))) +
            BitVec.ofNat 32 (i - 64 * (8 - (j + 1))) by
          rw [add_ofNat_assoc, show 0x55C + 64 * (8 - (j + 1)) + (i - 64 * (8 - (j + 1))) = 0x55C + i by omega],
          rkh_fill (by omega) (by decide)]
        decide
    refine WP.aluImm rkr_at_114 ?_; wn
    refine WP.aluImm rkr_at_118 ?_; wn
    have e8 : aluEval .add (F + BitVec.ofNat 32 (0x55C + 64 * (8 - (j + 1)))) 0x40 =
        F + BitVec.ofNat 32 (0x55C + 64 * (8 - j)) := by
      rw [ev_add]; exact rk_inc (d := 64) (by omega)
    have e9 : aluEval .add (BitVec.ofNat 32 (j + 1)) 0xFFFFFFFF = BitVec.ofNat 32 j := rkh_dec (by omega)
    refine WP.branch rkr_at_11a (fun eb => ?_) (fun eb => ?_) <;> wn
    · rsimp at eb
      rw [h9, e9, br_bne0 (by omega)] at eb
      have hj0 := not_dec_true eb
      exact ih (by omega) (by omega) _ _ (by rsimp; rw [h8, e8]) (by rsimp; rw [h9, e9]) (by rsimp; exact hsp)
        (by rsimp) (by keepz hzS) hO2s hO2c hZ2
    · rsimp at eb
      rw [h9, e9, br_bne0 (by omega)] at eb
      have hj0 : j = 0 := by have := not_dec_false eb; omega
      subst hj0
      exact K _ _ (by rsimp; exact hsp) (by rsimp) (by keepz hzS) hO2s hO2c hZ2

/-- The loop at 0x126 that writes the tag 0xFF of eight empty keys at
`F + 0x75C`, with `j` passes left. -/
theorem rkh_tags (E : RkEnv M0 M1 s out F P N g0) {Ms : Word → BitVec 8} (hzS : gS 0 = 0)
    (K : ∀ M' g', g' sp = F → g' 0 = 0 → (∀ x, x ∉ rkhM → g' x = gS x) → Out M1 M' s 3004 →
      Out Ms M' (F + BitVec.ofNat 32 0x75C) 0x310 → (∀ i < 8, M' (F + BitVec.ofNat 32 (0x75C + 98 * i)) = 0xFF) →
      WP tufRoleKeysReadCode TRK Q M' 0x132 g') :
    ∀ j, 0 < j → j ≤ 8 → ∀ M g, g a0 = F + BitVec.ofNat 32 (0x75C + 98 * (8 - j)) → g a1 = BitVec.ofNat 32 j →
      g a2 = 0xFFFFFFFF → g sp = F → g 0 = 0 → (∀ x, x ∉ rkhM → g x = gS x) → Out M1 M s 3004 →
      Out Ms M (F + BitVec.ofNat 32 0x75C) 0x310 → (∀ i < 8 - j, M (F + BitVec.ofNat 32 (0x75C + 98 * i)) = 0xFF) →
      WP tufRoleKeysReadCode TRK Q M 0x126 g := by
  intro j
  induction j with
  | zero => intro h; exact absurd h (by decide)
  | succ j ih =>
    intro _ hj M g h10 h11 h12 hsp hz hfr hO hOs hT
    refine WP.sb rkr_at_126 (by rw [h10, add_lit_zero]; exact E.cF (by omega)) ?_; wn
    rw [h10, add_lit_zero, h12, show (0xFFFFFFFF : Word).extractLsb' 0 8 = 0xFF by decide]
    have hO2 : Out M (memStore8 M (F + BitVec.ofNat 32 (0x75C + 98 * (8 - (j + 1)))) 0xFF)
        (F + BitVec.ofNat 32 (0x75C + 98 * (8 - (j + 1)))) 1 := out_store8 _ _ _
    have hO2s : Out M1 (memStore8 M (F + BitVec.ofNat 32 (0x75C + 98 * (8 - (j + 1)))) 0xFF) s 3004 :=
      hO.trans fun x hx => hO2 x
        (by have := hx.subR (c := 304 + (0x75C + 98 * (8 - (j + 1)))) (l := 1) (by omega)
            rwa [← E.Fc] at this)
    have hO2c : Out Ms (memStore8 M (F + BitVec.ofNat 32 (0x75C + 98 * (8 - (j + 1)))) 0xFF)
        (F + BitVec.ofNat 32 0x75C) 0x310 := hOs.trans fun x hx => hO2 x
      (by have := hx.subR (c := 98 * (8 - (j + 1))) (l := 1) (by omega)
          rwa [add_ofNat_assoc] at this)
    have hT2 : ∀ i < 8 - j,
        memStore8 M (F + BitVec.ofNat 32 (0x75C + 98 * (8 - (j + 1)))) 0xFF (F + BitVec.ofNat 32 (0x75C + 98 * i)) =
          0xFF := by
      intro i hi
      by_cases hi' : i < 8 - (j + 1)
      · rw [hO2 _ (rk_ff F (c := 0x75C + 98 * i) (n := 1) (d := 0x75C + 98 * (8 - (j + 1))) (k := 1)
          (Or.inl (by omega)) (by omega) (by omega))]
        exact hT i hi'
      · rw [show i = 8 - (j + 1) by omega]; exact memStore8_same _ _ _
    refine WP.aluImm rkr_at_12a ?_; wn
    refine WP.aluImm rkr_at_12e ?_; wn
    have e10 : aluEval .add (F + BitVec.ofNat 32 (0x75C + 98 * (8 - (j + 1)))) 0x62 =
        F + BitVec.ofNat 32 (0x75C + 98 * (8 - j)) := by
      rw [ev_add]; exact rk_inc (d := 98) (by omega)
    have e11 : aluEval .add (BitVec.ofNat 32 (j + 1)) 0xFFFFFFFF = BitVec.ofNat 32 j := rkh_dec (by omega)
    refine WP.branch rkr_at_130 (fun eb => ?_) (fun eb => ?_) <;> wn
    · rsimp at eb
      rw [h11, e11, br_bne0 (by omega)] at eb
      have hj0 := not_dec_true eb
      exact ih (by omega) (by omega) _ _ (by rsimp; rw [h10, e10]) (by rsimp; rw [h11, e11]) (by rsimp; exact h12)
        (by rsimp; exact hsp) (by rsimp) (by keepz hzS) hO2s hO2c hT2
    · rsimp at eb
      rw [h11, e11, br_bne0 (by omega)] at eb
      have hj0 : j = 0 := by have := not_dec_false eb; omega
      subst hj0
      exact K _ _ (by rsimp; exact hsp) (by rsimp) (by keepz hzS) hO2s hO2c hT2

/-- The empty `RoleKeys` after the loops at 0x104 and 0x126: the threshold
from `s8` and `s4`, the count, the zeroed key IDs and lengths, and the
tags, copied to `F + 0x18`. -/
theorem rkh_init (E : RkEnv M0 M1 s out F P N g0) {M : Word → BitVec 8} {g : Fin 32 → Word} {lo hi : Word}
    (hzS : gS 0 = 0) (hsp : g sp = F) (hz : g 0 = 0) (h24 : g 24 = lo) (h20 : g 20 = hi)
    (hfr : ∀ x, x ∉ rkhL → g x = gS x) (hO : Out M1 M s 3004)
    (K : ∀ M' g', g' sp = F → g' 0 = 0 → g' 19 = F + BitVec.ofNat 32 0x330 → g' 20 = F + BitVec.ofNat 32 0x530 →
      (∀ x, x ∉ rkhL → g' x = gS x) → Out M1 M' s 3004 →
      RkAt M' (F + 0x18) (hi.toNat * 2 ^ 32 + lo.toNat) [] → WP tufRoleKeysReadCode TRK Q M' 0x17A g') :
    WP tufRoleKeysReadCode TRK Q M 0xFC g := by
  refine WP.aluImm rkr_at_fc ?_; wn
  refine WP.aluImm rkr_at_100 ?_; wn
  refine WP.branch rkr_at_102 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb <;> exact absurd eb (by decide)
  refine rkh_ms E (gS := upd (upd g 8 (aluEval .add (g sp) 0x55C)) 9 (aluEval .add 0 8)) (Ms := M)
    (by rsimp) (fun Ma ga hspa hza hfra hOa hOsa hZa => ?_) 8 (by decide) (Nat.le_refl _) M _
    (by rsimp; rw [hsp, ev_add]; try rfl) (by rsimp; try rfl) (by rsimp; exact hsp) (by rsimp) (fun _ _ => rfl)
    hO (fun _ _ => rfl) (fun i hi => by omega)
  have ha24 : ga 24 = lo := by rw [hfra 24 (by decide)]; rsimp; exact h24
  have ha20 : ga 20 = hi := by rw [hfra 20 (by decide)]; rsimp; exact h20
  have hfra' : ∀ x, x ∉ rkhL → ga x = gS x := fun x hx => by
    have h8 : x ≠ 8 := fun e => hx (by rw [e]; decide)
    have h9 : x ≠ 9 := fun e => hx (by rw [e]; decide)
    rw [hfra x (rkh_sub x hx), upd_ne' h9 (by rsimp), upd_ne' h8 hz]; exact hfr x hx
  refine WP.aluImm rkr_at_11c ?_; wn
  refine WP.aluImm rkr_at_120 ?_; wn
  refine WP.aluImm rkr_at_122 ?_; wn
  refine WP.branch rkr_at_124 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb <;> exact absurd eb (by decide)
  refine rkh_tags E (gS := ga) (Ms := Ma) hza (fun Mt gt hspt hzt hfrt hOt hOst hTt => ?_) 8 (by decide)
    (Nat.le_refl _) Ma _ (by rsimp; rw [hspa, ev_add]; try rfl) (by rsimp; try rfl) (by rsimp; try rfl)
    (by rsimp; exact hspa) (by rsimp)
    (fun x hx => by
      have h1 : x ≠ a0 := fun e => hx (by rw [e]; decide)
      have h2 : x ≠ a1 := fun e => hx (by rw [e]; decide)
      have h3 : x ≠ a2 := fun e => hx (by rw [e]; decide)
      rw [upd_ne' h3 (by rsimp), upd_ne' h2 (by rsimp), upd_ne' h1 hza]) hOa (fun _ _ => rfl) (fun i hi => by omega)
  have t24 : gt 24 = lo := by rw [hfrt 24 (by decide)]; exact ha24
  have t20 : gt 20 = hi := by rw [hfrt 20 (by decide)]; exact ha20
  refine WP.sw rkr_at_132 (by rw [hspt]; exact E.alF (c := 0x328) (by decide))
    (by rw [hspt]; exact E.cF (c := 0x328) (by decide)) ?_
  wn
  refine WP.sw rkr_at_136 (by rw [hspt]; exact E.alF (c := 0x32C) (by decide))
    (by rw [hspt]; exact E.cF (c := 0x32C) (by decide)) ?_
  wn
  refine WP.sw rkr_at_13a (by rw [hspt]; exact E.alF (c := 0x550) (by decide))
    (by rw [hspt]; exact E.cF (c := 0x550) (by decide)) ?_
  wn
  rw [hspt, t24, t20, hzt]
  have hgt : ∀ x, x ∉ rkhL → gt x = gS x := fun x hx => (hfrt x (rkh_sub x hx)).trans (hfra' x hx)
  have eMb : memStore32 (memStore32 (memStore32 Mt (F + 808) lo) (F + 812) hi) (F + 1360) 0 =
      memStore32 (memStore32 (memStore32 Mt (F + BitVec.ofNat 32 0x328) lo) (F + BitVec.ofNat 32 0x32C) hi)
        (F + BitVec.ofNat 32 0x550) 0 := rfl
  rw [eMb]
  have hMbF : ∀ c, c + 1 ≤ 0xAC0 → (c < 0x328 ∨ 0x330 ≤ c) → (c < 0x550 ∨ 0x554 ≤ c) →
      memStore32 (memStore32 (memStore32 Mt (F + BitVec.ofNat 32 0x328) lo) (F + BitVec.ofNat 32 0x32C) hi)
        (F + BitVec.ofNat 32 0x550) 0 (F + BitVec.ofNat 32 c) = Mt (F + BitVec.ofNat 32 c) := by
    intro c hc h1 h2
    have s1 : Sep (F + BitVec.ofNat 32 0x550) 4 (F + BitVec.ofNat 32 c) 1 := by
      rcases h2 with h2 | h2
      · exact rk_ff F (Or.inr (by omega)) (by decide) (by omega)
      · exact rk_ff F (Or.inl (by omega)) (by decide) (by omega)
    have s2 : Sep (F + BitVec.ofNat 32 0x32C) 4 (F + BitVec.ofNat 32 c) 1 := by
      rcases h1 with h1 | h1
      · exact rk_ff F (Or.inr (by omega)) (by decide) (by omega)
      · exact rk_ff F (Or.inl (by omega)) (by decide) (by omega)
    have s3 : Sep (F + BitVec.ofNat 32 0x328) 4 (F + BitVec.ofNat 32 c) 1 := by
      rcases h1 with h1 | h1
      · exact rk_ff F (Or.inr (by omega)) (by decide) (by omega)
      · exact rk_ff F (Or.inl (by omega)) (by decide) (by omega)
    rw [memStore32_get_sep s1, memStore32_get_sep s2, memStore32_get_sep s3]
  have hMb0 : memLoad32 (memStore32 (memStore32 (memStore32 Mt (F + BitVec.ofNat 32 0x328) lo)
      (F + BitVec.ofNat 32 0x32C) hi) (F + BitVec.ofNat 32 0x550) 0) (F + BitVec.ofNat 32 0x328) = lo := by
    rw [memLoad32_store32_sep (rk_ff F (Or.inr (by decide)) (by decide) (by decide)),
      memLoad32_store32_sep (rk_ff F (Or.inr (by decide)) (by decide) (by decide)), memLoad32_store32_same]
  have hMb1 : memLoad32 (memStore32 (memStore32 (memStore32 Mt (F + BitVec.ofNat 32 0x328) lo)
      (F + BitVec.ofNat 32 0x32C) hi) (F + BitVec.ofNat 32 0x550) 0) (F + BitVec.ofNat 32 0x32C) = hi := by
    rw [memLoad32_store32_sep (rk_ff F (Or.inr (by decide)) (by decide) (by decide)), memLoad32_store32_same]
  have hMb2 : memLoad32 (memStore32 (memStore32 (memStore32 Mt (F + BitVec.ofNat 32 0x328) lo)
      (F + BitVec.ofNat 32 0x32C) hi) (F + BitVec.ofNat 32 0x550) 0) (F + BitVec.ofNat 32 0x550) = 0 :=
    memLoad32_store32_same _ _ _
  have hOb : Out M1 (memStore32 (memStore32 (memStore32 Mt (F + BitVec.ofNat 32 0x328) lo)
      (F + BitVec.ofNat 32 0x32C) hi) (F + BitVec.ofNat 32 0x550) 0) s 3004 :=
    ((hOt.trans (E.outF (out_store32 _ _ _) (by decide))).trans (E.outF (out_store32 _ _ _) (by decide))).trans
      (E.outF (out_store32 _ _ _) (by decide))
  generalize memStore32 (memStore32 (memStore32 Mt (F + BitVec.ofNat 32 0x328) lo)
      (F + BitVec.ofNat 32 0x32C) hi) (F + BitVec.ofNat 32 0x550) 0 = Mb at hMbF hMb0 hMb1 hMb2 hOb ⊢
  have hcb := E.code hOb
  refine WP.aluImm rkr_at_13e ?_; wn
  refine WP.aluImm rkr_at_142 ?_; wn
  refine WP.aluImm rkr_at_146 ?_; wn
  refine WP.alu rkr_at_14a ?_; wn
  refine WP.callMemcpy (dst := F + BitVec.ofNat 32 0x330) (src := F + 0x55C) (F := s + BitVec.ofNat 32 288)
    (N := 0x200) rkr_at_14c rkr_at_150 (by decide) (by decide) (by decide) hcb.tps.bms
    (E.mcFF hcb (c := 0x330) (d := 0x55C) (n := 0x200) (Or.inl (by decide)) (by decide) (by decide)
      (by decide) (by decide))
    (by rsimp; rw [ev0, hspt]; rfl) (by rsimp; rw [hspt]; rfl) (by rsimp; try rfl)
    (by rsimp; rw [hspt]; exact (E.sp 288 (by decide)).symm) (E.cS (by decide)) (E.cF (by decide)) fun m2 hm2 => ?_
  wn
  have hO2 : Out M1 m2.mem s 3004 :=
    (hOb.trans (E.outF (c := 0x330) (l := 0x200) (fun x hx => copyBytes_sep hx.symm (Nat.le_refl _)) (by decide))).trans
      (hm2.widen (by decide))
  have hc2 := E.code hO2
  refine WP.aluImm rkr_at_154 ?_; wn
  refine WP.aluImm rkr_at_158 ?_; wn
  refine WP.alu rkr_at_15c ?_; wn
  refine WP.aluImm rkr_at_15e ?_; wn
  refine WP.callMemsetT (tb := TPS_MS) (dst := F + BitVec.ofNat 32 0x530) (b := 0) (n := 0x20) rkr_at_160
    rkr_at_164 (by decide) (by decide) (by decide) hc2.tps.ms
    (by rsimp; rw [ev0, hspt]; rfl) (by rsimp; try rfl) (by rsimp; try rfl)
    (Nat.lt_of_le_of_lt (E.wF (c := 0x530) (k := 0x20) (by decide)) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) (E.cF (by decide)) fun m3 hm3 => ?_
  wn
  have hO3 : Out M1 m3.mem s 3004 :=
    hO2.trans (E.outF (c := 0x530) (l := 0x20) (by rw [hm3]; exact fun x hx => fillBytes_sep hx.symm (Nat.le_refl _))
      (by decide))
  have hc3 := E.code hO3
  refine WP.aluImm rkr_at_168 ?_; wn
  refine WP.aluImm rkr_at_16a ?_; wn
  refine WP.aluImm rkr_at_16e ?_; wn
  refine WP.callMemcpy (dst := F + 0x18) (src := F + 0x75C) (F := s + BitVec.ofNat 32 288)
    (N := 0x310) rkr_at_172 rkr_at_176 (by decide) (by decide) (by decide) hc3.tps.bms
    (E.mcFF hc3 (c := 0x18) (d := 0x75C) (n := 0x310) (Or.inl (by decide)) (by decide) (by decide)
      (by decide) (by decide))
    (by rsimp; rw [hspt]; rfl) (by rsimp; rw [hspt]; rfl) (by rsimp; try rfl)
    (by rsimp; rw [hspt]; exact (E.sp 288 (by decide)).symm) (E.cS (by decide)) (E.cF (c := 0x18) (by decide))
    fun m4 hm4 => ?_
  wn
  have hO4 : Out M1 m4.mem s 3004 :=
    (hO3.trans (E.outF (c := 0x18) (l := 0x310) (fun x hx => copyBytes_sep hx.symm (Nat.le_refl _)) (by decide))).trans
      (hm4.widen (by decide))
  refine K _ _ (by rsimp; exact hspt) (by rsimp) (by rsimp; rw [hspt, ev_add]; rfl) (by rsimp; rw [hspt, ev_add]; rfl)
    (by keepz hzS) hO4 ?_
  have L4 : ∀ c, c + 1 ≤ 0xAC0 →
      m4.mem (F + BitVec.ofNat 32 c) = copyBytes m3.mem (F + 0x18) (F + 0x75C) 0x310 (F + BitVec.ofNat 32 c) :=
    fun c hc => hm4 _ (E.fs (Or.inr (by omega)) hc (by decide))
  have L2 : ∀ c, c + 1 ≤ 0xAC0 →
      m2.mem (F + BitVec.ofNat 32 c) = copyBytes Mb (F + BitVec.ofNat 32 0x330) (F + 0x55C) 0x200 (F + BitVec.ofNat 32 c) :=
    fun c hc => hm2 _ (E.fs (Or.inr (by omega)) hc (by decide))
  have sd : ∀ d, 0x328 ≤ d → d + 1 ≤ 0xAC0 → Sep (F + 0x18) 0x310 (F + BitVec.ofNat 32 d) 1 :=
    fun d h1 h2 => rk_ff F (c := 0x18) (n := 0x310) (d := d) (k := 1) (Or.inl (by omega)) (by decide) h2
  have hdn : ∀ c, 0x328 ≤ c → c + 1 ≤ 0xAC0 → (c < 0x330 ∨ 0x550 ≤ c) →
      m4.mem (F + BitVec.ofNat 32 c) = Mb (F + BitVec.ofNat 32 c) := by
    intro c h1 hc h2
    have sf : Sep (F + BitVec.ofNat 32 0x530) 0x20 (F + BitVec.ofNat 32 c) 1 := by
      rcases h2 with h2 | h2
      · exact rk_ff F (Or.inr (by omega)) (by decide) hc
      · exact rk_ff F (Or.inl (by omega)) (by decide) hc
    have sc : Sep (F + BitVec.ofNat 32 0x330) 0x200 (F + BitVec.ofNat 32 c) 1 := by
      rcases h2 with h2 | h2
      · exact rk_ff F (Or.inr (by omega)) (by decide) hc
      · exact rk_ff F (Or.inl (by omega)) (by decide) hc
    rw [L4 c hc, copyBytes_sep (sd c h1 hc) (Nat.le_refl _), hm3, fillBytes_sep sf (Nat.le_refl _), L2 c hc, copyBytes_sep sc (Nat.le_refl _)]
  have hld : ∀ c, 0x328 ≤ c → c + 4 ≤ 0xAC0 → (c + 4 ≤ 0x330 ∨ 0x550 ≤ c) →
      memLoad32 m4.mem (F + BitVec.ofNat 32 c) = memLoad32 Mb (F + BitVec.ofNat 32 c) := by
    intro c h1 hc h2
    refine memLoad32_congr fun j hj => ?_
    have h2' : c + j < 0x330 ∨ 0x550 ≤ c + j := by
      rcases h2 with h2 | h2
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [add_ofNat_assoc]; exact hdn _ (by omega) (by omega) h2'
  unfold RkAt RkB
  refine ⟨Nat.zero_le _, ?_, ?_, fun i hi => ⟨Nat.zero_le _, fun j hj => ?_, ?_, ?_⟩⟩
  · rw [rk_w32, rk_w32, rk_ra, rk_ra, (hld (0x18 + 0x314) (by decide) (by decide) (Or.inl (by decide))).trans hMb1,
      (hld (0x18 + 0x310) (by decide) (by decide) (Or.inl (by decide))).trans hMb0]
  · rw [rk_w32, rk_ra]; exact (hld (0x18 + 0x538) (by decide) (by decide) (Or.inr (by decide))).trans hMb2
  · show m4.mem (F + 0x18 + BitVec.ofNat 32 (0x318 + 64 * i + j)) = BitVec.ofNat 8 0
    rw [rk_ra, L4 _ (by omega), copyBytes_sep (sd _ (by omega) (by omega)) (Nat.le_refl _), hm3,
      fillBytes_sep (rk_ff F (c := 0x530) (n := 0x20) (d := 0x18 + (0x318 + 64 * i + j)) (k := 1) (Or.inr (by omega))
        (by decide) (by omega)) (Nat.le_refl _), L2 _ (by omega),
      show F + BitVec.ofNat 32 (0x18 + (0x318 + 64 * i + j)) = F + BitVec.ofNat 32 0x330 + BitVec.ofNat 32 (64 * i + j) by
        rw [add_ofNat_assoc, show 0x330 + (64 * i + j) = 0x18 + (0x318 + 64 * i + j) by omega],
      copyBytes_at (by omega) (by decide),
      show F + 0x55C + BitVec.ofNat 32 (64 * i + j) = F + BitVec.ofNat 32 (0x55C + (64 * i + j)) from
        add_ofNat_assoc F 0x55C _,
      hMbF _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)),
      hOst _ (rk_ff F (Or.inl (by omega)) (by omega) (by decide)), hZa _ (by omega)]
    rfl
  · rw [rk_w32, rk_ra]
    refine rkh_ld0 fun j hj => ?_
    rw [add_ofNat_assoc, L4 _ (by omega), copyBytes_sep (sd _ (by omega) (by omega)) (Nat.le_refl _), hm3,
      show F + BitVec.ofNat 32 (0x18 + (0x518 + 4 * i) + j) = F + BitVec.ofNat 32 0x530 + BitVec.ofNat 32 (4 * i + j) by
        rw [add_ofNat_assoc, show 0x530 + (4 * i + j) = 0x18 + (0x518 + 4 * i) + j by omega],
      rkh_fill (by omega) (by decide)]
    rfl
  · show m4.mem (F + 0x18 + BitVec.ofNat 32 (98 * i)) = 0xFF
    have hcp := copyBytes_at (M := m3.mem) (dst := F + 0x18) (src := F + 0x75C) (N := 0x310) (i := 98 * i) (by omega)
      (by decide)
    rw [rk_ra] at hcp
    rw [rk_ra, L4 _ (by omega), hcp,
      show F + 0x75C + BitVec.ofNat 32 (98 * i) = F + BitVec.ofNat 32 (0x75C + 98 * i) from add_ofNat_assoc F 0x75C _,
      hm3, fillBytes_sep (rk_ff F (c := 0x530) (n := 0x20) (d := 0x75C + 98 * i) (k := 1) (Or.inl (by omega))
        (by decide) (by omega)) (Nat.le_refl _), L2 _ (by omega),
      copyBytes_sep (rk_ff F (c := 0x330) (n := 0x200) (d := 0x75C + 98 * i) (k := 1) (Or.inl (by omega))
        (by decide) (by omega)) (Nat.le_refl _),
      hMbF _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))]
    exact hTt i hi

theorem RkAt.upF {M M' : Word → BitVec 8} {t : Nat} {es : List RkEntry} {c n : Nat}
    (hB : RkAt M (F + 0x18) t es) (h : Out M M' (F + BitVec.ofNat 32 c) n) (hc : 0x558 ≤ c) (hcn : c + n ≤ 0xAC0) :
    RkAt M' (F + 0x18) t es :=
  RkB.congr hB fun o ho => by
    show M' (F + 0x18 + BitVec.ofNat 32 o) = M (F + 0x18 + BitVec.ofNat 32 o)
    rw [rk_ra]; exact h _ (rk_ff F (Or.inl (by omega)) (by omega) hcn)

theorem RkAt.upS (E : RkEnv M0 M1 s out F P N g0) {M M' : Word → BitVec 8} {t : Nat} {es : List RkEntry}
    {d k : Nat} (hB : RkAt M (F + 0x18) t es) (h : Out M M' (s + BitVec.ofNat 32 d) k) (hd : d + k ≤ 304) :
    RkAt M' (F + 0x18) t es :=
  RkB.congr hB fun o ho => by
    show M' (F + 0x18 + BitVec.ofNat 32 o) = M (F + 0x18 + BitVec.ofNat 32 o)
    rw [rk_ra]; exact h _ (E.fs (Or.inr (by omega)) (by omega) (by omega))

/-- A call to `field` from the start of `RoleKeys::read`, with its result
at `F + o`. -/
theorem rkh_field (E : RkEnv M0 M1 s out F P N g0) {M : Word → BitVec 8} (hO : Out M1 M s 3004)
    {off o n kl : Nat} {hi lo p kq : Word} {key : Bytes} {f : Fin 32 → Word}
    (h1 : fetchRel tufRoleKeysReadCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel tufRoleKeysReadCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : TRK + BitVec.ofNat 32 off + hi + lo = TPM_JF) (hev : (off + 8) % 2 = 0)
    (hsp : f sp = F) (h0 : f a0 = F + BitVec.ofNat 32 o) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (ha3 : f a3 = kq) (ha4 : f a4 = BitVec.ofNat 32 kl) (ho : o + 8 ≤ 0xA8C) (hoa : o % 4 = 0)
    (hkl : kl < 2 ^ 32) (hp0 : p.toNat ≠ 0) (hpw : p.toNat + n ≤ 0x40000000) (hSp : Sep s 3056 p n)
    (hSk : Sep (s + BitVec.ofNat 32 44) 260 kq kl) (hkey : memBytes M kq kl = key)
    (k : ∀ (m2 : Machine) Mb, Out M1 m2.mem s 3004 → Out M Mb (s + BitVec.ofNat 32 44) 260 →
      FieldRes Mb m2.mem (F + BitVec.ofNat 32 o) (fieldRes p (objField (memBytes M0 p n) key)) →
      WP tufRoleKeysReadCode TRK Q m2.mem (off + 8) (clob (upd f ra (TRK + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP tufRoleKeysReadCode TRK Q M off f := by
  have hc := E.code hO
  refine WP.callField (tb := TPM_JF) (out := F + BitVec.ofNat 32 o) (s := s + BitVec.ofNat 32 44) (p := p)
    (kq := kq) (n := n) (kl := kl) h1 h2 htgt (by decide) hev hc.pm.fieldC h0 ha1 ha2 ha3 ha4
    (by rw [hsp]; exact (E.sp 44 (by decide)).symm) (E.alS (by decide)) (E.alF hoa)
    (by have := E.wS (d := 44) (k := 260) (by decide); omega) hkl hp0 (by omega)
    (tuf_fieldSep (E.wS (by decide)) (E.hro.sub (by decide))) (hSp.sub (by decide)) hSk
    (E.fs (Or.inr (by omega)) (by omega) (by decide)) (E.lowF (by omega) (by decide) (by decide))
    (E.lowS (by decide) (by decide) (by decide)) (E.lowF (by omega) (by decide) (by decide)) fun m2 hR => ?_
  rw [E.bytes hO hSp, hkey] at hR
  obtain ⟨Mb, hOb, hFR⟩ := hR
  have hOo : Out Mb m2.mem (F + BitVec.ofNat 32 o) 8 := by
    rcases hr : fieldRes p (objField (memBytes M0 p n) key) with _ | ⟨_, _⟩ <;> rw [hr] at hFR <;> exact hFR.1
  exact k m2 Mb ((hO.trans (hOb.widen (by decide))).trans (E.outF hOo (by omega))) hOb hFR

/-- A call to `elements` with its result at `F + 0x75C`. -/
theorem rkh_elems (E : RkEnv M0 M1 s out F P N g0) {M : Word → BitVec 8} (hO : Out M1 M s 3004)
    {off n : Nat} {hi lo p : Word} {f : Fin 32 → Word}
    (h1 : fetchRel tufRoleKeysReadCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel tufRoleKeysReadCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : TRK + BitVec.ofNat 32 off + hi + lo = TPM_JEL) (hev : (off + 8) % 2 = 0)
    (hsp : f sp = F) (h0 : f a0 = F + BitVec.ofNat 32 0x75C) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (hn : n < 2 ^ 32) (hSp : Sep s 3056 p n)
    (k : ∀ (m2 : Machine) Mb, Out M1 m2.mem s 3004 → Out M Mb (s + BitVec.ofNat 32 288) 16 →
      CurRes Mb m2.mem (F + BitVec.ofNat 32 0x75C) 0x21 (curOpen 91 p (memBytes M0 p n)) →
      WP tufRoleKeysReadCode TRK Q m2.mem (off + 8) (clob (upd f ra (TRK + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP tufRoleKeysReadCode TRK Q M off f := by
  have hc := E.code hO
  refine WP.callElements (tb := TPM_JEL) (out := F + BitVec.ofNat 32 0x75C) (s := s + BitVec.ofNat 32 288)
    (p := p) (n := n) h1 h2 htgt (by decide) hev hc.pm.el hc.pm.sw h0 ha1 ha2
    (by rw [hsp]; exact (E.sp 288 (by decide)).symm) hn (E.alS (by decide)) (E.alF (by decide))
    (E.lowS (by decide) (by decide) (by decide)) (E.lowS (by decide) (by decide) (by decide)) (hSp.sub (by decide))
    (E.fs (Or.inr (by decide)) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide))
    (E.lowS (by decide) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide)) fun m2 hR => ?_
  rw [E.bytes hO hSp] at hR
  obtain ⟨Mb, hOb, hCR⟩ := hR
  exact k m2 Mb ((hO.trans (hOb.widen (by decide))).trans (E.outF hCR.out (by decide))) hOb hCR

/-- A call to `u64` with its result at `F + 0x18`. -/
theorem rkh_u64 (E : RkEnv M0 M1 s out F P N g0) {M : Word → BitVec 8} (hO : Out M1 M s 3004)
    {off n : Nat} {hi lo p : Word} {f : Fin 32 → Word}
    (h1 : fetchRel tufRoleKeysReadCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel tufRoleKeysReadCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : TRK + BitVec.ofNat 32 off + hi + lo = TPR_JU) (hev : (off + 8) % 2 = 0)
    (hsp : f sp = F) (h0 : f a0 = F + BitVec.ofNat 32 0x18) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (hn : n < 2 ^ 32) (hSp : Sep s 3056 p n)
    (k : ∀ (m2 : Machine) Mb, Out M1 m2.mem s 3004 → Out M Mb (s + BitVec.ofNat 32 272) 32 →
      U64Res Mb m2.mem (F + BitVec.ofNat 32 0x18) (u64Val (memBytes M0 p n)) →
      WP tufRoleKeysReadCode TRK Q m2.mem (off + 8) (clob (upd f ra (TRK + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP tufRoleKeysReadCode TRK Q M off f := by
  have hc := E.code hO
  refine WP.callU64 (out := F + BitVec.ofNat 32 0x18) (s := s + BitVec.ofNat 32 272) (p := p) (n := n) h1 h2 htgt
    hev hc.u64 hc.aad h0 ha1 ha2 (by rw [hsp]; exact (E.sp 272 (by decide)).symm) hn (E.alS (by decide))
    (E.alF (by decide)) (E.wS (by decide)) (hSp.sub (by decide)) (E.fs (Or.inr (by decide)) (by decide) (by decide))
    (E.wF (by decide)) (E.cS (by decide)) (E.cF (by decide)) fun m2 hR => ?_
  rw [E.bytes hO hSp] at hR
  obtain ⟨Mb, hOb, hU⟩ := hR
  exact k m2 Mb ((hO.trans (hOb.widen (by decide))).trans (E.outF hU.outside (by decide))) hOb hU

/-- A call to `members` with its result at `F + 0x18`. -/
theorem rkh_mem (E : RkEnv M0 M1 s out F P N g0) {M : Word → BitVec 8} (hO : Out M1 M s 3004)
    {off n : Nat} {hi lo p : Word} {f : Fin 32 → Word}
    (h1 : fetchRel tufRoleKeysReadCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel tufRoleKeysReadCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : TRK + BitVec.ofNat 32 off + hi + lo = TPM_JF + 0x16C + 0xA6) (hev : (off + 8) % 2 = 0)
    (hsp : f sp = F) (h0 : f a0 = F + BitVec.ofNat 32 0x18) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (hn : n < 2 ^ 32) (hSp : Sep s 3056 p n)
    (k : ∀ (m2 : Machine) Mb, Out M1 m2.mem s 3004 → Out M Mb (s + BitVec.ofNat 32 288) 16 →
      CurRes Mb m2.mem (F + BitVec.ofNat 32 0x18) 0x21 (curOpen 123 p (memBytes M0 p n)) →
      WP tufRoleKeysReadCode TRK Q m2.mem (off + 8) (clob (upd f ra (TRK + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP tufRoleKeysReadCode TRK Q M off f := by
  have hc := E.code hO
  refine WP.callMembers (tb := TPM_JF + 0x16C + 0xA6) (out := F + BitVec.ofNat 32 0x18)
    (s := s + BitVec.ofNat 32 288) (p := p) (n := n) h1 h2 htgt (by decide) hev hc.pm.fieldC.get.me
    (by rw [gt_ad_sw]; exact hc.pm.fieldC.get.ri.sw) h0 ha1 ha2 (by rw [hsp]; exact (E.sp 288 (by decide)).symm) hn
    (E.alS (by decide)) (E.alF (by decide)) (E.lowS (by decide) (by decide) (by decide))
    (E.lowS (by decide) (by decide) (by decide)) (hSp.sub (by decide))
    (E.fs (Or.inr (by decide)) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide))
    (E.cS (by decide)) (E.cF (by decide)) fun m2 hR => ?_
  rw [E.bytes hO hSp] at hR
  obtain ⟨Mb, hOb, hCR⟩ := hR
  exact k m2 Mb ((hO.trans (hOb.widen (by decide))).trans (E.outF hCR.out (by decide))) hOb hCR

/-- The `keyids` checks and the loop on the role `r` and the `keys`
value `kv`. -/
def rkKids (r kv : Bytes) : Except Nat (List RkEntry) :=
  match objField r (ascii!"keyids") with
  | .error e => .error e
  | .ok (ip, il) => rkIds (slice r ip il) kv

theorem rkh_e560 (F : Word) : F + BitVec.ofNat 32 0x55C + 4 = F + 0x560 := by rw [BitVec.add_assoc]; rfl

/-- From 0x17A: the role's `keyids` field, the cursor over it, and the
loop. -/
theorem rkh_ids (E : RkEnv M0 M1 s out F P N g0) {M : Word → BitVec 8} {g : Fin 32 → Word} {t RL KL : Nat}
    {RQ KQ : Word} (hO : Out M1 M s 3004) (hB : RkAt M (F + 0x18) t [])
    (hsp : g sp = F) (hz : g 0 = 0) (h27 : g 27 = out) (h23 : g 23 = RQ) (h22 : g 22 = BitVec.ofNat 32 RL)
    (h21 : g 21 = KQ) (h18 : g 18 = BitVec.ofNat 32 KL) (h19 : g 19 = F + BitVec.ofNat 32 0x330)
    (h20 : g 20 = F + BitVec.ofNat 32 0x530) (hfr : ∀ x, x ∉ rkE → g x = g0 x)
    (hR0 : RQ.toNat ≠ 0) (hRN : RQ.toNat + RL ≤ 0x40000000) (hRS : Sep s 3056 RQ RL)
    (hK0 : KQ.toNat ≠ 0) (hKN : KQ.toNat + KL ≤ 0x40000000) (hKS : Sep s 3056 KQ KL) :
    WP tufRoleKeysReadCode TRK (rkQ M0 s out g0 (rkThen (rkKids (memBytes M0 RQ RL) (memBytes M0 KQ KL)) t []))
      M 0x17A g := by
  refine WP.lui rkr_at_17a ?_; wn
  refine WP.aluImm rkr_at_17e ?_; wn
  refine WP.aluImm rkr_at_182 ?_; wn
  refine WP.aluImm rkr_at_186 ?_; wn
  refine WP.alu rkr_at_188 ?_; wn
  refine WP.alu rkr_at_18a ?_; wn
  refine rkh_field (off := 0x18C) (o := 0x55C) (p := RQ) (n := RL) (kq := TRK_KIDS) (kl := 6)
    (key := ascii!"keyids") E hO rkr_at_18c rkr_at_190 (by decide) (by decide) (by rsimp; exact hsp)
    (by rsimp; rw [hsp, ev_add]; rfl) (by rsimp; rw [ev0, h23]) (by rsimp; rw [ev0, h22]) (by rsimp; try rfl)
    (by rsimp; try rfl) (by decide) (by decide) (by decide) hR0 hRN hRS
    (tuf_sep_ro (E.hro.sub (by decide)) (by decide) (by decide)) (E.code hO).mKids fun m2 Mb hO2 hOb hR => ?_
  have hB2 : RkAt m2.mem (F + 0x18) t [] := by
    have hFR : Out Mb m2.mem (F + BitVec.ofNat 32 0x55C) 8 := by
      rcases hr : fieldRes RQ (objField (memBytes M0 RQ RL) (ascii!"keyids")) with _ | ⟨_, _⟩ <;>
        rw [hr] at hR <;> exact hR.1
    exact (RkAt.upS E hB hOb (by decide)).upF hFR (by decide) (by decide)
  rcases hof : objField (memBytes M0 RQ RL) (ascii!"keyids") with e | ⟨ip, il⟩ <;> rw [hof] at hR <;>
    simp only [fieldRes, Except.map, FieldRes] at hR
  · have hm : rkKids (memBytes M0 RQ RL) (memBytes M0 KQ KL) = .error e := by unfold rkKids; rw [hof]
    rw [hm]
    obtain ⟨-, r1, r2⟩ := hR
    rw [rkh_e560] at r2
    rw [show F + BitVec.ofNat 32 0x55C = F + 0x55C from rfl] at r1
    refine WP.lw rkr_at_194 (by rsimp; rw [hsp]; exact E.alF (c := 0x55C) (by decide)) ?_; wn
    refine WP.branch rkr_at_198 (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact rk_93c E hO2 (by rsimp; exact h27) (by rsimp; exact hsp) r2 (by keepz E.hz0)
    · exfalso; (try rsimp at eb); rw [hsp] at eb; rw [r1] at eb; exact absurd eb (by decide)
  obtain ⟨-, r1, r2⟩ := hR
  rw [rkh_e560] at r2
  rw [show F + BitVec.ofNat 32 0x55C = F + 0x55C from rfl] at r1
  have hv := objField_val hof
  rw [memBytes_length] at hv
  obtain ⟨hip, hipl⟩ := hv
  have hipN : (RQ + BitVec.ofNat 32 ip).toNat = RQ.toNat + ip := tex_toNat (by omega)
  have hsl : memBytes M0 (RQ + BitVec.ofNat 32 ip) il = slice (memBytes M0 RQ RL) ip il :=
    (tuf_memBytes_drop_take hipl).symm
  have hm : rkKids (memBytes M0 RQ RL) (memBytes M0 KQ KL) =
      rkIds (memBytes M0 (RQ + BitVec.ofNat 32 ip) il) (memBytes M0 KQ KL) := by
    rw [hsl]; unfold rkKids; rw [hof]
  rw [hm]
  refine WP.lw rkr_at_194 (by rsimp; rw [hsp]; exact E.alF (c := 0x55C) (by decide)) ?_; wn
  refine WP.branch rkr_at_198 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hsp, r1, nx_q0 hR0 (by omega) hip] at eb; exact absurd eb (by decide)
  refine WP.lw rkr_at_19c (by rsimp; rw [hsp]; exact E.alF (c := 0x560) (by decide)) ?_; wn
  refine WP.aluImm rkr_at_1a0 ?_; wn
  refine rkh_elems (off := 0x1A4) (p := RQ + BitVec.ofNat 32 ip) (n := il) E hO2 rkr_at_1a4 rkr_at_1a8
    (by decide) (by decide) (by rsimp; exact hsp) (by rsimp; rw [hsp, ev_add]; rfl) (by rsimp; rw [hsp, r1])
    (by rsimp; rw [hsp, r2]) (by omega) (hRS.subR (by omega)) fun m3 Mc hO3 hOc hC => ?_
  have hB3 : RkAt m3.mem (F + 0x18) t [] := (RkAt.upS E hB2 hOc (by decide)).upF hC.out (by decide) (by decide)
  rw [show F + BitVec.ofNat 32 0x75C = F + 0x75C from rfl] at hC
  by_cases hc : (memBytes M0 (RQ + BitVec.ofNat 32 ip) il).length = 0 ∨
      (memBytes M0 (RQ + BitVec.ofNat 32 ip) il).getD 0 0 ≠ 91
  · have hco : curOpen 91 (RQ + BitVec.ofNat 32 ip) (memBytes M0 (RQ + BitVec.ofNat 32 ip) il) = none := by
      unfold curOpen
      rcases hc with h | h
      · rw [if_pos h]
      · by_cases h0 : (memBytes M0 (RQ + BitVec.ofNat 32 ip) il).length = 0
        · rw [if_pos h0]
        · rw [if_neg h0, if_pos h]
    have hr : rkIds (memBytes M0 (RQ + BitVec.ofNat 32 ip) il) (memBytes M0 KQ KL) = .error 0x21 := by
      unfold rkIds; rw [if_pos hc]
    rw [hr]; rw [hco] at hC
    obtain ⟨-, t1, t2⟩ := hC
    rw [rk_e760] at t2
    refine WP.lw rkr_at_1ac (by rsimp; rw [hsp]; exact E.alF (c := 0x75C) (by decide)) ?_; wn
    refine WP.lbu rkr_at_1b0 ?_; wn
    refine WP.branch rkr_at_1b4 (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact rk_942 E hO3 (by rsimp; exact h27) (by rsimp; exact hsp) (by rsimp; rw [hsp, tlv_zext, t2]; rfl) (by rsimp)
        (by keepz E.hz0)
    · exfalso; (try rsimp at eb); rw [hsp, t1] at eb; exact absurd eb (by decide)
  have h0 : ¬(memBytes M0 (RQ + BitVec.ofNat 32 ip) il).length = 0 := fun h => hc (Or.inl h)
  have h1 : ¬(memBytes M0 (RQ + BitVec.ofNat 32 ip) il).getD 0 0 ≠ 91 := fun h => hc (Or.inr h)
  have hco : curOpen 91 (RQ + BitVec.ofNat 32 ip) (memBytes M0 (RQ + BitVec.ofNat 32 ip) il) =
      some (RQ + BitVec.ofNat 32 ip, il, skipWs (memBytes M0 (RQ + BitVec.ofNat 32 ip) il) 1) := by
    unfold curOpen; rw [if_neg h0, if_neg h1, memBytes_length]
  have hr : rkIds (memBytes M0 (RQ + BitVec.ofNat 32 ip) il) (memBytes M0 KQ KL) =
      rkLoop (memBytes M0 (RQ + BitVec.ofNat 32 ip) il) (memBytes M0 KQ KL) 8
        (skipWs (memBytes M0 (RQ + BitVec.ofNat 32 ip) il) 1) := by
    unfold rkIds; rw [if_neg hc]
  rw [hr]; rw [hco] at hC
  obtain ⟨-, t1, t2, t3⟩ := hC
  rw [rk_e760] at t2
  rw [show F + 0x75C + 8 = F + 0x764 by rw [BitVec.add_assoc]; rfl] at t3
  have hpos : skipWs (memBytes M0 (RQ + BitVec.ofNat 32 ip) il) 1 ≤ il := by
    have := skipWs_le (memBytes M0 (RQ + BitVec.ofNat 32 ip) il) 1
    rw [memBytes_length] at this h0; omega
  refine WP.lw rkr_at_1ac (by rsimp; rw [hsp]; exact E.alF (c := 0x75C) (by decide)) ?_; wn
  refine WP.lbu rkr_at_1b0 ?_; wn
  refine WP.branch rkr_at_1b4 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hsp, t1, nx_q0 hR0 (n := RL) (pos := ip) (by omega) hip] at eb
    exact absurd eb (by decide)
  refine WP.aluImm rkr_at_1b8 ?_; wn
  refine WP.aluImm rkr_at_1bc ?_; wn
  refine WP.aluImm rkr_at_1c0 ?_; wn
  refine WP.aluImm rkr_at_1c4 ?_; wn
  have hc3 := E.code hO3
  refine WP.callMemcpy (dst := F + BitVec.ofNat 32 0xA71) (src := F + 0x761) (F := s + BitVec.ofNat 32 288)
    (N := 7) rkr_at_1c6 rkr_at_1ca (by decide) (by decide) (by decide) hc3.tps.bms
    (E.mcFF hc3 (c := 0xA71) (d := 0x761) (n := 7) (Or.inr (by decide)) (by decide) (by decide)
      (by decide) (by decide))
    (by rsimp; rw [hsp, ev_add, ev_add, BitVec.add_assoc]; rfl) (by rsimp; rw [hsp]; rfl) (by rsimp; try rfl)
    (by rsimp; rw [hsp]; exact (E.sp 288 (by decide)).symm) (E.cS (by decide)) (E.cF (c := 0xA71) (by decide))
    fun m4 hm4 => ?_
  wn
  have hO4 : Out M1 m4.mem s 3004 :=
    (hO3.trans (E.outF (c := 0xA71) (l := 7) (fun x hx => copyBytes_sep hx.symm (Nat.le_refl _)) (by decide))).trans
      (hm4.widen (by decide))
  have e24 : aluEval .add (aluEval .add F 0x7FF) 0x26D = F + 0xA6C := by rw [ev_add, ev_add, BitVec.add_assoc]; rfl
  refine WP.aluImm rkr_at_1ce ?_; wn
  refine WP.aluImm rkr_at_1d2 ?_; wn
  have e70 : F + 0xA6C + 4 = F + 0xA70 := by rw [BitVec.add_assoc]; rfl
  refine WP.sw rkr_at_1d6 (by rsimp; rw [hsp, e24, add_lit_zero]; exact E.alF (c := 0xA6C) (by decide))
    (by rsimp; rw [hsp, e24, add_lit_zero]; exact E.cF (c := 0xA6C) (by decide)) ?_; wn
  refine WP.sb rkr_at_1da (by rsimp; rw [hsp, e24, e70]; exact E.cF (c := 0xA70) (by decide)) ?_; wn
  refine WP.aluImm rkr_at_1de ?_; wn
  refine WP.aluImm rkr_at_1e0 ?_; wn
  refine WP.aluImm rkr_at_1e4 ?_; wn
  have hcp : ∀ i < 7, m4.mem (F + BitVec.ofNat 32 (0xA71 + i)) = m3.mem (F + BitVec.ofNat 32 (0x761 + i)) := by
    intro i hi
    rw [hm4 _ (E.fs (Or.inr (by omega)) (by omega) (by decide)),
      show F + BitVec.ofNat 32 (0xA71 + i) = F + BitVec.ofNat 32 0xA71 + BitVec.ofNat 32 i from
        (add_ofNat_assoc F _ _).symm,
      copyBytes_at hi (by decide),
      show F + 0x761 + BitVec.ofNat 32 i = F + BitVec.ofNat 32 (0x761 + i) from add_ofNat_assoc F 0x761 i]
  have hMk : memStore8 (memStore32 m4.mem (aluEval AluOp.add (aluEval AluOp.add (g sp) 2047) 621 + 0)
      (memLoad32 m3.mem (g sp + 1884))) (aluEval AluOp.add (aluEval AluOp.add (g sp) 2047) 621 + 4)
      (BitVec.extractLsb' 0 8 (BitVec.zeroExtend 32 (m3.mem (g sp + 1888)))) =
      memStore8 (memStore32 m4.mem (F + 0xA6C) (RQ + BitVec.ofNat 32 ip)) (F + 0xA70) (m3.mem (F + 0x760)) := by
    rw [hsp, e24, add_lit_zero, e70, tlv_zext]; rw [t1]
  rw [hMk]
  generalize hMkd : memStore8 (memStore32 m4.mem (F + 0xA6C) (RQ + BitVec.ofNat 32 ip)) (F + 0xA70)
    (m3.mem (F + 0x760)) = Mk
  have hMb : ∀ i, 0xA71 ≤ i → i < 0xA78 → Mk (F + BitVec.ofNat 32 i) = m3.mem (F + BitVec.ofNat 32 (i - 0x310)) := by
    intro i h1 h2
    have s8 : Sep (F + BitVec.ofNat 32 i) 1 (F + 0xA70) 1 := rk_ff F (d := 0xA70) (Or.inr (by omega)) (by omega) (by decide)
    have s32 : Sep (F + BitVec.ofNat 32 i) 1 (F + 0xA6C) 4 := rk_ff F (d := 0xA6C) (Or.inr (by omega)) (by omega) (by decide)
    rw [← hMkd, out_store8 _ _ _ _ s8, out_store32 _ _ _ _ s32]
    have := hcp (i - 0xA71) (by omega)
    rw [show 0xA71 + (i - 0xA71) = i by omega, show 0x761 + (i - 0xA71) = i - 0x310 by omega] at this
    exact this
  have hOk : Out M1 Mk s 3004 := by
    rw [← hMkd]
    exact hO4.trans ((E.outF (c := 0xA6C) (l := 4) (out_store32 _ _ _) (by decide)).trans
      (E.outF (c := 0xA70) (l := 1) (out_store8 _ _ _) (by decide)))
  have hBk : RkAt Mk (F + 0x18) t [] := by
    rw [← hMkd]
    exact (((RkAt.upS E (hB3.upF (fun x hx => copyBytes_sep hx.symm (Nat.le_refl _)) (by decide) (by decide))
      hm4 (by decide)).upF (c := 0xA6C) (out_store32 _ _ _) (by decide) (by decide)).upF (c := 0xA70)
      (out_store8 _ _ _) (by decide) (by decide))
  have c0 : memLoad32 Mk (F + 0xA6C) = RQ + BitVec.ofNat 32 ip := by
    have s70 : Sep (F + 0xA70) 1 (F + 0xA6C) 4 := rk_ff F (d := 0xA6C) (Or.inr (by decide)) (by decide) (by decide)
    rw [← hMkd, memLoad32_store8_sep s70, memLoad32_store32_same]
  have c1 : memLoad32 Mk (F + 0xA70) = BitVec.ofNat 32 il := by
    rw [← t2]
    refine memLoad32_congr2 fun j hj => ?_
    rw [show F + 0xA70 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0xA70 + j) from add_ofNat_assoc F 0xA70 j,
      show F + 0x760 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x760 + j) from add_ofNat_assoc F 0x760 j]
    by_cases j0 : j = 0
    · subst j0; rw [← hMkd]; exact memStore8_same _ _ _
    · rw [hMb _ (by omega) (by omega), show 0xA70 + j - 0x310 = 0x760 + j by omega]
  have c2 : memLoad32 Mk (F + 0xA74) =
      BitVec.ofNat 32 (skipWs (memBytes M0 (RQ + BitVec.ofNat 32 ip) il) 1) := by
    rw [← t3]
    refine memLoad32_congr2 fun j hj => ?_
    rw [show F + 0xA74 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0xA74 + j) from add_ofNat_assoc F 0xA74 j,
      show F + 0x764 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x764 + j) from add_ofNat_assoc F 0x764 j,
      hMb _ (by omega) (by omega), show 0xA74 + j - 0x310 = 0x764 + j by omega]
  refine rk_loop E (AP := RQ + BitVec.ofNat 32 ip) (AN := il) (by rw [hipN]; omega) (by rw [hipN]; omega)
    (hRS.subR (by omega)) hK0 hKN hKS 8 _ [] Mk _ rfl hpos ⟨hOk, hBk, c0, c1, c2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
  · rsimp; exact hsp
  · rsimp; exact h27
  · rsimp; exact h19
  · rsimp; exact h20
  · rsimp; exact h21
  · rsimp; exact h18
  · rsimp; done
  · rsimp; rw [hsp, e24]
  · rsimp; rw [hsp, ev_add]; rfl
  · rsimp; done
  · rsimp
  · keepz E.hz0

theorem rkh_e760 (F : Word) : F + BitVec.ofNat 32 0x75C + 4 = F + 0x760 := by rw [BitVec.add_assoc]; rfl
theorem rkh_e19 (F : Word) : F + BitVec.ofNat 32 0x18 + 1 = F + 0x19 := by rw [BitVec.add_assoc]; rfl
theorem rkh_e20 (F : Word) : F + BitVec.ofNat 32 0x18 + 8 = F + 0x20 := by rw [BitVec.add_assoc]; rfl
theorem rkh_e24 (F : Word) : F + BitVec.ofNat 32 0x18 + 12 = F + 0x24 := by rw [BitVec.add_assoc]; rfl

theorem rkh_keep (g0 : Fin 32 → Word) {Q : Post} {M : Word → BitVec 8} {off : Nat} {G : Fin 32 → Word}
    (hS : ∀ x, x ∉ rkE → G x = g0 x) (k : (∀ x, x ∉ rkE → G x = g0 x) → WP tufRoleKeysReadCode TRK Q M off G) :
    WP tufRoleKeysReadCode TRK Q M off G := k hS

theorem rkh_role {r kv : Bytes} (h : ¬(kv.length = 0 ∨ kv.getD 0 0 ≠ 123)) : rkRole r kv = rkKids r kv := by
  unfold rkRole rkKids; rw [if_neg h]
  rcases objField r (ascii!"keyids") with _ | ⟨_, _⟩ <;> rfl

theorem rkh_sub2 : ∀ x, x ∉ rkE → x ∉ rkhL := by decide
theorem rkh_e1c (F : Word) : F + BitVec.ofNat 32 0x18 + 4 = F + 0x1C := by rw [BitVec.add_assoc]; rfl
theorem rkh_bt {x : Word} (h : branchTaken .beq x 0 = true) : x = 0 := of_decide_eq_true h
theorem rkh_bf {x : Word} (h : branchTaken .beq x 0 = false) : x ≠ 0 := of_decide_eq_false h

theorem rkh_thr0 {lo hi : Word} {v : Nat} (hv : hi.toNat * 2 ^ 32 + lo.toNat = v) : lo ||| hi = 0 ↔ v = 0 := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h
    rw [← hv, h1, h2]; rfl
  · intro h0
    have h1 : hi.toNat = 0 := by omega
    have h2 : lo.toNat = 0 := by omega
    exact BitVec.or_eq_zero_iff.mpr ⟨BitVec.eq_of_toNat_eq h2, BitVec.eq_of_toNat_eq h1⟩

/-- From the moves after the prologue to the `keyids` checks: the
`roles`, role, and `threshold` lookups, the threshold, and the `keys`
object. -/
theorem rkh_head (E : RkEnv M0 M1 s out F P N g0) {M : Word → BitVec 8} {g : Fin 32 → Word} {RP : Word}
    {RN : Nat} (hO : Out M1 M s 3004) (hsp : g sp = F) (hz : g 0 = 0) (ha0 : g a0 = out) (ha1 : g a1 = P)
    (ha2 : g a2 = BitVec.ofNat 32 N) (ha3 : g a3 = RP) (ha4 : g a4 = BitVec.ofNat 32 RN)
    (hfr : ∀ x, x ∉ rkE → g x = g0 x) (hRN : RN < 2 ^ 32) (hRS : Sep s 3056 RP RN) :
    WP tufRoleKeysReadCode TRK (rkQ M0 s out g0 (rkModel (memBytes M0 P N) (memBytes M0 RP RN))) M 0x3C g := by
  have hP0 := E.hP0
  have hPN := E.hPN
  refine WP.alu rkr_at_3c ?_; wn
  refine WP.alu rkr_at_3e ?_; wn
  refine WP.alu rkr_at_40 ?_; wn
  refine WP.alu rkr_at_42 ?_; wn
  refine WP.alu rkr_at_44 ?_; wn
  refine WP.lui rkr_at_46 ?_; wn
  refine WP.aluImm rkr_at_4a ?_; wn
  refine WP.aluImm rkr_at_4e ?_; wn
  refine WP.aluImm rkr_at_50 ?_; wn
  refine rkh_field (off := 0x52) (o := 0x18) (p := P) (n := N) (kq := TRK_ROLES) (kl := 5)
    (key := ascii!"roles") E hO rkr_at_52 rkr_at_56 (by decide) (by decide) (by rsimp; exact hsp)
    (by rsimp; rw [hsp, ev_add]; rfl) (by rsimp; exact ha1) (by rsimp; exact ha2) (by rsimp; try rfl)
    (by rsimp; try rfl) (by decide) (by decide) (by decide) hP0 hPN E.hSP
    (tuf_sep_ro (E.hro.sub (by decide)) (by decide) (by decide)) (E.code hO).mRoles fun m2 Mb hO2 hOb hR => ?_
  rcases hof1 : objField (memBytes M0 P N) (ascii!"roles") with e | ⟨rp, rl⟩ <;> rw [hof1] at hR <;>
    simp only [fieldRes, Except.map, FieldRes] at hR
  · have hm : rkModel (memBytes M0 P N) (memBytes M0 RP RN) = .error e := by unfold rkModel; rw [hof1]
    rw [hm]
    obtain ⟨-, r1, r2⟩ := hR
    rw [rkh_e1c] at r2
    rw [show F + BitVec.ofNat 32 0x18 = F + 0x18 from rfl] at r1
    refine WP.lw rkr_at_5a (by rsimp; rw [hsp]; exact E.alF (c := 0x18) (by decide)) ?_; wn
    refine WP.branch rkr_at_5c (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact rk_8de E hO2 (by rsimp; rw [ev0]; exact ha0) (by rsimp; exact hsp) r2 (by keepz E.hz0)
    · exfalso; (try rsimp at eb); rw [hsp] at eb; rw [r1] at eb; exact absurd eb (by decide)
  obtain ⟨-, r1, r2⟩ := hR
  rw [rkh_e1c] at r2
  rw [show F + BitVec.ofNat 32 0x18 = F + 0x18 from rfl] at r1
  have hv := objField_val hof1
  rw [memBytes_length] at hv
  obtain ⟨hrp, hrpl⟩ := hv
  have hrpN : (P + BitVec.ofNat 32 rp).toNat = P.toNat + rp := tex_toNat (by omega)
  have hsl1 : memBytes M0 (P + BitVec.ofNat 32 rp) rl = slice (memBytes M0 P N) rp rl :=
    (tuf_memBytes_drop_take hrpl).symm
  refine WP.lw rkr_at_5a (by rsimp; rw [hsp]; exact E.alF (c := 0x18) (by decide)) ?_; wn
  refine WP.branch rkr_at_5c (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hsp, r1, nx_q0 hP0 (by omega) hrp] at eb; exact absurd eb (by decide)
  refine WP.lw rkr_at_60 (by rsimp; rw [hsp]; exact E.alF (c := 0x1C) (by decide)) ?_; wn
  refine WP.aluImm rkr_at_62 ?_; wn
  refine WP.alu rkr_at_66 ?_; wn
  refine WP.alu rkr_at_68 ?_; wn
  refine rkh_field (off := 0x6A) (o := 0x75C) (p := P + BitVec.ofNat 32 rp) (n := rl) (kq := RP) (kl := RN)
    (key := memBytes M0 RP RN) E hO2 rkr_at_6a rkr_at_6e (by decide) (by decide) (by rsimp; exact hsp)
    (by rsimp; rw [hsp, ev_add]; rfl) (by rsimp; rw [hsp, r1]) (by rsimp; rw [hsp, r2]) (by rsimp; rw [ev0, ev0]; exact ha3)
    (by rsimp; rw [show x0 = (0 : Fin 32) from rfl, hz, ev0, ev0]; exact ha4) (by decide) (by decide) hRN (by rw [hrpN]; omega) (by rw [hrpN]; omega)
    (E.hSP.subR (by omega)) (hRS.sub (by decide)) (E.bytes hO2 hRS) fun m3 Mc hO3 hOc hR3 => ?_
  rw [hsl1] at hR3
  have hQb : Out Mc m3.mem (F + BitVec.ofNat 32 0x75C) 8 := by
    rcases hr : fieldRes (P + BitVec.ofNat 32 rp) (objField (slice (memBytes M0 P N) rp rl) (memBytes M0 RP RN))
      with _ | ⟨_, _⟩ <;> rw [hr] at hR3 <;> exact hR3.1
  rcases hof2 : objField (slice (memBytes M0 P N) rp rl) (memBytes M0 RP RN) with e | ⟨qp, ql⟩ <;>
    rw [hof2] at hR3 <;> simp only [fieldRes, Except.map, FieldRes] at hR3
  · have hm : rkModel (memBytes M0 P N) (memBytes M0 RP RN) = .error e := by
      simp only [rkModel, hof1, hof2]
    rw [hm]
    obtain ⟨-, r1, r2⟩ := hR3
    rw [rkh_e760] at r2
    rw [show F + BitVec.ofNat 32 0x75C = F + 0x75C from rfl] at r1
    refine WP.lw rkr_at_72 (by rsimp; rw [hsp]; exact E.alF (c := 0x75C) (by decide)) ?_; wn
    refine WP.branch rkr_at_76 (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact rk_8e4 E hO3 (by rsimp; rw [ev0]; exact ha0) (by rsimp; exact hsp) r2 (by keepz E.hz0)
    · exfalso; (try rsimp at eb); rw [hsp] at eb; rw [r1] at eb; exact absurd eb (by decide)
  obtain ⟨-, r1, r2⟩ := hR3
  rw [rkh_e760] at r2
  rw [show F + BitVec.ofNat 32 0x75C = F + 0x75C from rfl] at r1
  have hv := objField_val hof2
  rw [← hsl1, memBytes_length] at hv
  obtain ⟨hqp, hqpl⟩ := hv
  have hqpN : (P + BitVec.ofNat 32 rp + BitVec.ofNat 32 qp).toNat = P.toNat + rp + qp := by
    rw [tex_toNat (by omega), hrpN]
  have hsl2 : memBytes M0 (P + BitVec.ofNat 32 rp + BitVec.ofNat 32 qp) ql =
      slice (slice (memBytes M0 P N) rp rl) qp ql := by
    rw [← hsl1]; exact (tuf_memBytes_drop_take hqpl).symm
  refine WP.lw rkr_at_72 (by rsimp; rw [hsp]; exact E.alF (c := 0x75C) (by decide)) ?_; wn
  refine WP.branch rkr_at_76 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hsp, r1, nx_q0 (by omega) (by omega) hqp] at eb; exact absurd eb (by decide)
  refine WP.lw rkr_at_7a (by rsimp; rw [hsp]; exact E.alF (c := 0x760) (by decide)) ?_; wn
  refine WP.lui rkr_at_7e ?_; wn
  refine WP.aluImm rkr_at_82 ?_; wn
  refine WP.aluImm rkr_at_86 ?_; wn
  refine WP.aluImm rkr_at_8a ?_; wn
  refine WP.alu rkr_at_8c ?_; wn
  refine WP.alu rkr_at_8e ?_; wn
  refine rkh_field (off := 0x90) (o := 0x75C) (p := P + BitVec.ofNat 32 rp + BitVec.ofNat 32 qp) (n := ql)
    (kq := TRK_THR) (kl := 9) (key := ascii!"threshold") E hO3 rkr_at_90 rkr_at_94 (by decide) (by decide)
    (by rsimp; exact hsp) (by rsimp; rw [hsp, ev_add]; rfl) (by rsimp; rw [ev0, hsp, r1])
    (by rsimp; rw [ev0, hsp, r2]) (by rsimp; try rfl) (by rsimp; try rfl) (by decide) (by decide) (by decide)
    (by rw [hqpN]; omega) (by rw [hqpN]; omega) ((E.hSP.subR (by omega)).subR (by omega))
    (tuf_sep_ro (E.hro.sub (by decide)) (by decide) (by decide)) (E.code hO3).mThr fun m4 Md hO4 hOd hR4 => ?_
  rw [hsl2] at hR4
  have hTb : Out Md m4.mem (F + BitVec.ofNat 32 0x75C) 8 := by
    rcases hr : fieldRes (P + BitVec.ofNat 32 rp + BitVec.ofNat 32 qp)
        (objField (slice (slice (memBytes M0 P N) rp rl) qp ql) (ascii!"threshold")) with _ | ⟨_, _⟩ <;>
      rw [hr] at hR4 <;> exact hR4.1
  rcases hof3 : objField (slice (slice (memBytes M0 P N) rp rl) qp ql) (ascii!"threshold") with e | ⟨tp, tl⟩ <;>
    rw [hof3] at hR4 <;> simp only [fieldRes, Except.map, FieldRes] at hR4
  · have hm : rkModel (memBytes M0 P N) (memBytes M0 RP RN) = .error e := by
      simp only [rkModel, hof1, hof2, hof3]
    rw [hm]
    obtain ⟨-, t1, t2⟩ := hR4
    rw [rkh_e760] at t2
    rw [show F + BitVec.ofNat 32 0x75C = F + 0x75C from rfl] at t1
    refine WP.lw rkr_at_98 (by rsimp; rw [hsp]; exact E.alF (c := 0x75C) (by decide)) ?_; wn
    refine WP.branch rkr_at_9c (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact rk_8e4 E hO4 (by rsimp; rw [ev0]; exact ha0) (by rsimp; exact hsp) t2 (by keepz E.hz0)
    · exfalso; (try rsimp at eb); rw [hsp] at eb; rw [t1] at eb; exact absurd eb (by decide)
  obtain ⟨-, t1, t2⟩ := hR4
  rw [rkh_e760] at t2
  rw [show F + BitVec.ofNat 32 0x75C = F + 0x75C from rfl] at t1
  have hv := objField_val hof3
  rw [← hsl2, memBytes_length] at hv
  obtain ⟨htp, htpl⟩ := hv
  have htpN : (P + BitVec.ofNat 32 rp + BitVec.ofNat 32 qp + BitVec.ofNat 32 tp).toNat = P.toNat + rp + qp + tp := by
    rw [tex_toNat (by omega), hqpN]
  have hsl3 : memBytes M0 (P + BitVec.ofNat 32 rp + BitVec.ofNat 32 qp + BitVec.ofNat 32 tp) tl =
      slice (slice (slice (memBytes M0 P N) rp rl) qp ql) tp tl := by
    rw [← hsl2]; exact (tuf_memBytes_drop_take htpl).symm
  refine WP.lw rkr_at_98 (by rsimp; rw [hsp]; exact E.alF (c := 0x75C) (by decide)) ?_; wn
  refine WP.branch rkr_at_9c (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hsp, t1, nx_q0 (by omega) (by omega) htp] at eb; exact absurd eb (by decide)
  refine WP.lw rkr_at_a0 (by rsimp; rw [hsp]; exact E.alF (c := 0x760) (by decide)) ?_; wn
  refine WP.aluImm rkr_at_a4 ?_; wn
  refine rkh_u64 (off := 0xA6) (p := P + BitVec.ofNat 32 rp + BitVec.ofNat 32 qp + BitVec.ofNat 32 tp) (n := tl)
    E hO4 rkr_at_a6 rkr_at_aa (by decide) (by decide) (by rsimp; exact hsp) (by rsimp; rw [hsp, ev_add]; rfl)
    (by rsimp; rw [hsp, t1]) (by rsimp; rw [hsp, t2]) (by omega)
    (((E.hSP.subR (by omega)).subR (by omega)).subR (by omega)) fun m5 Mg hO5 hOg hU => ?_
  rw [hsl3] at hU
  rcases hu : u64Val (slice (slice (slice (memBytes M0 P N) rp rl) qp ql) tp tl) with _ | v <;> rw [hu] at hU <;>
    simp only [U64Res] at hU
  · have hm : rkModel (memBytes M0 P N) (memBytes M0 RP RN) = .error 0x21 := by
      simp only [rkModel, hof1, hof2, hof3, hu]
    rw [hm]
    obtain ⟨-, u1, u2⟩ := hU
    rw [rkh_e19] at u2
    rw [show F + BitVec.ofNat 32 0x18 = F + 0x18 from rfl] at u1
    refine WP.lbu rkr_at_ae ?_; wn
    refine WP.branch rkr_at_b2 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hsp] at eb; rw [u1] at eb; exact absurd eb (by decide)
    refine WP.lbu rkr_at_b4 ?_; wn
    refine WP.jal rkr_at_b8 (by decide) ?_; wn
    exact rk_8e8 E hO5 (by rsimp; rw [ev0]; exact ha0) (by rsimp; exact hsp)
      (by rsimp; rw [hsp, tlv_zext]; exact u2) (by rsimp) (by keepz E.hz0)
  obtain ⟨-, u1, u2⟩ := hU
  rw [rkh_e20, rkh_e24] at u2
  rw [show F + BitVec.ofNat 32 0x18 = F + 0x18 from rfl] at u1
  refine WP.lbu rkr_at_ae ?_; wn
  refine WP.branch rkr_at_b2 (fun _ => ?_) (fun eb => ?_) <;> wn
  rotate_left
  · exfalso; (try rsimp at eb); rw [hsp] at eb; rw [u1] at eb; exact absurd eb (by decide)
  refine WP.lw rkr_at_bc (by rsimp; rw [hsp]; exact E.alF (c := 0x20) (by decide)) ?_; wn
  refine WP.lw rkr_at_be (by rsimp; rw [hsp]; exact E.alF (c := 0x24) (by decide)) ?_; wn
  refine WP.alu rkr_at_c0 ?_; wn
  refine WP.branch rkr_at_c4 (fun eb => ?_) (fun eb => ?_) <;> wn
  · have hv0 : v = 0 := by
      (try rsimp at eb); (try simp only [tpr_or] at eb); rw [hsp] at eb
      exact (rkh_thr0 u2).mp (rkh_bt eb)
    have hm : rkModel (memBytes M0 P N) (memBytes M0 RP RN) = .error 0x21 := by
      simp only [rkModel, hof1, hof2, hof3, hu]; rw [if_pos hv0]
    rw [hm]
    exact rk_930 E hO5 (by rsimp; rw [ev0]; exact ha0) (by rsimp; exact hsp) (by keepz E.hz0)
  have hv0 : ¬v = 0 := by
    (try rsimp at eb); (try simp only [tpr_or] at eb); rw [hsp] at eb
    exact fun h => rkh_bf eb ((rkh_thr0 u2).mpr h)
  refine WP.lui rkr_at_c8 ?_; wn
  refine WP.aluImm rkr_at_cc ?_; wn
  refine WP.aluImm rkr_at_d0 ?_; wn
  refine WP.aluImm rkr_at_d2 ?_; wn
  refine WP.alu rkr_at_d4 ?_; wn
  refine WP.alu rkr_at_d6 ?_; wn
  refine rkh_field (off := 0xD8) (o := 0x18) (p := P) (n := N) (kq := TRK_KEYS) (kl := 4)
    (key := ascii!"keys") E hO5 rkr_at_d8 rkr_at_dc (by decide) (by decide) (by rsimp; exact hsp)
    (by rsimp; rw [hsp, ev_add]; rfl) (by rsimp; (try simp only [ev0]); exact ha1)
    (by rsimp; (try simp only [ev0]); exact ha2) (by rsimp; try rfl) (by rsimp; try rfl) (by decide) (by decide)
    (by decide) hP0 hPN E.hSP (tuf_sep_ro (E.hro.sub (by decide)) (by decide) (by decide)) (E.code hO5).mKeys
    fun m6 Mh hO6 hOh hR6 => ?_
  rcases hof4 : objField (memBytes M0 P N) (ascii!"keys") with e | ⟨kp, kl⟩ <;> rw [hof4] at hR6 <;>
    simp only [fieldRes, Except.map, FieldRes] at hR6
  · have hm : rkModel (memBytes M0 P N) (memBytes M0 RP RN) = .error e := by
      simp only [rkModel, hof1, hof2, hof3, hu]; rw [if_neg hv0]; simp only [hof4]
    rw [hm]
    obtain ⟨-, k1, k2⟩ := hR6
    rw [rkh_e1c] at k2
    rw [show F + BitVec.ofNat 32 0x18 = F + 0x18 from rfl] at k1
    refine WP.lw rkr_at_e0 (by rsimp; rw [hsp]; exact E.alF (c := 0x18) (by decide)) ?_; wn
    refine WP.branch rkr_at_e2 (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact rk_8de E hO6 (by rsimp; rw [ev0]; exact ha0) (by rsimp; exact hsp) k2 (by keepz E.hz0)
    · exfalso; (try rsimp at eb); rw [hsp] at eb; rw [k1] at eb; exact absurd eb (by decide)
  obtain ⟨-, k1, k2⟩ := hR6
  rw [rkh_e1c] at k2
  rw [show F + BitVec.ofNat 32 0x18 = F + 0x18 from rfl] at k1
  have hv := objField_val hof4
  rw [memBytes_length] at hv
  obtain ⟨hkp, hkpl⟩ := hv
  have hkpN : (P + BitVec.ofNat 32 kp).toNat = P.toNat + kp := tex_toNat (by omega)
  have hsl4 : memBytes M0 (P + BitVec.ofNat 32 kp) kl = slice (memBytes M0 P N) kp kl :=
    (tuf_memBytes_drop_take hkpl).symm
  have hm0 : rkModel (memBytes M0 P N) (memBytes M0 RP RN) =
      match rkRole (memBytes M0 (P + BitVec.ofNat 32 rp + BitVec.ofNat 32 qp) ql)
          (memBytes M0 (P + BitVec.ofNat 32 kp) kl) with
      | .error e => .error e
      | .ok es => .ok (v, es) := by
    simp only [rkModel, hof1, hof2, hof3, hu]; rw [if_neg hv0]; simp only [hof4]; rw [hsl2, hsl4]
    rcases rkRole (slice (slice (memBytes M0 P N) rp rl) qp ql) (slice (memBytes M0 P N) kp kl) with _ | _ <;> rfl
  refine WP.lw rkr_at_e0 (by rsimp; rw [hsp]; exact E.alF (c := 0x18) (by decide)) ?_; wn
  refine WP.branch rkr_at_e2 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hsp, k1, nx_q0 hP0 (by omega) hkp] at eb; exact absurd eb (by decide)
  refine WP.lw rkr_at_e6 (by rsimp; rw [hsp]; exact E.alF (c := 0x1C) (by decide)) ?_; wn
  refine WP.aluImm rkr_at_e8 ?_; wn
  refine WP.alu rkr_at_ea ?_; wn
  refine WP.alu rkr_at_ec ?_; wn
  refine rkh_mem (off := 0xEE) (p := P + BitVec.ofNat 32 kp) (n := kl) E hO6 rkr_at_ee rkr_at_f2 (by decide)
    (by decide) (by rsimp; exact hsp) (by rsimp; rw [hsp, ev_add]; rfl) (by rsimp; rw [ev0, hsp, k1])
    (by rsimp; rw [ev0, hsp, k2]) (by omega) (E.hSP.subR (by omega)) fun m7 Mi hO7 hOi hC => ?_
  rw [show F + BitVec.ofNat 32 0x18 = F + 0x18 from rfl] at hC
  by_cases hkv : (memBytes M0 (P + BitVec.ofNat 32 kp) kl).length = 0 ∨
      (memBytes M0 (P + BitVec.ofNat 32 kp) kl).getD 0 0 ≠ 123
  · have hco : curOpen 123 (P + BitVec.ofNat 32 kp) (memBytes M0 (P + BitVec.ofNat 32 kp) kl) = none := by
      unfold curOpen
      rcases hkv with h | h
      · rw [if_pos h]
      · by_cases h0 : (memBytes M0 (P + BitVec.ofNat 32 kp) kl).length = 0
        · rw [if_pos h0]
        · rw [if_neg h0, if_pos h]
    have hm : rkModel (memBytes M0 P N) (memBytes M0 RP RN) = .error 0x21 := by
      rw [hm0]; unfold rkRole; rw [if_pos hkv]
    rw [hm]; rw [hco] at hC
    obtain ⟨-, c1, c2⟩ := hC
    rw [show F + 0x18 + 4 = F + 0x1C by rw [BitVec.add_assoc]; rfl] at c2
    refine WP.lw rkr_at_f6 (by rsimp; rw [hsp]; exact E.alF (c := 0x18) (by decide)) ?_; wn
    refine WP.branch rkr_at_f8 (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact rk_8de E hO7 (by rsimp; rw [ev0]; exact ha0) (by rsimp; exact hsp) c2 (by keepz E.hz0)
    · exfalso; (try rsimp at eb); rw [hsp] at eb; rw [c1] at eb; exact absurd eb (by decide)
  have hco : curOpen 123 (P + BitVec.ofNat 32 kp) (memBytes M0 (P + BitVec.ofNat 32 kp) kl) =
      some (P + BitVec.ofNat 32 kp, (memBytes M0 (P + BitVec.ofNat 32 kp) kl).length,
        skipWs (memBytes M0 (P + BitVec.ofNat 32 kp) kl) 1) := by
    unfold curOpen
    have h0 : ¬(memBytes M0 (P + BitVec.ofNat 32 kp) kl).length = 0 := fun h => hkv (Or.inl h)
    have h1 : ¬(memBytes M0 (P + BitVec.ofNat 32 kp) kl).getD 0 0 ≠ 123 := fun h => hkv (Or.inr h)
    rw [if_neg h0, if_neg h1]
  have hm : rkModel (memBytes M0 P N) (memBytes M0 RP RN) =
      rkThen (rkKids (memBytes M0 (P + BitVec.ofNat 32 rp + BitVec.ofNat 32 qp) ql)
        (memBytes M0 (P + BitVec.ofNat 32 kp) kl)) v [] := by
    rw [hm0, rkh_role hkv]
    rcases rkKids (memBytes M0 (P + BitVec.ofNat 32 rp + BitVec.ofNat 32 qp) ql)
      (memBytes M0 (P + BitVec.ofNat 32 kp) kl) with _ | _ <;> rfl
  rw [hm]; rw [hco] at hC
  obtain ⟨-, c1, -, -⟩ := hC
  refine WP.lw rkr_at_f6 (by rsimp; rw [hsp]; exact E.alF (c := 0x18) (by decide)) ?_; wn
  refine WP.branch rkr_at_f8 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hsp, c1, nx_q0 hP0 (by omega) hkp] at eb; exact absurd eb (by decide)
  refine rkh_keep g0 (by keepz E.hz0) fun hS => ?_
  refine rkh_init E (lo := memLoad32 m5.mem (F + 0x20)) (hi := memLoad32 m5.mem (F + 0x24)) (by rsimp)
    (by rsimp; exact hsp) (by rsimp) (by rsimp; rw [hsp]) (by rsimp; rw [hsp]) (fun _ _ => rfl) hO7
    fun M' g' hsp' hz' h19 h20 hfr' hO' hB' => ?_
  rw [u2] at hB'
  exact rkh_ids E hO' hB' hsp' hz' ((hfr' 27 (by decide)).trans (by rsimp; rw [ev0]; exact ha0))
    ((hfr' 23 (by decide)).trans (by rsimp; rw [hsp, r1])) ((hfr' 22 (by decide)).trans (by rsimp; rw [hsp, r2]))
    ((hfr' 21 (by decide)).trans (by rsimp; rw [hsp, k1])) ((hfr' 18 (by decide)).trans (by rsimp; rw [hsp, k2]))
    h19 h20 (fun x hx => (hfr' x (rkh_sub2 x hx)).trans (hS x hx)) (by rw [hqpN]; omega) (by rw [hqpN]; omega)
    ((E.hSP.subR (by omega)).subR (by omega)) (by rw [hkpN]; omega) (by rw [hkpN]; omega) (E.hSP.subR (by omega))

end

end C3.RV32
