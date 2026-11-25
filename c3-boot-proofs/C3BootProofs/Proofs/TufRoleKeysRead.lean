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

end

end C3.RV32
