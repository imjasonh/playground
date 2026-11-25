import C3BootProofs.Proofs.TufRoleKeysMetLookup
import C3BootProofs.Proofs.TufRoleKeysMetCmp
import C3BootProofs.Proofs.TufRoleKeysKey

/-!
# `RoleKeys::met`: the duplicate-key loop

Before it checks the signature of slot `i`, `met` compares the key of slot
`i` with the key of each slot it already counted, from 0x17E to 0x20A. The
counted slots are words at `F + 0x28`, and `[F + 0x1C]` is four times their
count. A key that matches skips slot `i` (0x2C0); otherwise the loop ends at
0x20A, and no counted slot holds the same key.

The key of a slot is a tag byte, 0xFF for none, followed by its bytes. The
loop copies slot `i` to `F + 0x48`, then compares the tags, and for equal tags
the bytes: with `memcmp` for P-256 (65 bytes), `eq_arr97` for P-384, and
`arr32_eq` for Ed25519.
-/

namespace C3.Json

/-- The key of entry `j` of `es`, `none` past the end. -/
def rmKeyAt (es : List RkEntry) (j : Nat) : Option (Nat × Bytes) := (es.getD j ([], none)).2

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

/-- The registers that the duplicate-key loop keeps. -/
abbrev rmDL : List (Fin 32) := [sp, 18, 19, 20, 22, 23, 24, 25, 26, 27]

/-- `rmDL` and the loop's own pointer and counter, `s0` and `s1`. -/
abbrev rmDK : List (Fin 32) := [sp, 8, 9, 18, 19, 20, 22, 23, 24, 25, 26, 27]

theorem rm_wfAt {es : List RkEntry} (hw : RkWf es) {j : Nat} {k : Nat × Bytes} (h : rmKeyAt es j = some k) :
    (k.1 = 0 ∧ k.2.length = 65) ∨ (k.1 = 1 ∧ k.2.length = 97) ∨ (k.1 = 2 ∧ k.2.length = 32) := by
  unfold rmKeyAt at h
  rw [List.getD_eq_getElem?_getD] at h
  rcases hj : es[j]? with _ | e
  · rw [hj] at h; cases h
  · rw [hj] at h
    exact hw e (List.mem_of_getElem? hj) k h

theorem rm_nbPre {M : Word → BitVec 8} {q : Word} {k : Bytes}
    (h : ∀ j < k.length, M (q + BitVec.ofNat 32 j) = BitVec.ofNat 8 (k.getD j 0)) :
    memBytes M q k.length = nb k := by
  have hl : (nb k).length = k.length := List.length_map _
  rw [← hl]
  refine RkPre.eq (fun j hj => ?_) rfl fun x hx => ?_
  · rw [hl] at hj
    rw [h j hj]
    show BitVec.ofNat 8 (k.getD j 0) = BitVec.ofNat 8 ((k.map (· % 256)).getD j 0)
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases k[j]? with _ | y
    · rfl
    show BitVec.ofNat 8 y = BitVec.ofNat 8 (y % 256)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
    exact Nat.mod_lt _ (by decide)

/-- The tag byte of slot `j` and, for a key, its bytes. -/
theorem rm_slotKey {M0 : Word → BitVec 8} {R : Word} {t : Nat} {es : List RkEntry} (hR : RkAt M0 R t es)
    {j : Nat} (hj8 : j < 8) :
    (rmKeyAt es j = none ∧ M0 (R + BitVec.ofNat 32 (98 * j)) = 0xFF) ∨
      ∃ tj kj, rmKeyAt es j = some (tj, kj) ∧ M0 (R + BitVec.ofNat 32 (98 * j)) = BitVec.ofNat 8 tj ∧
        memBytes M0 (R + BitVec.ofNat 32 (98 * j + 1)) kj.length = nb kj := by
  have hs := (hR.2.2.2 j hj8).2.2.2
  unfold rmKeyAt
  rcases he : (es.getD j ([], none)).2 with _ | ⟨tj, kj⟩ <;> rw [he] at hs
  · exact Or.inl ⟨rfl, hs⟩
  · obtain ⟨h0, -, hb⟩ := hs
    refine Or.inr ⟨tj, kj, rfl, h0, rm_nbPre fun jj hjj => ?_⟩
    rw [add_ofNat_assoc]
    exact hb jj hjj

theorem rm_mul98 : ∀ j < 8, aluEval .mul (BitVec.ofNat 32 j) 0x62 = BitVec.ofNat 32 (98 * j) := by decide

theorem rm_dec4 (r : Nat) :
    aluEval .add (BitVec.ofNat 32 (4 * (r + 1))) 0xFFFFFFFC = BitVec.ofNat 32 (4 * r) := by
  rw [ev_add, show (0xFFFFFFFC : Word) = BitVec.ofNat 32 (2 ^ 32 - 4) from rfl, BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

section
variable {Q : Post} {M : Word → BitVec 8} {g0 : Fin 32 → Word}

/-- The tag comparison from 0x1AC: `a1` holds the tag of slot `j` and `a2`
that of slot `i`. -/
theorem rm_tags {g : Fin 32 → Word} {B T : BitVec 8} (hB : B = 0xFF ∨ B = 0 ∨ B = 1 ∨ B = 2)
    (hT : T = 0 ∨ T = 1 ∨ T = 2) (h11 : g 11 = B.zeroExtend 32) (h12 : g 12 = T.zeroExtend 32)
    (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ rkE → g x = g0 x)
    (hn : B ≠ T → ∀ g' : Fin 32 → Word, (∀ x, x ∈ rmDK → g' x = g x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → WP tufRoleKeysMetCode TRM Q M 0x1DE g')
    (h0 : B = 0 → T = 0 → ∀ g' : Fin 32 → Word, (∀ x, x ∈ rmDK → g' x = g x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → g' 10 = aluEval .add (g 10) 1 → WP tufRoleKeysMetCode TRM Q M 0x1E6 g')
    (h1 : B = 1 → T = 1 → ∀ g' : Fin 32 → Word, (∀ x, x ∈ rmDK → g' x = g x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → g' 10 = aluEval .add (g 10) 1 → WP tufRoleKeysMetCode TRM Q M 0x1C6 g')
    (h2 : B = 2 → T = 2 → ∀ g' : Fin 32 → Word, (∀ x, x ∈ rmDK → g' x = g x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → g' 10 = aluEval .add (g 10) 1 → WP tufRoleKeysMetCode TRM Q M 0x1FA g') :
    WP tufRoleKeysMetCode TRM Q M 0x1AC g := by
  have hE := fun x (hx : x ∈ rmDK) => (rfl : g x = g x)
  refine WP.zero fun hz' => ?_
  refine WP.aluImm rkm_at_1ac ?_; wn
  rcases hB with rfl | hB'
  · rcases hT with rfl | rfl | rfl
    all_goals
      refine WP.branch rkm_at_1b0 (fun eb => ?_) (fun eb => ?_) <;> wn
      all_goals (try (exfalso; (try rsimp at eb); (try simp only [h11, h12] at eb); all_goals exact absurd eb (by decide)))
      refine WP.alu rkm_at_1d6 ?_; wn
      refine WP.aluImm rkm_at_1d8 ?_; wn
      refine WP.branch rkm_at_1dc (fun eb => ?_) (fun eb => ?_) <;> wn
      all_goals (try (exfalso; (try rsimp at eb); (try simp only [h11, h12] at eb); all_goals exact absurd eb (by decide)))
      exact hn (by decide) _ (by rmkeep hE) (by rsimp) (by keepz hz0)
  by_cases hBT : B = T
  · subst hBT
    rcases hT with rfl | rfl | rfl
    all_goals
      refine WP.branch rkm_at_1b0 (fun eb => ?_) (fun eb => ?_) <;> wn
      all_goals (try (exfalso; (try rsimp at eb); (try simp only [h11, h12] at eb); all_goals exact absurd eb (by decide)))
      refine WP.aluImm rkm_at_1b2 ?_; wn
      refine WP.branch rkm_at_1b6 (fun eb => ?_) (fun eb => ?_) <;> wn
      all_goals (try (exfalso; (try rsimp at eb); (try simp only [h11, h12] at eb); all_goals exact absurd eb (by decide)))
      refine WP.branch rkm_at_1b8 (fun eb => ?_) (fun eb => ?_) <;> wn
      all_goals (try (exfalso; (try rsimp at eb); (try simp only [h11, h12] at eb); all_goals exact absurd eb (by decide)))
      refine WP.aluImm rkm_at_1bc ?_; wn
      refine WP.branch rkm_at_1be (fun eb => ?_) (fun eb => ?_) <;> wn
      all_goals (try (exfalso; (try rsimp at eb); (try simp only [h11, h12] at eb); all_goals exact absurd eb (by decide)))
    · exact h0 rfl rfl _ (by rmkeep hE) (by rsimp) (by keepz hz0) (by rsimp)
    all_goals
      refine WP.aluImm rkm_at_1c0 ?_; wn
      refine WP.branch rkm_at_1c2 (fun eb => ?_) (fun eb => ?_) <;> wn
      all_goals (try (exfalso; (try rsimp at eb); (try simp only [h11, h12] at eb); all_goals exact absurd eb (by decide)))
    · exact h1 rfl rfl _ (by rmkeep hE) (by rsimp) (by keepz hz0) (by rsimp)
    · exact h2 rfl rfl _ (by rmkeep hE) (by rsimp) (by keepz hz0) (by rsimp)
  rcases hB' with rfl | rfl | rfl <;> rcases hT with rfl | rfl | rfl
  all_goals (try exact absurd rfl hBT)
  all_goals
    refine WP.branch rkm_at_1b0 (fun eb => ?_) (fun eb => ?_) <;> wn
    all_goals (try (exfalso; (try rsimp at eb); (try simp only [h11, h12] at eb); all_goals exact absurd eb (by decide)))
    refine WP.aluImm rkm_at_1b2 ?_; wn
    refine WP.branch rkm_at_1b6 (fun eb => ?_) (fun eb => ?_) <;> wn
    all_goals (try (exfalso; (try rsimp at eb); (try simp only [h11, h12] at eb); all_goals exact absurd eb (by decide)))
    refine WP.branch rkm_at_1b8 (fun eb => ?_) (fun eb => ?_) <;> wn
    all_goals (try (exfalso; (try rsimp at eb); (try simp only [h11, h12] at eb); all_goals exact absurd eb (by decide)))
    exact hn hBT _ (by rmkeep hE) (by rsimp) (by keepz hz0)

end

section
variable {M0 M1 : Word → BitVec 8} {s F R MP SP : Word} {ML SL : Nat} {g0 : Fin 32 → Word} {Q : Post}

theorem rm_beqT {a : Word} (h : branchTaken .beq a 0 = true) : a = 0 := by simpa [branchTaken] using h

theorem rm_beqF {a : Word} (h : branchTaken .beq a 0 = false) : a ≠ 0 := fun e => by
  rw [e] at h; exact absurd h (by decide)

theorem rm_bneT {a : Word} (h : branchTaken .bne a 0 = true) : a ≠ 0 := fun e => by
  rw [e] at h; exact absurd h (by decide)

theorem rm_bneF {a : Word} (h : branchTaken .bne a 0 = false) : a = 0 := by
  simpa [branchTaken] using h

/-- What the key comparisons leave: memory changed at most in the 16 bytes
below `F`, and the registers of `rmDK` kept. -/
abbrev RmCK (M M' : Word → BitVec 8) (F : Word) (g g' : Fin 32 → Word) (g0 : Fin 32 → Word) : Prop :=
  Out M M' (F + 0xFFFFFFF0) 16 ∧ (∀ x, x ∈ rmDK → g' x = g x) ∧ g' 0 = 0 ∧ ∀ x, x ∉ rkE → g' x = g0 x

/-- The P-256 comparison from 0x1E6: `memcmp` of the 65 bytes at `A` and at
`F + 0x49`. -/
theorem rm_c0 (E : RmBase M0 M1 s F R MP SP ML SL g0) {M : Word → BitVec 8} (hc : RmCodeA M) {g : Fin 32 → Word}
    {A : Word} (hsp : g sp = F) (h10 : g 10 = A) (hz : g 0 = 0) (hfr : ∀ x, x ∉ rkE → g x = g0 x)
    (hsk : ∀ M' g', RmCK M M' F g g' g0 → WP tufRoleKeysMetCode TRM Q M' 0x2C0 g')
    (hnx : memBytes M A 65 ≠ memBytes M (F + BitVec.ofNat 32 0x49) 65 →
      ∀ M' g', RmCK M M' F g g' g0 → WP tufRoleKeysMetCode TRM Q M' 0x1DE g') :
    WP tufRoleKeysMetCode TRM Q M 0x1E6 g := by
  have hE := fun x (_ : x ∈ rmDK) => (rfl : g x = g x)
  have hO : Out M M (F + 0xFFFFFFF0) 16 := fun _ _ => rfl
  refine WP.aluImm rkm_at_1e6 ?_; wn
  refine WP.aluImm rkm_at_1ea ?_; wn
  refine WP.callMemcmpIff (tb := BitVec.ofNat 32 eqArr97Address + 0xC04C) (p := A) (q := F + BitVec.ofNat 32 0x49)
    (n := 0x41) rkm_at_1ee rkm_at_1f2 (by decide) (by decide) (by decide) hc.eq97m (by (try rsimp); exact h10)
    (by (try rsimp); rw [ev_add, hsp]; rfl) (by (try rsimp); rw [hz, ev0]; rfl) (by decide) fun m2 hiff hm2 => ?_
  rw [hm2]
  refine WP.branch rkm_at_1f6 (fun eb => ?_) (fun eb => ?_) <;> wn
  · exact hsk M _ ⟨hO, by rmkeep hE, by rsimp, by keepz E.hz0⟩
  · refine WP.jal rkm_at_1f8 (by decide) ?_; wn
    (try rsimp at eb)
    exact hnx (fun h => rm_beqF eb (hiff.mpr h)) M _ ⟨hO, by rmkeep hE, by rsimp, by keepz E.hz0⟩


/-- The P-384 comparison from 0x1C6: `eq_arr97` of the bytes at `A` and at
`F + 0x49`. -/
theorem rm_c1 (E : RmBase M0 M1 s F R MP SP ML SL g0) {M : Word → BitVec 8} (hc : RmCodeA M) {g : Fin 32 → Word}
    {d : Nat} (hd : d + 97 ≤ 0x540) (hsp : g sp = F) (h10 : g 10 = R + BitVec.ofNat 32 d)
    (hfr : ∀ x, x ∉ rkE → g x = g0 x)
    (hsk : ∀ M' g', RmCK M M' F g g' g0 → WP tufRoleKeysMetCode TRM Q M' 0x2C0 g')
    (hnx : memBytes M (R + BitVec.ofNat 32 d) 97 ≠ memBytes M (F + BitVec.ofNat 32 0x49) 97 →
      ∀ M' g', RmCK M M' F g g' g0 → WP tufRoleKeysMetCode TRM Q M' 0x1DE g') :
    WP tufRoleKeysMetCode TRM Q M 0x1C6 g := by
  have hE := fun x (_ : x ∈ rmDK) => (rfl : g x = g x)
  have hF4 : F.toNat % 4 = 0 := by have := E.halF; omega
  have hw : F + 0xFFFFFFF0 = s + BitVec.ofNat 32 0x3720 := E.Fm (c := 16) (by decide) rfl
  refine WP.aluImm rkm_at_1c6 ?_; wn
  refine WP.callEq97 (p := R + BitVec.ofNat 32 d) (q := F + BitVec.ofNat 32 0x49) rkm_at_1ca rkm_at_1ce
    (by decide) (by decide) hc.eq97 hc.eq97m (by (try rsimp); exact h10) (by (try rsimp); rw [ev_add, hsp]; rfl)
    (by (try rsimp); rw [hsp]; exact hF4) (by (try rsimp); rw [hsp, hw]; exact E.lowS (by decide) (by decide) (by decide))
    (by (try rsimp); rw [hsp, hw]; exact E.lowS (by decide) (by decide) (by decide))
    (by (try rsimp); rw [hsp, hw]; exact E.rS hd (by decide))
    (by (try rsimp); rw [hsp, hw]; exact E.fs (Or.inr (by decide)) (by decide) (by decide))
    (by (try rsimp); rw [hsp, hw]; exact E.lowS (by decide) (by decide) (by decide)) fun m2 ha0 hO2 => ?_
  (try rsimp at hO2)
  rw [hsp] at hO2
  generalize m2.mem = M2 at hO2
  refine WP.branch rkm_at_1d2 (fun eb => ?_) (fun eb => ?_) <;> wn
  · exact hsk M2 _ ⟨hO2, by rmkeep hE, by rsimp, by keepz E.hz0⟩
  · refine WP.jal rkm_at_1d4 (by decide) ?_; wn
    (try rsimp at eb)
    have e0 := rm_bneF eb
    rw [ha0] at e0
    refine hnx (fun h => ?_) M2 _ ⟨hO2, by rmkeep hE, by rsimp, by keepz E.hz0⟩
    rw [ite_eq_left h] at e0
    exact absurd e0 (by decide)

/-- The Ed25519 comparison from 0x1FA: `arr32_eq` of the bytes at `A` and at
`F + 0x49`. -/
theorem rm_c2 (E : RmBase M0 M1 s F R MP SP ML SL g0) {M : Word → BitVec 8} (hc : RmCodeA M) {g : Fin 32 → Word}
    {d : Nat} (hd : d + 32 ≤ 0x540) (hsp : g sp = F) (h10 : g 10 = R + BitVec.ofNat 32 d)
    (hfr : ∀ x, x ∉ rkE → g x = g0 x)
    (hsk : ∀ M' g', RmCK M M' F g g' g0 → WP tufRoleKeysMetCode TRM Q M' 0x2C0 g')
    (hnx : memBytes M (R + BitVec.ofNat 32 d) 32 ≠ memBytes M (F + BitVec.ofNat 32 0x49) 32 →
      ∀ M' g', RmCK M M' F g g' g0 → WP tufRoleKeysMetCode TRM Q M' 0x1DE g') :
    WP tufRoleKeysMetCode TRM Q M 0x1FA g := by
  have hE := fun x (_ : x ∈ rmDK) => (rfl : g x = g x)
  have hF4 : F.toNat % 4 = 0 := by have := E.halF; omega
  have hw : F + 0xFFFFFFFC = s + BitVec.ofNat 32 0x372C := E.Fm (c := 4) (by decide) rfl
  refine WP.aluImm rkm_at_1fa ?_; wn
  refine WP.callArr32 (p := R + BitVec.ofNat 32 d) (q := F + BitVec.ofNat 32 0x49) rkm_at_1fe rkm_at_202
    (by decide) (by decide) hc.a32 hc.a32m (by (try rsimp); exact h10) (by (try rsimp); rw [ev_add, hsp]; rfl)
    (by (try rsimp); rw [hsp]; exact hF4) (by (try rsimp); rw [hsp, hw]; exact E.lowS (by decide) (by decide) (by decide))
    (by (try rsimp); rw [hsp, hw]; exact E.lowS (by decide) (by decide) (by decide))
    (by (try rsimp); rw [hsp, hw]; exact (E.rS hd (by decide)).symm)
    (by (try rsimp); rw [hsp, hw]; exact (E.fs (Or.inr (by decide)) (by decide) (by decide)).symm)
    (by (try rsimp); rw [hsp, hw]; exact E.lowS (by decide) (by decide) (by decide)) fun m2 ha0 hO2 => ?_
  (try rsimp at hO2)
  rw [hsp, show F + 0xFFFFFFFC = F + 0xFFFFFFF0 + BitVec.ofNat 32 12 by rw [BitVec.add_assoc]; rfl] at hO2
  have hO3 := hO2.widen (k := 16) (by decide)
  generalize m2.mem = M2 at hO3
  refine WP.branch rkm_at_206 (fun eb => ?_) (fun eb => ?_) <;> wn
  · exact hsk M2 _ ⟨hO3, by rmkeep hE, by rsimp, by keepz E.hz0⟩
  · refine WP.jal rkm_at_208 (by decide) ?_; wn
    (try rsimp at eb)
    have e0 := rm_bneF eb
    rw [ha0] at e0
    refine hnx (fun h => ?_) M2 _ ⟨hO3, by rmkeep hE, by rsimp, by keepz E.hz0⟩
    rw [ite_eq_left h] at e0
    exact absurd e0 (by decide)


end


theorem rm_mbx {M M' : Word → BitVec 8} {a b : Word} {n : Nat}
    (h : ∀ i, i < n → M' (a + BitVec.ofNat 32 i) = M (b + BitVec.ofNat 32 i)) : memBytes M' a n = memBytes M b n := by
  unfold memBytes
  exact List.map_congr_left fun i hi => congrArg BitVec.toNat (h i (List.mem_range.mp hi))

/-- Keys whose bytes in memory differ are different keys. -/
theorem rm_ne {M0 M2 : Word → BitVec 8} {R F : Word} {es : List RkEntry} {i j ti : Nat} {ki : Bytes}
    (hw : RkWf es) (hki : rmKeyAt es i = some (ti, ki))
    (hj : ∀ kj, rmKeyAt es j = some kj → memBytes M0 (R + BitVec.ofNat 32 (98 * j + 1)) kj.2.length = nb kj.2)
    (hi : memBytes M0 (R + BitVec.ofNat 32 (98 * i + 1)) ki.length = nb ki)
    (hR2 : ∀ d, d < 0x540 → M2 (R + BitVec.ofNat 32 d) = M0 (R + BitVec.ofNat 32 d))
    (hcp : ∀ c, c < 0x62 → M2 (F + BitVec.ofNat 32 (0x48 + c)) = M0 (R + BitVec.ofNat 32 (98 * i + c)))
    (hj8 : j < 8)
    (hdiff : memBytes M2 (R + BitVec.ofNat 32 (98 * j + 1)) ki.length ≠
      memBytes M2 (F + BitVec.ofNat 32 0x49) ki.length) :
    ∀ kj, rmKeyAt es j = some kj → (kj.1, nb kj.2) ≠ (ti, nb ki) := by
  intro kj hk heq
  have e1 : kj.1 = ti := congrArg Prod.fst heq
  have e2 : nb kj.2 = nb ki := congrArg Prod.snd heq
  have hl97 : ki.length ≤ 97 := by
    rcases rm_wfAt hw hki with ⟨-, d⟩ | ⟨-, d⟩ | ⟨-, d⟩ <;> dsimp only at d <;> omega
  have hl : kj.2.length = ki.length := by
    rcases rm_wfAt hw hk with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
      rcases rm_wfAt hw hki with ⟨c, d⟩ | ⟨c, d⟩ | ⟨c, d⟩ <;> dsimp only at c d <;> omega
  apply hdiff
  rw [rm_mbx (M := M0) (b := R + BitVec.ofNat 32 (98 * j + 1)) (fun c hc => by
      rw [add_ofNat_assoc]; exact hR2 _ (by omega)),
    rm_mbx (M := M0) (b := R + BitVec.ofNat 32 (98 * i + 1)) (a := F + BitVec.ofNat 32 0x49) (fun c hc => by
      rw [add_ofNat_assoc, add_ofNat_assoc, show 0x49 + c = 0x48 + (1 + c) by omega, hcp _ (by omega),
        Nat.add_assoc]),
    ← hl, hj kj hk, hl, hi, e2]

section
variable {M0 M1 Mz : Word → BitVec 8} {s F R MP SP : Word} {ML SL : Nat} {g0 : Fin 32 → Word} {S : Prop}
  {H : Post}

/-- The memory that the duplicate-key loop keeps: memory outside the stack
as in `M1`, the outer loop's words as in `Mz`, and the signature length at
`F + 8`. -/
def RmDM (M1 Mz Mk : Word → BitVec 8) (s F W8 : Word) : Prop :=
  Out M1 Mk s 0x38EC ∧ RmLow Mz Mk F ∧ memLoad32 Mk (F + 8) = W8

theorem rm_dm16 (E : RmBase M0 M1 s F R MP SP ML SL g0) {M2 M' : Word → BitVec 8} {W8 : Word}
    (hM : RmDM M1 Mz M2 s F W8) (h : Out M2 M' (F + 0xFFFFFFF0) 16) : RmDM M1 Mz M' s F W8 := by
  have hw : F + 0xFFFFFFF0 = s + BitVec.ofNat 32 0x3720 := E.Fm (c := 16) (by decide) rfl
  rw [hw] at h
  obtain ⟨hO, hL, hW⟩ := hM
  refine ⟨hO.trans (E.outS h (by decide)),
    hL.out h (E.fs (c := 0xC) (n := 0x3C) (d := 0x3720) (k := 16) (Or.inr (by decide)) (by decide) (by decide)).symm,
    ?_⟩
  rw [← hW]
  exact h.load32 (E.fs (c := 8) (n := 4) (d := 0x3720) (k := 16) (Or.inr (by decide)) (by decide) (by decide)).symm

theorem rm_dlk : ∀ x, x ∈ rmDL → x ∈ rmDK := by decide

theorem rm_bnz : ∀ r < 8, branchTaken .beq (BitVec.ofNat 32 (4 * (r + 1))) 0 = false := by decide

theorem rm_blt7 : ∀ j < 8, branchTaken .bltu (aluEval .add 0 7) (BitVec.ofNat 32 j) = false := by decide

/-- One pass of the duplicate-key loop, from 0x184: compare the key of slot
`i` with that of the counted slot `j`. -/
theorem rm_dstep (E : RmBase M0 M1 s F R MP SP ML SL g0) {t : Nat} {es : List RkEntry} (hR : RkAt M0 R t es)
    (hw : RkWf es) {i ti : Nat} {ki : Bytes} (hi8 : i < 8) (hki : rmKeyAt es i = some (ti, ki))
    {gK : Fin 32 → Word} (hKsp : gK sp = F) (hK18 : gK 18 = 0x62) (hK19 : gK 19 = R)
    (hK27 : gK 27 = R + BitVec.ofNat 32 (98 * i)) {W8 : Word} {m j : Nat} (hm8 : m < 8)
    (hj : memLoad32 Mz (F + BitVec.ofNat 32 (0x28 + 4 * m)) = BitVec.ofNat 32 j) (hj8 : j < 8)
    (hskip : ∀ Mk g', RmDM M1 Mz Mk s F W8 → (∀ x, x ∈ rmDL → g' x = gK x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x2C0 g')
    {g : Fin 32 → Word}
    (hnx : ∀ Mk g', RmDM M1 Mz Mk s F W8 → (∀ x, x ∈ rmDL → g' x = gK x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → g' 8 = g 8 → g' 9 = g 9 →
      (∀ kj, rmKeyAt es j = some kj → (kj.1, nb kj.2) ≠ (ti, nb ki)) →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x1DE g')
    (hK : ∀ x, x ∈ rmDL → g x = gK x) (h8 : g 8 = F + BitVec.ofNat 32 (0x28 + 4 * m))
    (hfr : ∀ x, x ∉ rkE → g x = g0 x) {Mk : Word → BitVec 8} (hM : RmDM M1 Mz Mk s F W8) :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x184 g := by
  obtain ⟨hO, hLo, hW8⟩ := hM
  have hsp : g sp = F := (hK sp (by decide)).trans hKsp
  have h18 : g 18 = 0x62 := (hK 18 (by decide)).trans hK18
  have h19 : g 19 = R := (hK 19 (by decide)).trans hK19
  have h27 : g 27 = R + BitVec.ofNat 32 (98 * i) := (hK 27 (by decide)).trans hK27
  have hJ : memLoad32 Mk (F + BitVec.ofNat 32 (0x28 + 4 * m)) = BitVec.ofNat 32 j := by
    have := hLo.load (c := 0x1C + 4 * m) (by omega)
    rw [show 0xC + (0x1C + 4 * m) = 0x28 + 4 * m by omega] at this
    rw [this, hj]
  have hR0 : ∀ M' : Word → BitVec 8, Out M1 M' s 0x38EC → ∀ d, d < 0x540 →
      M' (R + BitVec.ofNat 32 d) = M0 (R + BitVec.ofNat 32 d) :=
    fun M' h d hd => E.agree h _ (sep_pt E.hSR hd)
  have hc := E.codeA hO
  refine WP.lw rkm_at_184 (by (try rsimp); rw [h8, add_lit_zero]; exact E.alF (by omega)) ?_; wn
  refine WP.aluImm rkm_at_188 ?_; wn
  refine WP.aluImm rkm_at_18a ?_; wn
  refine WP.alu rkm_at_18e ?_; wn
  refine WP.callMemcpy (dst := F + BitVec.ofNat 32 0x48) (src := R + BitVec.ofNat 32 (98 * i))
    (F := s + BitVec.ofNat 32 0x3720) (N := 0x62) rkm_at_190 rkm_at_194 (by decide) (by decide) (by decide)
    hc.rk.tps.bms (E.mcFR hc (c := 0x48) (d := 98 * i) (n := 0x62) (by decide) (by omega))
    (by (try rsimp); rw [ev_add, hsp]; rfl) (by (try rsimp); (try simp only [ev0]); exact h27)
    (by (try rsimp); (try simp only [ev0]); try rfl) (by (try rsimp); rw [hsp]; exact (E.sp 0x3720 (by decide)).symm)
    (E.lowS (by decide) (by decide) (by decide)) (E.cF (c := 0x48) (by decide)) fun m2 hO3 => ?_
  generalize m2.mem = M2 at hO3
  have oC : Out Mk (copyBytes Mk (F + BitVec.ofNat 32 0x48) (R + BitVec.ofNat 32 (98 * i)) 0x62)
      (F + BitVec.ofNat 32 0x48) 0x62 := fun x hx => copyBytes_sep hx.symm (Nat.le_refl _)
  have hO2 : Out M1 M2 s 0x38EC := hO.trans ((E.outF oC (by decide)).trans (E.outS hO3 (by decide)))
  have hL2 : RmLow Mz M2 F := (hLo.out oC (rm_ff F (Or.inr (by decide)) (by decide) (by decide))).out hO3
    (E.fs (c := 0xC) (n := 0x3C) (d := 0x3720) (k := 16) (Or.inr (by decide)) (by decide) (by decide)).symm
  have hW2 : memLoad32 M2 (F + 8) = W8 := by
    rw [← hW8]
    show memLoad32 M2 (F + BitVec.ofNat 32 8) = memLoad32 Mk (F + BitVec.ofNat 32 8)
    rw [hO3.load32 (E.fs (c := 8) (n := 4) (d := 0x3720) (k := 16) (Or.inr (by decide)) (by decide)
      (by decide)).symm]
    exact oC.load32 (rm_ff F (c := 0x48) (n := 0x62) (d := 8) (k := 4) (Or.inr (by decide)) (by decide) (by decide))
  have hM2 : RmDM M1 Mz M2 s F W8 := ⟨hO2, hL2, hW2⟩
  have hcp : ∀ c, c < 0x62 → M2 (F + BitVec.ofNat 32 (0x48 + c)) = M0 (R + BitVec.ofNat 32 (98 * i + c)) := by
    intro c hc'
    rw [hO3 _ (E.fs (c := 0x48 + c) (n := 1) (d := 0x3720) (k := 16) (Or.inr (by omega)) (by omega) (by decide)),
      ← add_ofNat_assoc, copyBytes_at hc' (by decide), add_ofNat_assoc]
    exact hR0 Mk hO _ (by omega)
  refine WP.aluImm rkm_at_198 ?_; wn
  refine WP.branch rkm_at_19a (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso
    (try rsimp at eb)
    rw [h8, add_lit_zero, hJ, rm_blt7 j hj8] at eb
    exact absurd eb (by decide)
  refine WP.alu rkm_at_19e ?_; wn
  refine WP.alu rkm_at_1a2 ?_; wn
  refine WP.lbu rkm_at_1a4 ?_; wn
  refine WP.lbu rkm_at_1a8 ?_; wn
  rcases rm_slotKey hR hi8 with ⟨hn, -⟩ | ⟨ti', ki', hki', hbi, hbyi⟩
  · rw [hki] at hn; cases hn
  rw [hki] at hki'
  cases hki'
  have hT : BitVec.ofNat 8 ti = 0 ∨ BitVec.ofNat 8 ti = 1 ∨ BitVec.ofNat 8 ti = 2 := by
    rcases rm_wfAt hw hki with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> dsimp only at h <;> rw [h] <;> decide
  have hjK : ∀ kj, rmKeyAt es j = some kj → M0 (R + BitVec.ofNat 32 (98 * j)) = BitVec.ofNat 8 kj.1 ∧
      memBytes M0 (R + BitVec.ofNat 32 (98 * j + 1)) kj.2.length = nb kj.2 := by
    intro kj hk
    rcases rm_slotKey hR hj8 with ⟨hn, -⟩ | ⟨tj, kj', hkj, hb, hby⟩
    · rw [hn] at hk; cases hk
    · rw [hkj] at hk; cases hk; exact ⟨hb, hby⟩
  have hB : M0 (R + BitVec.ofNat 32 (98 * j)) = 0xFF ∨ M0 (R + BitVec.ofNat 32 (98 * j)) = 0 ∨
      M0 (R + BitVec.ofNat 32 (98 * j)) = 1 ∨ M0 (R + BitVec.ofNat 32 (98 * j)) = 2 := by
    rcases rm_slotKey hR hj8 with ⟨-, hb⟩ | ⟨tj, kj, hkj, hb, -⟩
    · exact Or.inl hb
    · rcases rm_wfAt hw hkj with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> dsimp only at h <;> rw [hb, h] <;> decide
  have hA : aluEval .add (aluEval .mul (memLoad32 Mk (g 8 + 0)) (g 18)) (g 19) = R + BitVec.ofNat 32 (98 * j) := by
    rw [h8, add_lit_zero, hJ, h18, h19, rm_mul98 j hj8, ev_add, BitVec.add_comm]
  have hA1 : ∀ d, d = 98 * j + 1 →
      aluEval .add (aluEval .add (aluEval .mul (memLoad32 Mk (g 8 + 0)) (g 18)) (g 19)) 1 = R + BitVec.ofNat 32 d := by
    intro d hd
    rw [hA, ev_add, show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc, hd]
  have hR2 := hR0 M2 hO2
  have hjb : ∀ kj, rmKeyAt es j = some kj →
      memBytes M0 (R + BitVec.ofNat 32 (98 * j + 1)) kj.2.length = nb kj.2 := fun kj hk => (hjK kj hk).2
  refine rm_tags (B := M0 (R + BitVec.ofNat 32 (98 * j))) (T := BitVec.ofNat 8 ti) hB hT ?_ ?_ E.hz0
    (by keepz E.hz0) (fun hBT g' hk' hz' hf' => ?_) (fun _ hT0 g' hk' hz' hf' h10' => ?_)
    (fun _ hT0 g' hk' hz' hf' h10' => ?_) (fun _ hT0 g' hk' hz' hf' h10' => ?_)
  · (try rsimp)
    rw [hA, add_lit_zero, hR2 _ (by omega)]
  · (try rsimp)
    rw [hsp]
    have := hcp 0 (by decide)
    simp only [Nat.add_zero] at this
    exact congrArg (BitVec.zeroExtend 32) (this.trans hbi)
  all_goals
    have hk2 : ∀ x, x ∈ rmDK → g' x = g x := by
      intro x hx; rw [hk' x hx]; revert x; rmkeep (fun _ _ => rfl)
    have hKg : ∀ x, x ∈ rmDL → g' x = gK x := fun x hx => (hk2 x (rm_dlk x hx)).trans (hK x hx)
  · exact hnx M2 g' hM2 hKg hz' hf' (hk2 8 (by decide)) (hk2 9 (by decide)) fun kj hk heq => hBT (by
      have e1 : kj.1 = ti := congrArg Prod.fst heq
      rw [(hjK kj hk).1, e1])
  all_goals
    have hsp' : g' sp = F := (hk2 sp (by decide)).trans hsp
    have h10 : g' 10 = R + BitVec.ofNat 32 (98 * j + 1) := by rw [h10']; (try rsimp); exact hA1 _ rfl
    have hsk : ∀ M' g'', RmCK M2 M' F g' g'' g0 → WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) M' 0x2C0 g'' :=
      fun M' g'' hck => hskip M' g'' (rm_dm16 E hM2 hck.1)
        (fun x hx => (hck.2.1 x (rm_dlk x hx)).trans (hKg x hx)) hck.2.2.1 hck.2.2.2
    have hnk : ∀ M' g'', RmCK M2 M' F g' g'' g0 →
        (∀ kj, rmKeyAt es j = some kj → (kj.1, nb kj.2) ≠ (ti, nb ki)) →
        WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) M' 0x1DE g'' :=
      fun M' g'' hck hne => hnx M' g'' (rm_dm16 E hM2 hck.1)
        (fun x hx => (hck.2.1 x (rm_dlk x hx)).trans (hKg x hx)) hck.2.2.1 hck.2.2.2
        ((hck.2.1 8 (by decide)).trans (hk2 8 (by decide))) ((hck.2.1 9 (by decide)).trans (hk2 9 (by decide))) hne
  · have hl : ki.length = 65 := by
      rcases rm_wfAt hw hki with ⟨h, l⟩ | ⟨h, l⟩ | ⟨h, l⟩ <;> dsimp only at h l <;>
        first | exact l | (rw [h] at hT0; exact absurd hT0 (by decide))
    exact rm_c0 E (E.codeA hO2) hsp' h10 hz' hf' hsk fun hd M' g'' hck =>
      hnk M' g'' hck (rm_ne hw hki hjb hbyi hR2 hcp hj8 (by rw [hl]; exact hd))
  · have hl : ki.length = 97 := by
      rcases rm_wfAt hw hki with ⟨h, l⟩ | ⟨h, l⟩ | ⟨h, l⟩ <;> dsimp only at h l <;>
        first | exact l | (rw [h] at hT0; exact absurd hT0 (by decide))
    exact rm_c1 E (E.codeA hO2) (by omega) hsp' h10 hf' hsk fun hd M' g'' hck =>
      hnk M' g'' hck (rm_ne hw hki hjb hbyi hR2 hcp hj8 (by rw [hl]; exact hd))
  · have hl : ki.length = 32 := by
      rcases rm_wfAt hw hki with ⟨h, l⟩ | ⟨h, l⟩ | ⟨h, l⟩ <;> dsimp only at h l <;>
        first | exact l | (rw [h] at hT0; exact absurd hT0 (by decide))
    exact rm_c2 E (E.codeA hO2) (by omega) hsp' h10 hf' hsk fun hd M' g'' hck =>
      hnk M' g'' hck (rm_ne hw hki hjb hbyi hR2 hcp hj8 (by rw [hl]; exact hd))

/-- No counted slot before position `m` of `cs` holds the key of slot `i`,
as memory holds keys. -/
def RmPd (es : List RkEntry) (cs : List Nat) (ti : Nat) (ki : Bytes) (m : Nat) : Prop :=
  ∀ m', m' < m → ∀ kj, rmKeyAt es (cs.getD m' 0) = some kj → (kj.1, nb kj.2) ≠ (ti, nb ki)

theorem rm_pdS {es : List RkEntry} {cs : List Nat} {ti m : Nat} {ki : Bytes} (h : RmPd es cs ti ki m)
    (hm : ∀ kj, rmKeyAt es (cs.getD m 0) = some kj → (kj.1, nb kj.2) ≠ (ti, nb ki)) :
    RmPd es cs ti ki (m + 1) := by
  intro m' hm' kj hk
  by_cases hlt : m' < m
  · exact h m' hlt kj hk
  · have : m' = m := by omega
    subst this
    exact hm kj hk

/-- The duplicate-key loop from 0x184, with `r + 1` counted slots left from
position `m` of `cs`. -/
theorem rm_dloop (E : RmBase M0 M1 s F R MP SP ML SL g0) {t : Nat} {es : List RkEntry} (hR : RkAt M0 R t es)
    (hw : RkWf es) {i ti : Nat} {ki : Bytes} (hi8 : i < 8) (hki : rmKeyAt es i = some (ti, ki))
    {gK : Fin 32 → Word} (hKsp : gK sp = F) (hK18 : gK 18 = 0x62) (hK19 : gK 19 = R)
    (hK27 : gK 27 = R + BitVec.ofNat 32 (98 * i)) {W8 : Word} {cs : List Nat} (hc8 : cs.length ≤ 8)
    (hcs : ∀ m, m < cs.length →
      memLoad32 Mz (F + BitVec.ofNat 32 (0x28 + 4 * m)) = BitVec.ofNat 32 (cs.getD m 0) ∧ cs.getD m 0 < 8)
    (hskip : ∀ Mk g', RmDM M1 Mz Mk s F W8 → (∀ x, x ∈ rmDL → g' x = gK x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x2C0 g')
    (hdone : ∀ Mk g', RmDM M1 Mz Mk s F W8 → (∀ x, x ∈ rmDL → g' x = gK x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → RmPd es cs ti ki cs.length →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x20A g') :
    ∀ r m, m + r + 1 = cs.length → RmPd es cs ti ki m → ∀ (g : Fin 32 → Word) (Mk : Word → BitVec 8),
      (∀ x, x ∈ rmDL → g x = gK x) → g 8 = F + BitVec.ofNat 32 (0x28 + 4 * m) →
      g 9 = BitVec.ofNat 32 (4 * (r + 1)) → (∀ x, x ∉ rkE → g x = g0 x) → RmDM M1 Mz Mk s F W8 →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x184 g := by
  intro r
  induction r with
  | zero =>
    intro m hm hP g Mk hK h8 h9 hfr hM
    refine rm_dstep E hR hw hi8 hki hKsp hK18 hK19 hK27 (m := m) (j := cs.getD m 0) (by omega)
      (hcs m (by omega)).1 (hcs m (by omega)).2 hskip ?_ hK h8 hfr hM
    intro Mk' g' hM' hK' hz' hf' e8 e9 hne
    refine WP.aluImm rkm_at_1de ?_; wn
    refine WP.aluImm rkm_at_1e0 ?_; wn
    refine WP.branch rkm_at_1e2 (fun eb => ?_) (fun eb => ?_) <;> wn
    · exact hdone Mk' _ hM' (by rmkeep hK') (by rsimp; (try exact hz')) (by keepz E.hz0)
        (by rw [← hm]; exact rm_pdS hP hne)
    · exfalso; (try rsimp at eb); rw [e9, h9, rm_dec4] at eb; exact absurd eb (by decide)
  | succ r ih =>
    intro m hm hP g Mk hK h8 h9 hfr hM
    refine rm_dstep E hR hw hi8 hki hKsp hK18 hK19 hK27 (m := m) (j := cs.getD m 0) (by omega)
      (hcs m (by omega)).1 (hcs m (by omega)).2 hskip ?_ hK h8 hfr hM
    intro Mk' g' hM' hK' hz' hf' e8 e9 hne
    refine WP.aluImm rkm_at_1de ?_; wn
    refine WP.aluImm rkm_at_1e0 ?_; wn
    refine WP.branch rkm_at_1e2 (fun eb => ?_) (fun eb => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [e9, h9, rm_dec4] at eb; exact absurd eb (by rw [rm_bnz r (by omega)]; decide)
    refine WP.jal rkm_at_1e4 (by decide) ?_; wn
    refine ih (m + 1) (by omega) (rm_pdS hP hne) _ Mk' (by rmkeep hK') ?_ ?_ (by keepz E.hz0) hM'
    · (try rsimp); rw [e8, h8, ev_add, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]; rfl
    · (try rsimp); rw [e9, h9, rm_dec4]
/-- The duplicate-key loop from 0x17E: either some counted slot holds the
key of slot `i` and the code goes to 0x2C0, or none does and it goes to
0x20A. -/
theorem rm_dup (E : RmBase M0 M1 s F R MP SP ML SL g0) {t : Nat} {es : List RkEntry} (hR : RkAt M0 R t es)
    (hw : RkWf es) {i ti : Nat} {ki : Bytes} (hi8 : i < 8) (hki : rmKeyAt es i = some (ti, ki))
    {g : Fin 32 → Word} (hsp : g sp = F) (h18 : g 18 = 0x62) (h19 : g 19 = R)
    (h27 : g 27 = R + BitVec.ofNat 32 (98 * i)) {W8 : Word} {cs : List Nat} (hc8 : cs.length ≤ 8)
    (hcs : ∀ m, m < cs.length →
      memLoad32 Mz (F + BitVec.ofNat 32 (0x28 + 4 * m)) = BitVec.ofNat 32 (cs.getD m 0) ∧ cs.getD m 0 < 8)
    (hcnt : memLoad32 Mz (F + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 (4 * cs.length))
    (hskip : ∀ Mk g', RmDM M1 Mz Mk s F W8 → (∀ x, x ∈ rmDL → g' x = g x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x2C0 g')
    (hdone : ∀ Mk g', RmDM M1 Mz Mk s F W8 → (∀ x, x ∈ rmDL → g' x = g x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → RmPd es cs ti ki cs.length →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x20A g')
    (hfr : ∀ x, x ∉ rkE → g x = g0 x) {Mk : Word → BitVec 8} (hM : RmDM M1 Mz Mk s F W8) :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x17E g := by
  have hE := fun x (_ : x ∈ rmDL) => (rfl : g x = g x)
  refine WP.zero fun hz => ?_
  have hc9 : memLoad32 Mk (F + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 (4 * cs.length) :=
    (hM.2.1.load (c := 0x10) (by decide)).trans hcnt
  refine WP.aluImm rkm_at_17e ?_; wn
  refine WP.lw rkm_at_180 (by (try rsimp); rw [hsp]; exact E.alF (c := 0x1C) (by decide)) ?_; wn
  refine WP.branch rkm_at_182 (fun eb => ?_) (fun eb => ?_) <;> wn
  · cases hl : cs.length with
    | zero =>
      exact hdone Mk _ hM (by rmkeep hE) (by rsimp; (try exact hz)) (by keepz E.hz0)
        (by rw [hl]; exact fun m' h => absurd h (by omega))
    | succ k =>
      exfalso; (try rsimp at eb); rw [hsp] at eb
      change branchTaken .beq (memLoad32 Mk (F + BitVec.ofNat 32 0x1C)) 0 = true at eb
      rw [hc9, hl] at eb; exact absurd eb (by rw [rm_bnz k (by omega)]; decide)
  · cases hl : cs.length with
    | zero =>
      exfalso; (try rsimp at eb); rw [hsp] at eb
      change branchTaken .beq (memLoad32 Mk (F + BitVec.ofNat 32 0x1C)) 0 = false at eb
      rw [hc9, hl] at eb; exact absurd eb (by decide)
    | succ k =>
      refine rm_dloop E hR hw hi8 hki hsp h18 h19 h27 hc8 hcs hskip hdone k 0 (by omega)
        (fun m' h => absurd h (by omega)) _ Mk (by rmkeep hE) ?_ ?_ (by keepz E.hz0) hM
      · (try rsimp); rw [hsp]; rfl
      · (try rsimp); rw [hsp]
        change memLoad32 Mk (F + BitVec.ofNat 32 0x1C) = _
        rw [hc9, hl]

end

end C3.RV32
