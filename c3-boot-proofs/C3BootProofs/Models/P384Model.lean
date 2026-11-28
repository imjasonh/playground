import C3BootProofs.Models.P384Inv
import C3BootProofs.Models.P384Point
import C3BootProofs.Models.EcdsaWnaf
import C3BootProofs.Proofs.SvPvModel

/-!
# The P-384 check computes `p384Verify`

`p384_model_mem` assembles the layers for `pvModel`: the inversion of `s`
gives `w = s⁻¹` in Montgomery form, the scalar products are `u₁` and `u₂`,
the wNAF digits sum to them, the main loop ends at `u₁ G + u₂ Q`, and the
inversion of `Z` gives its affine `x`, which the check compares with `r` in
Montgomery form.

`SvPvRes` says what `pvModel` returns on every memory that `SvPvAt`
describes, so it says nothing when no memory does, and `pvModel` reads `r`
and `s` as `svBytes sr 48` and `svBytes ss 48`. `SvP384Model'` therefore
asks for such a memory and states the result for `svBytes sr 48` and
`svBytes ss 48`.
-/

namespace C3.Models

open C3.RV32 C3.RV32.Pv C3.RV32.P3 C3.RV32.Dq C3.RV32.Fs C3.RV32.Sv C3.Image

/-- `p384_verify_prehash` accepts only signatures that `p384Verify` accepts,
for a memory that `SvPvAt` describes, and the 48-byte `r` and `s` that it
reads. -/
def SvP384Model' (M : Word → BitVec 8) : Prop :=
  ∀ (pk ph : Word) (len : Nat) (h : Bytes) (rp sp' : Word) (sr ss : Bytes) (pv : Word),
    (∃ M', SvPvAt M M' pk ph len h rp sp' sr ss) → SvPvRes M pk ph len h rp sp' sr ss (some pv) → pv ≠ 0 →
      p384Verify (memBytes M pk 0x61) h (svBytes sr 48) (svBytes ss 48) = true

theorem n384_n : C3.p384.n = n384 := by unfold n384; rfl

set_option exponentiation.threshold 800 in
set_option maxRecDepth 10000 in
theorem n3_rinv : 2 ^ 384 * n3RInv % n384 = 1 := by unfold n384 n3RInv; decide

set_option exponentiation.threshold 800 in
theorem p3_rinv' : 2 ^ 384 * p3RInv % RV32.p384 = 1 := p384_p ▸ p3_rinv

theorem mod3 {p : Nat} (a b c : Nat) : ((a % p + b % p) % p + c % p) % p = (a + b + c) % p := by
  calc ((a % p + b % p) % p + c % p) % p = (a % p + (b % p + c)) % p := by
        rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
    _ = (a + c + b % p) % p := by rw [Nat.mod_add_mod, Nat.add_comm (b % p) c, ← Nat.add_assoc]
    _ = (a + b + c) % p := by rw [Nat.add_mod_mod, Nat.add_right_comm]

theorem memBytes_drop (M : Word → BitVec 8) (p : Word) {k n : Nat} (h : k ≤ n) :
    (memBytes M p n).drop k = memBytes M (p + BitVec.ofNat 32 k) (n - k) := by
  have := memBytes_split M p k (n - k)
  rw [show k + (n - k) = n by omega] at this
  rw [this, List.drop_left' (memBytes_length M p k)]

/-! ## The key -/

set_option exponentiation.threshold 800 in
/-- `x³ + ax + b` in Montgomery form. -/
theorem dqAlpha_mont (x : Nat) :
    dqAlpha (x * 2 ^ 384 % RV32.p384) = (x * x * x + (RV32.p384 - 3) * x + C3.p384.b) * 2 ^ 384 % RV32.p384 := by
  have hX : x * 2 ^ 384 % RV32.p384 % RV32.p384 = x * 2 ^ 384 % RV32.p384 := Nat.mod_mod _ _
  have h2 : p3fm (x * 2 ^ 384 % RV32.p384) (x * 2 ^ 384 % RV32.p384) = x * x * 2 ^ 384 % RV32.p384 :=
    mont_mul p3_rinv' hX hX
  have h3 : p3fm (p3fm (x * 2 ^ 384 % RV32.p384) (x * 2 ^ 384 % RV32.p384)) (x * 2 ^ 384 % RV32.p384) =
      x * x * x * 2 ^ 384 % RV32.p384 :=
    mont_mul p3_rinv' (by rw [h2, Nat.mod_mod]) hX
  have hA : p3A % RV32.p384 = (RV32.p384 - 3) * 2 ^ 384 % RV32.p384 := by rw [p3A_mont, Nat.mod_mod]
  have h4 : p3fm p3A (x * 2 ^ 384 % RV32.p384) = (RV32.p384 - 3) * x * 2 ^ 384 % RV32.p384 :=
    mont_mul p3_rinv' hA hX
  unfold dqAlpha
  rw [p3AddRes_mod (p3fm_lt _ _) (p3fm_lt _ _), p3AddRes_mod (Nat.mod_lt _ p384_pos) p3B_lt, h3, h4, p3B_mont,
    mod3, Nat.add_mul, Nat.add_mul]
  rfl

theorem fs_eq {M : Word → BitVec 8} {pk : Word} (hg : FsOk M pk) :
    fsVal M pk 0x31 * fsVal M pk 0x31 % C3.p384.p =
      (fsVal M pk 1 * fsVal M pk 1 % C3.p384.p * fsVal M pk 1 + C3.p384.a * fsVal M pk 1 + C3.p384.b) % C3.p384.p := by
  obtain ⟨-, -, -, he⟩ := hg
  have hYY : p3fm (fsVal M pk 0x31 * 2 ^ 384 % RV32.p384) (fsVal M pk 0x31 * 2 ^ 384 % RV32.p384) =
      fsVal M pk 0x31 * fsVal M pk 0x31 * 2 ^ 384 % RV32.p384 :=
    mont_mul p3_rinv' (Nat.mod_mod _ _) (Nat.mod_mod _ _)
  rw [he, dqAlpha_mont] at hYY
  have hc := mont_cancel p3_rinv' hYY
  rw [p384_p, show C3.p384.a = RV32.p384 - 3 by rw [← p384_p]; rfl, ← hc]
  have h1 : fsVal M pk 1 * fsVal M pk 1 % RV32.p384 * fsVal M pk 1 % RV32.p384 =
      fsVal M pk 1 * fsVal M pk 1 * fsVal M pk 1 % RV32.p384 := Nat.mod_mul_mod _ _ _
  have h2 : (fsVal M pk 1 * fsVal M pk 1 % RV32.p384 * fsVal M pk 1 + (RV32.p384 - 3) * fsVal M pk 1) % RV32.p384 =
      (fsVal M pk 1 * fsVal M pk 1 * fsVal M pk 1 + (RV32.p384 - 3) * fsVal M pk 1) % RV32.p384 := by
    rw [Nat.add_mod, h1, ← Nat.add_mod]
  rw [Nat.add_mod (fsVal M pk 1 * fsVal M pk 1 % RV32.p384 * fsVal M pk 1 + (RV32.p384 - 3) * fsVal M pk 1), h2,
    ← Nat.add_mod]

/-- The key the check accepts decodes to its coordinates. -/
theorem fs_decode {M : Word → BitVec 8} {pk : Word} (hg : FsOk M pk) :
    C3.p384.decodePoint (memBytes M pk 0x61) = some (fsVal M pk 1, fsVal M pk 0x31) := by
  have heq := fs_eq hg
  obtain ⟨h4, hx, hy, -⟩ := hg
  refine decode_some (by rw [memBytes_length]; rfl) ?_ ?_ ?_ (p384_p ▸ hx) (p384_p ▸ hy) heq
  · rw [show 0x61 = 0x60 + 1 from rfl, memBytes_succ, List.head?_cons, h4]
    rfl
  · rw [memBytes_drop M pk (by decide), memBytes_take' (by decide)]
    rfl
  · rw [memBytes_drop M pk (by decide)]
    rfl

/-- The key the check accepts is on the curve. -/
theorem fs_onC {M : Word → BitVec 8} {pk : Word} (hg : FsOk M pk) :
    EC.OnC C3.p384 (some (fsVal M pk 1, fsVal M pk 0x31)) :=
  onC_of_eq (p384_p ▸ hg.2.1) (p384_p ▸ hg.2.2.1) (fs_eq hg)

/-! ## The scalars -/

theorem mul_unit {n R Ri : Nat} (hR : R * Ri % n = 1) (a : Nat) : a * (R * Ri) % n = a % n := by
  rw [Nat.mul_mod, hR, Nat.mul_one, Nat.mod_mod]

/-- `n3fm W 1`, `W` taken out of Montgomery form, is `s⁻¹` modulo `n` when
`W (s R mod n) ≡ R²`. -/
theorem mont_inv {n R Ri W s : Nat} (hR : R * Ri % n = 1) (hn : 1 < n)
    (hW : W * (s * R % n) % n = R * R % n) : W * 1 * Ri % n * s % n = 1 := by
  calc W * 1 * Ri % n * s % n = W * Ri * s * (R * Ri) % n := by
        rw [Nat.mod_mul_mod, Nat.mul_one, mul_unit hR]
    _ = W * (s * R) % n * (Ri * Ri) % n := by
        rw [Nat.mod_mul_mod]; simp only [Nat.mul_comm, Nat.mul_left_comm]
    _ = W * (s * R % n) % n * (Ri * Ri) % n := by rw [Nat.mul_mod_mod]
    _ = 1 := by
        rw [hW, Nat.mod_mul_mod, show R * R * (Ri * Ri) = 1 * (R * Ri) * (R * Ri) by
          rw [Nat.one_mul]; simp only [Nat.mul_comm, Nat.mul_left_comm], mul_unit hR, mul_unit hR,
          Nat.one_mod_eq_one.mpr (by omega)]

/-- The Montgomery products the check forms: `n3fm (n3fm (a R) W) 1` is
`a` times `n3fm W 1` modulo `n`. -/
theorem mont_scal {n R Ri a W : Nat} (hR : R * Ri % n = 1) :
    a * R % n * W * Ri % n * 1 * Ri % n = a * (W * 1 * Ri % n) % n := by
  rw [Nat.mul_one, Nat.mul_one, Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mul_assoc (a * R % n), Nat.mul_assoc (a * R % n),
    Nat.mod_mul_mod, show a * R * (W * Ri * Ri) = a * (W * Ri) * (R * Ri) by
      simp only [Nat.mul_comm, Nat.mul_left_comm], mul_unit hR]

/-! ## The model -/

set_option maxHeartbeats 8000000 in
set_option exponentiation.threshold 800 in
/-- **The P-384 check**: when `pvModel` returns a nonzero word, the key, the
prehash, `r`, and `s` it reads pass `p384Verify`. -/
theorem p384_model_mem {M : Word → BitVec 8} {pk ph rp sp' : Word} {len : Nat} {pv : Word}
    (hp : IsPrime C3.p384.p) (hc : EC.AddClosed C3.p384) (ha : EC.AddAssoc C3.p384) (hadd : P384AddOk)
    (hdbl : P384DblOk) (h : pvModel M pk ph len rp sp' = some pv) (hpv : pv ≠ 0) :
    p384Verify (memBytes M pk 0x61) (memBytes M ph (min len 48)) (memBytes M rp 48) (memBytes M sp' 48) = true := by
  unfold pvModel at h
  by_cases hck : ¬ (PvCk1 M pk rp sp' ∧ PvCk2 M rp sp')
  · rw [ite_eq_right hck] at h
    exact absurd (Option.some.inj h).symm hpv
  have hck : PvCk1 M pk rp sp' ∧ PvCk2 M rp sp' := Decidable.of_not_not hck
  rw [ite_eq_left hck] at h
  obtain ⟨⟨-, -, hfs⟩, hrn, hsn, hr0, hs0⟩ := hck
  by_cases hf : ¬ (pvW M sp').f.natAbs = 1
  · rw [ite_eq_right hf] at h
    cases h
  have hf : (pvW M sp').f.natAbs = 1 := Decidable.of_not_not hf
  rw [ite_eq_left hf] at h
  -- The inverse of `s`.
  have hS : beNat (memBytes M sp' 48) * 2 ^ 384 % n384 < n384 := Nat.mod_lt _ (by decide)
  obtain ⟨hw, hwn⟩ := pvInv_inv hS hf
  have hW : pvInv (pvW M sp') * (beNat (memBytes M sp' 48) * 2 ^ 384 % n384) % n384 = 2 ^ 384 * 2 ^ 384 % n384 := by
    have := MEq.natCast.mp (show MEq n384 ((pvInv (pvW M sp') * (beNat (memBytes M sp' 48) * 2 ^ 384 % n384) : Nat) : Int)
      ((2 ^ 768 % n384 : Nat) : Int) by rw [Int.natCast_mul]; exact hw)
    rw [this, Nat.mod_mod, ← Nat.pow_add]
  have hinv0 := mont_inv n3_rinv (by decide) hW
  have hinv : modInv (beNat (memBytes M sp' 48)) C3.p384.n = n3fm (pvInv (pvW M sp')) 1 := by
    rw [n384_n]
    refine modInv_unique (by decide) (Nat.mod_lt _ (by decide)) ?_
    rw [← Int.natCast_mul]
    exact MEq.natCast.mpr (by unfold n3fm; rw [hinv0, Nat.one_mod_eq_one.mpr (by decide)])
  -- The scalars.
  generalize hW0 : pvInv (pvW M sp') = W at hinv hwn
  rcases hsum : pvSumM M pk ph len rp sp' with _ | ⟨PX, PY, PZ⟩ <;> rw [hsum] at h
  · cases h
  have hH : pvH (beNat (memBytes M rp 48) * 2 ^ 384 % n384) PX PZ = pv := Option.some.inj h
  unfold pvSumM pvSum pvD pvL at hsum
  rw [hW0] at hsum
  have hu1e : n3fm (n3fm (beNat (memBytes M ph (min len 48)) * 2 ^ 384 % n384) W) 1 =
      beNat (memBytes M ph (min len 48)) * n3fm W 1 % n384 := mont_scal n3_rinv
  have hu2e : n3fm (n3fm (beNat (memBytes M rp 48) * 2 ^ 384 % n384) W) 1 =
      beNat (memBytes M rp 48) * n3fm W 1 % n384 := mont_scal n3_rinv
  rw [hu1e, hu2e, mlRun_eq, pvG_val, montOne_val, ← p384_p] at hsum
  generalize hU1 : beNat (memBytes M ph (min len 48)) * n3fm W 1 % n384 = u1 at hsum
  generalize hU2 : beNat (memBytes M rp 48) * n3fm W 1 % n384 = u2 at hsum
  have hu1 : u1 < 2 ^ 0x180 := hU1 ▸ Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have hu2 : u2 < 2 ^ 0x180 := hU2 ▸ Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  -- The digits.
  have hl1 := wnafGo_length hu1 0x181 0 0 (Nat.zero_le _) (Nat.zero_le _)
  have hl2 := wnafGo_length hu2 0x181 0 0 (Nat.zero_le _) (Nat.zero_le _)
  generalize hLm : max (wnafGo u1 0x180 0x181 0 0).length (wnafGo u2 0x180 0x181 0 0).length = Lm at hsum
  have hLm1 : (wnafGo u1 0x180 0x181 0 0).length ≤ Lm := hLm ▸ Nat.le_max_left _ _
  have hLm2 : (wnafGo u2 0x180 0x181 0 0).length ≤ Lm := hLm ▸ Nat.le_max_right _ _
  have hLmK : Lm ≤ 0x181 := hLm ▸ Nat.max_le.mpr ⟨hl1, hl2⟩
  have hd1 : dsum (wnafBytes (wnafGo u1 0x180 0x181 0 0) 0x181) Lm = u1 := wnaf_dsum hu1 hLm1 hLmK
  have hd2 : dsum (wnafBytes (wnafGo u2 0x180 0x181 0 0) 0x181) Lm = u2 := wnaf_dsum hu2 hLm2 hLmK
  -- The main loop.
  have hG : EC.OnC C3.p384 (some (C3.p384.gx, C3.p384.gy)) := by unfold EC.OnC MEq; decide
  have hQ := fs_onC hfs
  have L := p384Ops hadd hdbl
  have hqx : fsVal M pk 1 < C3.p384.p := p384_p ▸ hfs.2.1
  have hqy : fsVal M pk 0x31 < C3.p384.p := p384_p ▸ hfs.2.2.1
  have hT0 := tbl_rep hp hc ha L (T := tblPt (C3.p384.gx * 2 ^ 384 % C3.p384.p, C3.p384.gy * 2 ^ 384 % C3.p384.p,
    2 ^ 384 % C3.p384.p)) (g := ⟨_, hG⟩) rfl (fun _ => rfl) (mont_rep (by decide) (by decide) (by decide))
  have hT1 := tbl_rep hp hc ha L (T := tblPt (fsVal M pk 1 * 2 ^ 384 % C3.p384.p,
    fsVal M pk 0x31 * 2 ^ 384 % C3.p384.p, 2 ^ 384 % C3.p384.p)) (g := ⟨_, hQ⟩) rfl (fun _ => rfl)
    (mont_rep hqx hqy (by decide))
  obtain ⟨st', hst, hrep, -⟩ := gLoop_spec hp hc ha L (K := 0x181) (fun j _ => hT0 j) (fun j _ => hT1 j)
    (wnafBytes_digOk (wnafGo_dig _ _ _ (Nat.zero_le _)) 0x181)
    (wnafBytes_digOk (wnafGo_dig _ _ _ (Nat.zero_le _)) 0x181) Lm hLmK (idPt, false) 0 0 idPt_rep (fun _ => rfl)
  rw [hst, Option.map_some] at hsum
  have hP := Option.some.inj hsum
  simp only [Int.zero_mul, Int.zero_add] at hrep
  rw [hd1, hd2, hP] at hrep
  have hlc : (lc hp hc ha ⟨_, hG⟩ ⟨_, hQ⟩ (u1 : Int) (u2 : Int)).1 =
      C3.p384.add (C3.p384.mul u1 (some (C3.p384.gx, C3.p384.gy)))
        (C3.p384.mul u2 (some (fsVal M pk 1, fsVal M pk 0x31))) :=
    by rw [EC.mul_eq hp hc ha ⟨_, hG⟩ u1, EC.mul_eq hp hc ha ⟨_, hQ⟩ u2]; rfl
  rw [hlc] at hrep
  -- The affine `x` and the comparison.
  have hZp : PZ < C3.p384.p := by
    rcases hs : C3.p384.add (C3.p384.mul u1 (some (C3.p384.gx, C3.p384.gy)))
      (C3.p384.mul u2 (some (fsVal M pk 1, fsVal M pk 0x31))) with _ | ⟨x, y⟩ <;> rw [hs] at hrep
    · exact hrep.2.2.1
    · exact hrep.2.2.1
  have hRn : 2 ^ 384 * n3RInv % n384 = 1 := n3_rinv
  have hrR : ∀ v, beNat (memBytes M rp 48) * 2 ^ 384 % n384 = v * 2 ^ 384 % n384 →
      v % n384 = beNat (memBytes M rp 48) := fun v e => by
    rw [← Nat.mod_eq_of_lt hrn]; exact (mont_cancel hRn e).symm
  unfold pvH at hH
  by_cases hok : ¬ hvOk PZ
  · rw [ite_eq_right hok] at hH
    by_cases hc0 : beNat (memBytes M rp 48) * 2 ^ 384 % n384 = p3fm 0 1 * 2 ^ 384 % n384
    · have e := hrR _ hc0
      rw [show p3fm 0 1 = 0 by unfold p3fm; simp only [Nat.zero_mul, Nat.zero_mod]] at e
      exact absurd e.symm hr0
    · rw [ite_eq_right hc0] at hH
      exact absurd hH.symm hpv
  have hok : hvOk PZ := Decidable.of_not_not hok
  rw [ite_eq_left hok] at hH
  by_cases hc1 : ¬ beNat (memBytes M rp 48) * 2 ^ 384 % n384 =
      p3fm (p3fm PX (hvInv (hvLoop 15 (hvInit PZ)))) 1 * 2 ^ 384 % n384
  · rw [ite_eq_right hc1] at hH
    exact absurd hH.symm hpv
  have hc1 := Decidable.of_not_not hc1
  obtain ⟨hz, -⟩ := hvInv_inv (p384_p ▸ hZp) hok
  rcases hs : C3.p384.add (C3.p384.mul u1 (some (C3.p384.gx, C3.p384.gy)))
    (C3.p384.mul u2 (some (fsVal M pk 1, fsVal M pk 0x31))) with _ | ⟨x, y⟩ <;> rw [hs] at hrep
  · exact absurd hrep.2.2.2.2.2 hok.2
  rw [p3fm_affine_x hrep (by rw [p384_p]; exact hz)] at hc1
  have hfin := hrR _ hc1
  -- The specification.
  unfold p384Verify Curve.verify
  rw [fs_decode hfs]
  dsimp only
  rw [hinv, show C3.p384.digestScalar (memBytes M ph (min len 48)) = beNat (memBytes M ph (min len 48)) % C3.p384.n by
    unfold Curve.digestScalar
    rw [List.take_of_length_le (by rw [memBytes_length]; exact Nat.min_le_right _ _)], Nat.mod_mul_mod, n384_n, hU1,
    hU2, hs]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, memBytes_length]
  exact ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, by omega⟩, hrn⟩, by omega⟩, hsn⟩, hfin⟩

/-- **`SvP384Model'`**: the P-384 check computes `p384Verify`. -/
theorem p384_model {M : Word → BitVec 8} (hp : IsPrime C3.p384.p) (hc : EC.AddClosed C3.p384)
    (ha : EC.AddAssoc C3.p384) (hadd : P384AddOk) (hdbl : P384DblOk) : SvP384Model' M := by
  intro pk ph len h rp sp' sr ss pv ⟨M', hM⟩ hres hpv
  have e := p384_model_mem hp hc ha hadd hdbl (hres M' hM) hpv
  obtain ⟨hk, -, hh, hr, hs⟩ := hM
  rwa [hk, hh, hr, hs] at e

end C3.Models
