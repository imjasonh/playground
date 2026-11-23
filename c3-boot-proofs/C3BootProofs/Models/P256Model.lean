import C3BootProofs.Models.P256Inv
import C3BootProofs.Models.P256Point
import C3BootProofs.Models.EcdsaWnaf
import C3BootProofs.Proofs.SvGsSpec

/-!
# The P-256 check computes `p256Verify`

`p256_model` assembles the layers: the inversion of `s` gives `w = s⁻¹`,
the scalar products are `u₁` and `u₂`, the wNAF digits sum to them, the main
loop ends at `u₁ G + u₂ Q`, and the inversion of `Z` gives its affine `x`,
which the check compares with `r`.

`SvP256Facts` only constrains the first 32 bytes of `r` and `s` (`b32`),
while `p256Verify` also checks their lengths, so the model holds for
`b32 r` and `b32 s`: `SvP256Model'` states it that way.
-/

namespace C3.Models

open C3.RV32 C3.RV32.Sv C3.RV32.Pv C3.RV32.P2 C3.RV32.Gs C3.Image

/-- The constants the P-256 check reads, as the image holds them: the
order `n`, 1, the prime `p`, `R² mod p`, `G` and 1 in Montgomery form, and
the affine `x` the check uses for the point at infinity. -/
structure P256Consts (M : Word → BitVec 8) : Prop where
  n : accV M (BitVec.ofNat 32 0x3FCC4268) 8 = C3.p256.n
  one : accV M (BitVec.ofNat 32 0x3FCC42E8) 8 = 1
  p : accV M (BitVec.ofNat 32 0x3FCC4B38) 8 = C3.p256.p
  r2 : accV M (BitVec.ofNat 32 0x3FCC4B78) 8 = 2 ^ 512 % C3.p256.p
  gx : accV M (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x0) 8 = C3.p256.gx * 2 ^ 256 % C3.p256.p
  gy : accV M (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x20) 8 = C3.p256.gy * 2 ^ 256 % C3.p256.p
  gz : accV M (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x40) 8 = 2 ^ 256 % C3.p256.p
  mone : accV M (BitVec.ofNat 32 0x3FCC43A8) 8 = 2 ^ 256 % C3.p256.p
  idx : accV M (BitVec.ofNat 32 0x3FCC442C) 8 = 0

/-- The scalar field's compiled `mul` (Barrett reduction) reduces a product
of two scalars below `n` modulo `n`. -/
def P256PsmOk : Prop := ∀ X, X < C3.p256.n * C3.p256.n → psmVal X = X % C3.p256.n

/-- `SvP256Model` for the 32-byte `r` and `s` the check reads. -/
def SvP256Model' (M : Word → BitVec 8) : Prop :=
  ∀ bp dg r s, SvP256Facts M bp dg r s → p256Verify (memBytes M bp 65) (memBytes M dg 32) (b32 r) (b32 s) = true

theorem modInv_lt {a m : Nat} (hm : 0 < m) : modInv a m < m := by
  unfold modInv
  generalize modInv.go m (a % m) 0 1 (2 * m.log2 + 4) = g
  have h1 := Int.emod_nonneg g (show (m : Int) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos g (show (0 : Int) < m by omega)
  omega

/-- An inverse below `m` is the one `modInv` computes. -/
theorem modInv_unique {a w m : Nat} (hm : 1 < m) (hw : w < m) (h : MEq m ((w : Int) * a) 1) : modInv a m = w := by
  have hn : w * a % m = 1 := by
    have := MEq.natCast.mp (show MEq m ((w * a : Nat) : Int) ((1 : Nat) : Int) by rw [Int.natCast_mul]; exact h)
    rwa [Nat.mod_eq_of_lt hm] at this
  have hc : Nat.Coprime a m := by
    have d1 : Nat.gcd a m ∣ w * a := Nat.dvd_trans (Nat.gcd_dvd_left a m) (Nat.dvd_mul_left a w)
    have d2 : Nat.gcd a m ∣ w * a % m := (Nat.dvd_mod_iff (Nat.gcd_dvd_right a m)).mpr d1
    rw [hn] at d2
    exact Nat.dvd_one.mp d2
  have hs := modInv_spec hm hc
  have hv := modInv_lt (a := a) (Nat.lt_trans Nat.zero_lt_one hm)
  have e : w % m = modInv a m % m := by
    calc w % m = w * (a * modInv a m % m) % m := by rw [hs, Nat.mul_one]
      _ = w * a * modInv a m % m := by rw [Nat.mul_mod_mod, Nat.mul_assoc]
      _ = w * a % m * modInv a m % m := by rw [Nat.mod_mul_mod]
      _ = modInv a m % m := by rw [hn, Nat.one_mul]
  rw [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hv] at e
  exact e.symm

theorem gs_eq {M : Word → BitVec 8} {bp : Word} (hg : GsOk M bp) :
    gsVal M bp 0x21 * gsVal M bp 0x21 % RV32.p256 =
      (gsVal M bp 1 * gsVal M bp 1 % RV32.p256 * gsVal M bp 1 + (RV32.p256 - 3) * gsVal M bp 1 + C3.p256.b) %
        RV32.p256 := by
  obtain ⟨-, -, -, he⟩ := hg
  have hYY := p2fm_mont (A := gsVal M bp 0x21 * 2 ^ 256 % RV32.p256) (B := gsVal M bp 0x21 * 2 ^ 256 % RV32.p256)
    (a := gsVal M bp 0x21) (b := gsVal M bp 0x21) (Nat.mod_mod _ _) (Nat.mod_mod _ _)
  rw [he, gsAlpha_mont] at hYY
  rw [← cancelR hYY]
  exact add_mod_congr (add_mod_congr (Nat.mod_mul_mod _ _ _).symm)

/-- The key the check accepts decodes to its coordinates. -/
theorem gs_decode {M : Word → BitVec 8} {bp : Word} (hg : GsOk M bp) :
    C3.p256.decodePoint (memBytes M bp 65) = some (gsVal M bp 1, gsVal M bp 0x21) := by
  have heq := gs_eq hg
  obtain ⟨h4, hx, hy, -⟩ := hg
  have hlen := memBytes_length M bp 65
  have hx' : beNat (((memBytes M bp 65).drop 1).take 32) = gsVal M bp 1 := by
    rw [memBytes_dropK' M bp (by decide), memBytes_take' (by decide)]
    rfl
  have hy' : beNat ((memBytes M bp 65).drop (1 + 32)) = gsVal M bp 0x21 := by
    rw [memBytes_dropK' M bp (by decide)]
    rfl
  have hhead : (memBytes M bp 65).head? = some 0x04 := by
    rw [show 65 = 64 + 1 from rfl, memBytes_succ, List.head?_cons, h4]
    rfl
  unfold Curve.decodePoint
  simp only [Option.bind_eq_bind]
  rw [hlen, hhead, show C3.p256.size = 32 from rfl, show (65 == 1 + 2 * 32 && some 4 == some 4) = true from rfl,
    require_true, Option.bind_some, hx', hy', show C3.p256.p = RV32.p256 from rfl,
    show C3.p256.a = RV32.p256 - 3 from rfl, decide_eq_true hx, decide_eq_true hy, heq, beq_iff_eq.mpr rfl]
  rfl

/-- The key the check accepts is on the curve. -/
theorem gs_onC {M : Word → BitVec 8} {bp : Word} (hg : GsOk M bp) :
    EC.OnC C3.p256 (some (gsVal M bp 1, gsVal M bp 0x21)) := by
  have heq := gs_eq hg
  obtain ⟨-, hx, hy, -⟩ := hg
  have e : (gsVal M bp 0x21 * gsVal M bp 0x21) % RV32.p256 =
      (gsVal M bp 1 * gsVal M bp 1 * gsVal M bp 1 + (RV32.p256 - 3) * gsVal M bp 1 + C3.p256.b) % RV32.p256 := by
    rw [heq]
    exact add_mod_congr (add_mod_congr (Nat.mod_mul_mod _ _ _))
  rw [show RV32.p256 - 3 = C3.p256.a from rfl, ← p256_p] at e
  rw [← p256_p] at hx hy
  refine ⟨hx, hy, ?_⟩
  have := MEq.natCast.mpr e
  rw [Int.natCast_mul, Int.natCast_add, Int.natCast_add, Int.natCast_mul, Int.natCast_mul, Int.natCast_mul] at this
  exact this

theorem p2fm_zero_one : p2fm 0 1 = 0 := by unfold p2fm; simp only [Nat.zero_mul, Nat.zero_mod]

theorem b32_length (L : Bytes) : (b32 L).length = 32 := by unfold b32; rw [List.length_map, List.length_range]

set_option maxHeartbeats 8000000 in
set_option exponentiation.threshold 600 in
/-- **The P-256 check refines `p256Verify`**, for the curve's group law
(`IsPrime`, `AddClosed`, `AddAssoc`), the compiled formulas
(`P256AddOk`, `P256DblOk`) and scalar product (`P256PsmOk`), and the
image's constants in `M`. -/
theorem p256_model {M : Word → BitVec 8} (hp : IsPrime C3.p256.p) (hc : EC.AddClosed C3.p256)
    (ha : EC.AddAssoc C3.p256) (hadd : P256AddOk) (hdbl : P256DblOk) (hpsm : P256PsmOk) (K : P256Consts M) :
    SvP256Model' M := by
  intro bp dg r s h
  obtain ⟨⟨-, ⟨hgs, hrn, hsn, hr0, hs0, -⟩⟩, σd, σf, Dv, Fv, hσd, hσf, hf, hd, ⟨hFv, -⟩, stm, hml,
    τd, τf, Dz, Fz, hτd, hτf, hzf, hzd, ⟨hfin, -⟩⟩ := h
  -- The inverse of `s`.
  have hSf : p256Sf M s = ivLoop8 C3.p256.n 10 ⟨1, C3.p256.n, beNat (b32 s), 0, 1, 0x24F⟩ := by
    unfold p256Sf p256Iv0; rw [K.n, K.one]; rfl
  rw [hSf] at hf hd
  rw [K.one] at hFv
  obtain ⟨hw, hwn⟩ := ivLoop8_inv (N := C3.p256.n) (x := beNat (b32 s)) (by decide) (by decide) (by decide)
    (by decide) (Nat.lt_trans hsn (by decide)) hσd hσf hf hd hFv
  have hinv := modInv_unique (by decide) hwn hw
  -- The scalars.
  rw [K.n, K.gx, K.gy, K.gz, K.mone, ← p256_p] at hml
  have he : beNat (memBytes M dg 32) % C3.p256.n < C3.p256.n := Nat.mod_lt _ (by decide)
  rw [hpsm _ (Nat.mul_lt_mul'' he hwn), hpsm _ (Nat.mul_lt_mul'' hrn hwn)] at hml
  generalize hU1 : beNat (memBytes M dg 32) % C3.p256.n * normVal8 σd σf Dv C3.p256.n % C3.p256.n = u1 at hml
  generalize hU2 : beNat (b32 r) * normVal8 σd σf Dv C3.p256.n % C3.p256.n = u2 at hml
  have hu1 : u1 < 2 ^ 0x100 := hU1 ▸ Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have hu2 : u2 < 2 ^ 0x100 := hU2 ▸ Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  -- The digits.
  have hl1 := wnafGo_length hu1 0x101 0 0 (Nat.zero_le _) (Nat.zero_le _)
  have hl2 := wnafGo_length hu2 0x101 0 0 (Nat.zero_le _) (Nat.zero_le _)
  generalize hLm : max (wnafGo u1 0x100 0x101 0 0).length (wnafGo u2 0x100 0x101 0 0).length = Lm at hml
  have hLm1 : (wnafGo u1 0x100 0x101 0 0).length ≤ Lm := hLm ▸ Nat.le_max_left _ _
  have hLm2 : (wnafGo u2 0x100 0x101 0 0).length ≤ Lm := hLm ▸ Nat.le_max_right _ _
  have hLmK : Lm ≤ 0x101 := hLm ▸ Nat.max_le.mpr ⟨hl1, hl2⟩
  have hd1 : dsum (wnafBytes (wnafGo u1 0x100 0x101 0 0) 0x101) Lm = u1 := wnaf_dsum hu1 hLm1 hLmK
  have hd2 : dsum (wnafBytes (wnafGo u2 0x100 0x101 0 0) 0x101) Lm = u2 := wnaf_dsum hu2 hLm2 hLmK
  -- The main loop.
  have hG : EC.OnC C3.p256 (some (C3.p256.gx, C3.p256.gy)) := by unfold EC.OnC MEq; decide
  have hQ := gs_onC hgs
  have L := p256Ops hadd hdbl
  have hgx : gsVal M bp 1 < C3.p256.p := p256_p ▸ hgs.2.1
  have hgy : gsVal M bp 0x21 < C3.p256.p := p256_p ▸ hgs.2.2.1
  have hT0 := tbl_rep hp hc ha L (T := tbl2 (C3.p256.gx * 2 ^ 256 % C3.p256.p, C3.p256.gy * 2 ^ 256 % C3.p256.p,
    2 ^ 256 % C3.p256.p)) (g := ⟨_, hG⟩) rfl (fun _ => rfl) (mont_rep (by decide) (by decide))
  have hT1 := tbl_rep hp hc ha L (T := tbl2 (gsVal M bp 1 * 2 ^ 256 % C3.p256.p,
    gsVal M bp 0x21 * 2 ^ 256 % C3.p256.p, 2 ^ 256 % C3.p256.p)) (g := ⟨_, hQ⟩) rfl (fun _ => rfl)
    (mont_rep hgx hgy)
  obtain ⟨st', hst, hrep, -⟩ := gLoop_spec hp hc ha L (K := 0x101) (fun j _ => hT0 j) (fun j _ => hT1 j)
    (wnafBytes_digOk (wnafGo_dig _ _ _ (Nat.zero_le _)) 0x101)
    (wnafBytes_digOk (wnafGo_dig _ _ _ (Nat.zero_le _)) 0x101) Lm hLmK (idPt2, false) 0 0 idPt2_rep (fun _ => rfl)
  unfold mlMain2 at hml
  rw [mlLoop2_eq, hst] at hml
  have hst' := Option.some.inj hml
  subst hst'
  simp only [Int.zero_mul, Int.zero_add] at hrep
  rw [hd1, hd2] at hrep
  have hlc : (lc hp hc ha ⟨_, hG⟩ ⟨_, hQ⟩ (u1 : Int) (u2 : Int)).1 =
      C3.p256.add (C3.p256.mul u1 (some (C3.p256.gx, C3.p256.gy)))
        (C3.p256.mul u2 (some (gsVal M bp 1, gsVal M bp 0x21))) :=
    by rw [EC.mul_eq hp hc ha ⟨_, hG⟩ u1, EC.mul_eq hp hc ha ⟨_, hQ⟩ u2]; rfl
  rw [hlc] at hrep
  -- The affine `x` and the comparison.
  obtain ⟨⟨X, Y, Z⟩, fl⟩ := st'
  dsimp only at hrep hfin hzf hzd
  rw [K.idx, K.one, K.p] at hfin
  have hZp : Z < C3.p256.p := by
    rcases hsum : C3.p256.add (C3.p256.mul u1 (some (C3.p256.gx, C3.p256.gy)))
      (C3.p256.mul u2 (some (gsVal M bp 1, gsVal M bp 0x21))) with _ | ⟨x, y⟩ <;> rw [hsum] at hrep
    · exact hrep.2.2.1
    · exact hrep.2.2.1
  by_cases hZ : Z = 0
  · rw [ite_eq_left hZ] at hfin
    by_cases hF : Fz = 1
    · rw [ite_eq_left hF] at hfin
      simp +decide only [↓reduceIte] at hfin
      rw [p2fm_zero_one, Nat.zero_mod] at hfin
      exact absurd hfin hr0
    · rw [ite_eq_right hF] at hfin
      simp +decide only [↓reduceIte] at hfin
      rw [p2fm_zero_one, Nat.zero_mod] at hfin
      exact absurd hfin hr0
  rw [ite_eq_right hZ] at hfin
  by_cases hF : Fz ≠ 1
  · rw [ite_eq_right hF] at hfin
    simp +decide only [↓reduceIte] at hfin
    rw [p2fm_zero_one, Nat.zero_mod] at hfin
    exact absurd hfin hr0
  have hF : Fz = 1 := Decidable.of_not_not hF
  rw [ite_eq_left hF] at hfin
  simp +decide only [↓reduceIte] at hfin
  have hSz : p256Sz M Z = zvLoop C3.p256.p 10 ⟨1, C3.p256.p, Z, 0, ((2 ^ 512 % C3.p256.p : Nat) : Int), 0x24F⟩ := by
    unfold p256Sz p256Zv0; rw [K.p, K.r2]
  rw [hSz] at hzf hzd
  obtain ⟨hz, -⟩ := zvLoop_inv (P := C3.p256.p) (x := Z) (e0 := 2 ^ 512 % C3.p256.p) (by decide) (by decide)
    (by decide) (Nat.lt_trans hZp (by decide)) (Nat.mod_lt _ (by decide)) hτd hτf hzf hzd hF
  rcases hsum : C3.p256.add (C3.p256.mul u1 (some (C3.p256.gx, C3.p256.gy)))
    (C3.p256.mul u2 (some (gsVal M bp 1, gsVal M bp 0x21))) with _ | ⟨x, y⟩ <;> rw [hsum] at hrep
  · exact absurd hrep.2.2.2.2.2 hZ
  rw [p2fm_affine_x hrep hz] at hfin
  -- The specification.
  unfold p256Verify Curve.verify
  rw [gs_decode hgs]
  dsimp only
  rw [hinv, show C3.p256.digestScalar (memBytes M dg 32) = beNat (memBytes M dg 32) % C3.p256.n by
    unfold Curve.digestScalar; rw [List.take_of_length_le (by rw [memBytes_length]; decide)], hU1, hU2, hsum]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, b32_length]
  exact ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, by omega⟩, hrn⟩, by omega⟩, hsn⟩, hfin.symm⟩

end C3.Models
