import C3BootProofs.Proofs.Ed25519VerifyC
import C3BootProofs.Proofs.KeySet

/-!
# `c3_verify::keys::check_signatures`
-/

namespace C3.RV32

open C3.Image

/-- `M` and `M'` agree on `ed25519_verify`'s read-only constants. -/
def RoAgree (M M' : Word → BitVec 8) : Prop :=
  ∀ i, i < 0x1400 → M (BitVec.ofNat 32 (0x3FCC4000 + i)) = M' (BitVec.ofNat 32 (0x3FCC4000 + i))

theorem ro_mb {M M' : Word → BitVec 8} (h : RoAgree M M') (A n : Nat) (h1 : 0x3FCC4000 ≤ A)
    (h2 : A + n ≤ 0x3FCC5400) : memBytes M (BitVec.ofNat 32 A) n = memBytes M' (BitVec.ofNat 32 A) n :=
  memBytes_eq_of fun i hi => by
    rw [ofNat_add_ofNat, show A + i = 0x3FCC4000 + (A - 0x3FCC4000 + i) by omega]
    exact h (A - 0x3FCC4000 + i) (by omega)

theorem ro_ld {M M' : Word → BitVec 8} (h : RoAgree M M') (A : Nat) (h1 : 0x3FCC4000 ≤ A)
    (h2 : A + 4 ≤ 0x3FCC5400) : memLoad32 M (BitVec.ofNat 32 A) = memLoad32 M' (BitVec.ofNat 32 A) :=
  (memLoad32_congr fun j hj => by
    rw [ofNat_add_ofNat, show A + j = 0x3FCC4000 + (A - 0x3FCC4000 + j) by omega]
    exact h (A - 0x3FCC4000 + j) (by omega))

theorem ro_feW {M M' : Word → BitVec 8} (h : RoAgree M M') (A : Nat) (h1 : 0x3FCC4000 ≤ A)
    (h2 : A + 40 ≤ 0x3FCC5400) : feW M (BitVec.ofNat 32 A) = feW M' (BitVec.ofNat 32 A) :=
  (feW_eq2 fun i hi => by rw [ofNat_add_ofNat]; exact (ro_ld h (A + 4 * i) (by omega) (by omega)).symm).symm

theorem ro_smm {M M' : Word → BitVec 8} (h : RoAgree M M') (A : Nat) (h1 : 0x3FCC4000 ≤ A)
    (h2 : A + 36 ≤ 0x3FCC5400) : smmIn M (BitVec.ofNat 32 A) = smmIn M' (BitVec.ofNat 32 A) := by
  funext i; unfold smmIn limbAt
  split
  · rw [ofNat_add_ofNat, ro_ld h (A + 4 * i) (by omega) (by omega)]
  · rfl

theorem ro_pt {M M' : Word → BitVec 8} (h : RoAgree M M') (A : Nat) (h1 : 0x3FCC4000 ≤ A)
    (h2 : A + 160 ≤ 0x3FCC5400) : ptAt M (BitVec.ofNat 32 A) = ptAt M' (BitVec.ofNat 32 A) := by
  unfold ptAt
  rw [ofNat_add_ofNat, ofNat_add_ofNat, ofNat_add_ofNat, ro_feW h A h1 (by omega), ro_feW h (A + 40) (by omega) (by omega),
    ro_feW h (A + 80) (by omega) (by omega), ro_feW h (A + 120) (by omega) (by omega)]

theorem leAcc_congr' {M M' : Word → BitVec 8} {b : Word} :
    ∀ n, (∀ j, j < n → M (b + BitVec.ofNat 32 j) = M' (b + BitVec.ofNat 32 j)) → leAcc M b n = leAcc M' b n
  | 0, _ => rfl
  | n + 1, h => by
    show leAcc M b n + (M (b + BitVec.ofNat 32 n)).toNat * 256 ^ n = leAcc M' b n + (M' (b + BitVec.ofNat 32 n)).toNat * 256 ^ n
    rw [leAcc_congr' n fun j hj => h j (by omega), h n (by omega)]

set_option maxRecDepth 20000 in
theorem evSpecA_congr {M M' : Word → BitVec 8} {pk sig : Word} (hro : RoAgree M M')
    (hpk : ∀ i, i < 32 → M (pk + BitVec.ofNat 32 i) = M' (pk + BitVec.ofNat 32 i))
    (hsig : ∀ i, i < 64 → M (sig + BitVec.ofNat 32 i) = M' (sig + BitVec.ofNat 32 i)) :
    evSpecA M pk sig = evSpecA M' pk sig := by
  have mpk : memBytes M pk 32 = memBytes M' pk 32 := memBytes_eq_of hpk
  have msig : memBytes M sig 32 = memBytes M' sig 32 := memBytes_eq_of fun i hi => hsig i (by omega)
  have msig2 : memBytes M (sig + BitVec.ofNat 32 32) 32 = memBytes M' (sig + BitVec.ofNat 32 32) 32 :=
    memBytes_eq_of fun i hi => by rw [add_ofNat_assoc]; exact hsig _ (by omega)
  have b63 : M (sig + BitVec.ofNat 32 63) = M' (sig + BitVec.ofNat 32 63) := hsig 63 (by omega)
  have sw : sWords M sig = sWords M' sig := by
    funext i; unfold sWords
    split
    · next hi =>
      rw [leAcc_congr' (M := M) (M' := M') (b := sig + BitVec.ofNat 32 (32 + 4 * i)) 4 fun j hj => by
        rw [add_ofNat_assoc]; exact hsig (32 + 4 * i + j) (by omega)]
    · rfl
  have e1 := ro_mb hro 0x3FCC4308 32 (by omega) (by omega)
  have e2 := ro_mb hro 0x3FCC4328 32 (by omega) (by omega)
  have e3 := ro_mb hro 0x3FCC42E8 32 (by omega) (by omega)
  have e4 := ro_mb hro 0x3FCC4388 32 (by omega) (by omega)
  have f1 := ro_feW hro edOneAddress (by decide) (by decide)
  have f2 := ro_feW hro edDAddress (by decide) (by decide)
  have f3 := ro_feW hro edSqrtM1Address (by decide) (by decide)
  have lt : evLt M sig = evLt M' sig := by unfold evLt; rw [msig2, e1]
  have pkc : ∀ b, evPk M b = evPk M' b := fun b => by unfold evPk; rw [e2, e3, e4, f1, f2, f3]
  have dc : ∀ b, evDec M b = evDec M' b := fun b => by unfold evDec; rw [f1, f2, f3]
  have so : evSOk M sig = evSOk M' sig := by unfold evSOk; rw [msig2, sw, b63]
  have ch : evChecks M pk sig = evChecks M' pk sig := by unfold evChecks; rw [lt, pkc, pkc, mpk, msig]
  unfold evSpecA
  simp only [ch, dc, so, mpk, msig]

set_option maxRecDepth 20000 in
/-- `ed25519_verify`'s result depends only on its constants, the key, the
signature, and the message. -/
theorem evSpec_congr {M M' : Word → BitVec 8} {pk sig msg : Word} {len : Nat} (hro : RoAgree M M')
    (hpk : ∀ i, i < 32 → M (pk + BitVec.ofNat 32 i) = M' (pk + BitVec.ofNat 32 i))
    (hsig : ∀ i, i < 64 → M (sig + BitVec.ofNat 32 i) = M' (sig + BitVec.ofNat 32 i))
    (hmsg : ∀ i, i < len → M (msg + BitVec.ofNat 32 i) = M' (msg + BitVec.ofNat 32 i)) :
    evSpec M pk sig msg len = evSpec M' pk sig msg len := by
  have mpk : memBytes M pk 32 = memBytes M' pk 32 := memBytes_eq_of hpk
  have msig : memBytes M sig 32 = memBytes M' sig 32 := memBytes_eq_of fun i hi => hsig i (by omega)
  have msig2 : memBytes M (sig + BitVec.ofNat 32 32) 32 = memBytes M' (sig + BitVec.ofNat 32 32) 32 :=
    memBytes_eq_of fun i hi => by rw [add_ofNat_assoc]; exact hsig _ (by omega)
  have mmsg : memBytes M msg len = memBytes M' msg len := memBytes_eq_of hmsg
  have f4 : feW M apnD = feW M' apnD := ro_feW hro 0x3FCC4A2C (by omega) (by omega)
  have f5 := ro_feW hro 0x3FCC4948 (by omega) (by omega)
  have s1 := ro_smm hro 0x3FCC49E4 (by omega) (by omega)
  have s2 := ro_smm hro 0x3FCC49C0 (by omega) (by omega)
  have p1 := ro_pt hro 0x3FCC4A54 (by omega) (by omega)
  unfold evSpec
  simp only [evSpecA_congr hro hpk hsig, s1, s2, msig, mpk, mmsg, msig2, f4, p1, f5]

end C3.RV32

