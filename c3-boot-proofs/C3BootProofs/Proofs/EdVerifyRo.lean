import C3BootProofs.Proofs.Ed25519VerifyC
import C3BootProofs.Image.BootloaderData5
import C3BootProofs.Image.BootloaderData7

/-!
# `ed25519_verify` and the read-only data

`ed25519_verify`'s result and its environment depend only on the image's
read-only constants, the key, the signature, and the message. A caller that
changes other memory between two states keeps the same result.
-/

namespace C3.RV32

open C3.Image

/-- `M` and `M'` agree on `ed25519_verify`'s read-only constants. -/
def RoAgree (M M' : Word → BitVec 8) : Prop :=
  ∀ i, i < (img% roWindowSize) → M (BitVec.ofNat 32 ((img% roWindowAddress) + i)) = M' (BitVec.ofNat 32 ((img% roWindowAddress) + i))

theorem ro_mb {M M' : Word → BitVec 8} (h : RoAgree M M') (A n : Nat) (h1 : (img% roWindowAddress) ≤ A)
    (h2 : A + n ≤ 0x3FCC5400) : memBytes M (BitVec.ofNat 32 A) n = memBytes M' (BitVec.ofNat 32 A) n :=
  memBytes_eq_of fun i hi => by
    rw [ofNat_add_ofNat, show A + i = (img% roWindowAddress) + (A - (img% roWindowAddress) + i) by omega]
    exact h (A - (img% roWindowAddress) + i) (by omega)

theorem ro_ld {M M' : Word → BitVec 8} (h : RoAgree M M') (A : Nat) (h1 : (img% roWindowAddress) ≤ A)
    (h2 : A + 4 ≤ 0x3FCC5400) : memLoad32 M (BitVec.ofNat 32 A) = memLoad32 M' (BitVec.ofNat 32 A) :=
  (memLoad32_congr fun j hj => by
    rw [ofNat_add_ofNat, show A + j = (img% roWindowAddress) + (A - (img% roWindowAddress) + j) by omega]
    exact h (A - (img% roWindowAddress) + j) (by omega))

theorem ro_feW {M M' : Word → BitVec 8} (h : RoAgree M M') (A : Nat) (h1 : (img% roWindowAddress) ≤ A)
    (h2 : A + 40 ≤ 0x3FCC5400) : feW M (BitVec.ofNat 32 A) = feW M' (BitVec.ofNat 32 A) :=
  (feW_eq2 fun i hi => by rw [ofNat_add_ofNat]; exact (ro_ld h (A + 4 * i) (by omega) (by omega)).symm).symm

theorem ro_smm {M M' : Word → BitVec 8} (h : RoAgree M M') (A : Nat) (h1 : (img% roWindowAddress) ≤ A)
    (h2 : A + 36 ≤ 0x3FCC5400) : smmIn M (BitVec.ofNat 32 A) = smmIn M' (BitVec.ofNat 32 A) := by
  funext i; unfold smmIn limbAt
  split
  · rw [ofNat_add_ofNat, ro_ld h (A + 4 * i) (by omega) (by omega)]
  · rfl

theorem ro_pt {M M' : Word → BitVec 8} (h : RoAgree M M') (A : Nat) (h1 : (img% roWindowAddress) ≤ A)
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
  have e1 := ro_mb hro (img% edOrderAddress) 32 (by omega) (by omega)
  have e2 := ro_mb hro (img% edPrimeAddress) 32 (by omega) (by omega)
  have e3 := ro_mb hro (img% p256OneAddress) 32 (by omega) (by omega)
  have e4 := ro_mb hro (img% edPm1Address) 32 (by omega) (by omega)
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
  have f4 : feW M apnD = feW M' apnD := ro_feW hro (img% edwardsD2Address) (by omega) (by omega)
  have f5 := ro_feW hro (img% edOneAddress) (by omega) (by omega)
  have s1 := ro_smm hro (img% edMontRAddress) (by omega) (by omega)
  have s2 := ro_smm hro (img% edMontRRAddress) (by omega) (by omega)
  have p1 := ro_pt hro (img% edBaseAddress) (by omega) (by omega)
  unfold evSpec
  simp only [evSpecA_congr hro hpk hsig, s1, s2, msig, mpk, mmsg, msig2, f4, p1, f5]

set_option maxRecDepth 200000 in
/-- `EvEnv` survives any change that keeps the code and the read-only data. -/
theorem EvEnv.congr {M M' : Word → BitVec 8} (E : EvEnv M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x)
    (hro : RoAgree M' M) : EvEnv M' := by
  have roC : ∀ {A : Nat} {code : List Nat}, (img% roWindowAddress) ≤ A → A + code.length ≤ 0x3FCC5400 →
      CodeIn M (BitVec.ofNat 32 A) code → CodeIn M' (BitVec.ofNat 32 A) code := by
    intro A code h1 h2 hc i hi
    have := hro (A - (img% roWindowAddress) + i) (by omega)
    rw [show (img% roWindowAddress) + (A - (img% roWindowAddress) + i) = A + i by omega] at this
    rw [ofNat_add_ofNat, this, ← ofNat_add_ofNat]; exact hc i hi
  exact ⟨E.pk.hi h (ro_feW hro edOneAddress (by decide) (by decide)), E.cod.hi h (by decide) (by decide),
    E.s29s.hi h (by decide) (by decide), E.s29i.hi h (by decide) (by decide), E.s29im.hi h (by decide) (by decide),
    roC (by decide) (by decide) E.sL, E.s29p.hi h (by decide) (by decide), E.s5u.hi h (by decide) (by decide),
    E.s5blk.hi h (by decide) (by decide), E.s5c.hi h (by decide) (by decide), E.rfi.hi h (by decide) (by decide),
    roC (by decide) (by decide) E.s5k, E.s5fb.hi h (by decide) (by decide), E.s5a.hi h (by decide) (by decide),
    E.za64.hi h (by decide) (by decide), E.smm.hi h (by decide) (by decide), E.naf.hi h (by decide) (by decide),
    E.lsh.hi h (by decide) (by decide), E.ash.hi h (by decide) (by decide), E.ntf.hi h (by decide) (by decide),
    E.apn.hi h (by decide) (by decide), E.ean.hi h (by decide) (by decide), E.esn.hi h (by decide) (by decide),
    E.nsel.hi h (by decide) (by decide), E.panic.hi' h⟩

theorem s5Hv_ro {M M' : Word → BitVec 8} (hro : RoAgree M M') :
    s5Hv M (BitVec.ofNat 32 (img% sha512IVAddress)) = s5Hv M' (BitVec.ofNat 32 (img% sha512IVAddress)) := by
  have L : ∀ c, c + 4 ≤ 0x40 → memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + BitVec.ofNat 32 c) =
      memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + BitVec.ofNat 32 c) := fun c hc => by
    rw [ofNat_add_ofNat]; exact ro_ld hro _ (by omega) (by omega)
  have L0 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0x0) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0x0) :=
    L 0 (by omega)
  have L4 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0x4) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0x4) :=
    L 4 (by omega)
  have L8 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0x8) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0x8) :=
    L 8 (by omega)
  have L12 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0xC) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0xC) :=
    L 12 (by omega)
  have L16 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0x10) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0x10) :=
    L 16 (by omega)
  have L20 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0x14) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0x14) :=
    L 20 (by omega)
  have L24 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0x18) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0x18) :=
    L 24 (by omega)
  have L28 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0x1C) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0x1C) :=
    L 28 (by omega)
  have L32 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0x20) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0x20) :=
    L 32 (by omega)
  have L36 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0x24) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0x24) :=
    L 36 (by omega)
  have L40 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0x28) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0x28) :=
    L 40 (by omega)
  have L44 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0x2C) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0x2C) :=
    L 44 (by omega)
  have L48 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0x30) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0x30) :=
    L 48 (by omega)
  have L52 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0x34) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0x34) :=
    L 52 (by omega)
  have L56 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0x38) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0x38) :=
    L 56 (by omega)
  have L60 : memLoad32 M (BitVec.ofNat 32 (img% sha512IVAddress) + 0x3C) = memLoad32 M' (BitVec.ofNat 32 (img% sha512IVAddress) + 0x3C) :=
    L 60 (by omega)
  unfold s5Hv
  rw [L0, L4, L8, L12, L16, L20, L24, L28, L32, L36, L40, L44, L48, L52, L56, L60]

end C3.RV32
