import C3BootProofs.Proofs.Ed25519VerifyC
import C3BootProofs.Proofs.KeySet
import C3BootProofs.Image.BootloaderData5
import C3BootProofs.Image.BootloaderData7

/-!
# `c3_verify::keys::check_signatures`

`check_signatures(sigs, keys, prefix, payload, buf)` builds the signed
message in `buf`: the 21-byte prefix, a zero byte, and the payload of at
most 0x1002 bytes (else error 0x13). The signatures are 65 bytes each, at
least two (else `OutOfRange`, 5): a key index, strictly increasing and below
the number of keys (else 0xF), and an Ed25519 signature that
`ed25519_verify` must accept for that key and the message (else 0x10). It
returns 0xFF when every signature passes.
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

abbrev CSG : Word := BitVec.ofNat 32 checkSignaturesAddress

theorem upd_zero_cs (g : Fin 32 → Word) (r : Fin 32) (v : Word) : upd g r v x0 = 0 := rfl

/-- The message `check_signatures` builds in `buf`. -/
def csMsgMem (M : Word → BitVec 8) (buf pre pay : Word) (plen : Nat) : Word → BitVec 8 :=
  copyBytes (memStore8 (copyBytes M buf pre 21) (buf + 0x15) 0) (buf + 0x16) pay plen

/-- The result of checking `k` signatures from `s`, the next key index at least `last`. -/
def csLoop (M : Word → BitVec 8) (keys buf : Word) (mlen nkeys : Nat) : Word → Nat → Nat → BitVec 8
  | _, 0, _ => 0xFF
  | s, k + 1, last =>
    if (M s).toNat < last ∨ nkeys ≤ (M s).toNat then 0xF
    else if evSpec M (keys + BitVec.ofNat 32 (32 * (M s).toNat)) (s + 1) buf mlen then
      csLoop M keys buf mlen nkeys (s + 0x41) k ((M s).toNat + 1)
    else 0x10

/-- `check_signatures`'s result. -/
def csResult (M : Word → BitVec 8) (sigs slen keys klen pre pay plen buf : Word) : BitVec 8 :=
  if slen.toNat < 0x82 ∨ slen.toNat % 65 ≠ 0 then 5
  else if 0x1002 < plen.toNat then 0x13
  else csLoop (csMsgMem M buf pre pay plen.toNat) keys buf (plen.toNat + 0x16) (klen.toNat / 32) sigs
    (slen.toNat / 65) 0

/-- Memory after `check_signatures` returns, outside the stack it uses. -/
def csMem (M : Word → BitVec 8) (slen pre pay plen buf : Word) : Word → BitVec 8 :=
  if slen.toNat < 0x82 ∨ slen.toNat % 65 ≠ 0 then M
  else if 0x1002 < plen.toNat then M
  else csMsgMem M buf pre pay plen.toNat

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

set_option maxRecDepth 10000

theorem csg_at_0 : fetchRel checkSignaturesCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem csg_at_2 : fetchRel checkSignaturesCode 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem csg_at_4 : fetchRel checkSignaturesCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem csg_at_6 : fetchRel checkSignaturesCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem csg_at_8 : fetchRel checkSignaturesCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem csg_at_a : fetchRel checkSignaturesCode 0xA = some (.store .sw sp (19 : Fin 32) 0x1C, 2) := by decide
theorem csg_at_c : fetchRel checkSignaturesCode 0xC = some (.store .sw sp (20 : Fin 32) 0x18, 2) := by decide
theorem csg_at_e : fetchRel checkSignaturesCode 0xE = some (.store .sw sp (21 : Fin 32) 0x14, 2) := by decide
theorem csg_at_10 : fetchRel checkSignaturesCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x10, 2) := by decide
theorem csg_at_12 : fetchRel checkSignaturesCode 0x12 = some (.store .sw sp (23 : Fin 32) 0xC, 2) := by decide
theorem csg_at_14 : fetchRel checkSignaturesCode 0x14 = some (.store .sw sp (24 : Fin 32) 0x8, 2) := by decide
theorem csg_at_16 : fetchRel checkSignaturesCode 0x16 = some (.alu .add (18 : Fin 32) x0 a2, 2) := by decide
theorem csg_at_18 : fetchRel checkSignaturesCode 0x18 = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem csg_at_1a : fetchRel checkSignaturesCode 0x1A = some (.aluImm .add a2 x0 0x82, 4) := by decide
theorem csg_at_1e : fetchRel checkSignaturesCode 0x1E = some (.aluImm .add a0 x0 0x5, 2) := by decide
theorem csg_at_20 : fetchRel checkSignaturesCode 0x20 = some (.branch .bltu a1 a2 0x98, 4) := by decide
theorem csg_at_24 : fetchRel checkSignaturesCode 0x24 = some (.aluImm .add a2 x0 0x41, 4) := by decide
theorem csg_at_28 : fetchRel checkSignaturesCode 0x28 = some (.alu .divu (24 : Fin 32) a1 a2, 4) := by decide
theorem csg_at_2c : fetchRel checkSignaturesCode 0x2C = some (.aluImm .sll a2 (24 : Fin 32) 0x6, 4) := by decide
theorem csg_at_30 : fetchRel checkSignaturesCode 0x30 = some (.alu .add (24 : Fin 32) (24 : Fin 32) a2, 2) := by decide
theorem csg_at_32 : fetchRel checkSignaturesCode 0x32 = some (.alu .sub a1 a1 (24 : Fin 32), 4) := by decide
theorem csg_at_36 : fetchRel checkSignaturesCode 0x36 = some (.branch .bne a1 x0 0x82, 2) := by decide
theorem csg_at_38 : fetchRel checkSignaturesCode 0x38 = some (.alu .add (21 : Fin 32) x0 a6, 2) := by decide
theorem csg_at_3a : fetchRel checkSignaturesCode 0x3A = some (.lui a0 0x1000, 2) := by decide
theorem csg_at_3c : fetchRel checkSignaturesCode 0x3C = some (.aluImm .add a0 a0 0x2, 2) := by decide
theorem csg_at_3e : fetchRel checkSignaturesCode 0x3E = some (.branch .bgeu a0 a6 0x8, 4) := by decide
theorem csg_at_42 : fetchRel checkSignaturesCode 0x42 = some (.aluImm .add a0 x0 0x13, 2) := by decide
theorem csg_at_44 : fetchRel checkSignaturesCode 0x44 = some (.jal x0 0x74, 2) := by decide
theorem csg_at_46 : fetchRel checkSignaturesCode 0x46 = some (.alu .add (23 : Fin 32) x0 (17 : Fin 32), 2) := by decide
theorem csg_at_48 : fetchRel checkSignaturesCode 0x48 = some (.alu .add (22 : Fin 32) x0 a5, 2) := by decide
theorem csg_at_4a : fetchRel checkSignaturesCode 0x4A = some (.alu .add (20 : Fin 32) x0 a3, 2) := by decide
theorem csg_at_4c : fetchRel checkSignaturesCode 0x4C = some (.aluImm .add (19 : Fin 32) (21 : Fin 32) 0x16, 4) := by decide
theorem csg_at_50 : fetchRel checkSignaturesCode 0x50 = some (.aluImm .add a2 x0 0x15, 2) := by decide
theorem csg_at_52 : fetchRel checkSignaturesCode 0x52 = some (.alu .add a0 x0 (17 : Fin 32), 2) := by decide
theorem csg_at_54 : fetchRel checkSignaturesCode 0x54 = some (.alu .add a1 x0 a4, 2) := by decide
theorem csg_at_56 : fetchRel checkSignaturesCode 0x56 = some (.auipc ra 0xB000, 4) := by decide
theorem csg_at_5a : fetchRel checkSignaturesCode 0x5A = some (.jalr ra ra 0x660, 4) := by decide
theorem csg_at_5e : fetchRel checkSignaturesCode 0x5E = some (.aluImm .add a0 (23 : Fin 32) 0x16, 4) := by decide
theorem csg_at_62 : fetchRel checkSignaturesCode 0x62 = some (.store .sb (23 : Fin 32) x0 0x15, 4) := by decide
theorem csg_at_66 : fetchRel checkSignaturesCode 0x66 = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem csg_at_68 : fetchRel checkSignaturesCode 0x68 = some (.alu .add a2 x0 (22 : Fin 32), 2) := by decide
theorem csg_at_6a : fetchRel checkSignaturesCode 0x6A = some (.alu .add a3 x0 (21 : Fin 32), 2) := by decide
theorem csg_at_6c : fetchRel checkSignaturesCode 0x6C = some (.auipc ra 0x4000, 4) := by decide
theorem csg_at_70 : fetchRel checkSignaturesCode 0x70 = some (.jalr ra ra 0x2C, 4) := by decide
theorem csg_at_74 : fetchRel checkSignaturesCode 0x74 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem csg_at_76 : fetchRel checkSignaturesCode 0x76 = some (.aluImm .srl (20 : Fin 32) (20 : Fin 32) 0x5, 4) := by decide
theorem csg_at_7a : fetchRel checkSignaturesCode 0x7A = some (.branch .beq (24 : Fin 32) x0 0x3A, 4) := by decide
theorem csg_at_7e : fetchRel checkSignaturesCode 0x7E = some (.load .lbu (8 : Fin 32) (9 : Fin 32) 0x0, 4) := by decide
theorem csg_at_82 : fetchRel checkSignaturesCode 0x82 = some (.aluImm .add a0 x0 0xF, 2) := by decide
theorem csg_at_84 : fetchRel checkSignaturesCode 0x84 = some (.branch .bltu (8 : Fin 32) a1 0x34, 4) := by decide
theorem csg_at_88 : fetchRel checkSignaturesCode 0x88 = some (.branch .bgeu (8 : Fin 32) (20 : Fin 32) 0x30, 4) := by decide
theorem csg_at_8c : fetchRel checkSignaturesCode 0x8C = some (.aluImm .add a3 (9 : Fin 32) 0x1, 4) := by decide
theorem csg_at_90 : fetchRel checkSignaturesCode 0x90 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x41, 4) := by decide
theorem csg_at_94 : fetchRel checkSignaturesCode 0x94 = some (.aluImm .sll a0 (8 : Fin 32) 0x5, 4) := by decide
theorem csg_at_98 : fetchRel checkSignaturesCode 0x98 = some (.alu .add a0 a0 (18 : Fin 32), 2) := by decide
theorem csg_at_9a : fetchRel checkSignaturesCode 0x9A = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0xFFFFFFBF, 4) := by decide
theorem csg_at_9e : fetchRel checkSignaturesCode 0x9E = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem csg_at_a0 : fetchRel checkSignaturesCode 0xA0 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem csg_at_a2 : fetchRel checkSignaturesCode 0xA2 = some (.auipc ra 0xFFFFA000, 4) := by decide
theorem csg_at_a6 : fetchRel checkSignaturesCode 0xA6 = some (.jalr ra ra 0xFFFFFFFE, 4) := by decide
theorem csg_at_aa : fetchRel checkSignaturesCode 0xAA = some (.aluImm .add a1 (8 : Fin 32) 0x1, 4) := by decide
theorem csg_at_ae : fetchRel checkSignaturesCode 0xAE = some (.branch .bne a0 x0 0xFFFFFFCC, 2) := by decide
theorem csg_at_b0 : fetchRel checkSignaturesCode 0xB0 = some (.aluImm .add a0 x0 0x10, 2) := by decide
theorem csg_at_b2 : fetchRel checkSignaturesCode 0xB2 = some (.jal x0 0x6, 2) := by decide
theorem csg_at_b4 : fetchRel checkSignaturesCode 0xB4 = some (.aluImm .add a0 x0 0xFF, 4) := by decide
theorem csg_at_b8 : fetchRel checkSignaturesCode 0xB8 = some (.load .lw ra sp 0x2C, 2) := by decide
theorem csg_at_ba : fetchRel checkSignaturesCode 0xBA = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem csg_at_bc : fetchRel checkSignaturesCode 0xBC = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem csg_at_be : fetchRel checkSignaturesCode 0xBE = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem csg_at_c0 : fetchRel checkSignaturesCode 0xC0 = some (.load .lw (19 : Fin 32) sp 0x1C, 2) := by decide
theorem csg_at_c2 : fetchRel checkSignaturesCode 0xC2 = some (.load .lw (20 : Fin 32) sp 0x18, 2) := by decide
theorem csg_at_c4 : fetchRel checkSignaturesCode 0xC4 = some (.load .lw (21 : Fin 32) sp 0x14, 2) := by decide
theorem csg_at_c6 : fetchRel checkSignaturesCode 0xC6 = some (.load .lw (22 : Fin 32) sp 0x10, 2) := by decide
theorem csg_at_c8 : fetchRel checkSignaturesCode 0xC8 = some (.load .lw (23 : Fin 32) sp 0xC, 2) := by decide
theorem csg_at_ca : fetchRel checkSignaturesCode 0xCA = some (.load .lw (24 : Fin 32) sp 0x8, 2) := by decide
theorem csg_at_cc : fetchRel checkSignaturesCode 0xCC = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem csg_at_ce : fetchRel checkSignaturesCode 0xCE = some (.jalr x0 ra 0x0, 2) := by decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 32000000 in
/-- The signature loop, from offset 0x7A to the epilogue with `a0` holding
the result. -/
theorem cs_loop {F keys buf : Word} {mlen nkeys : Nat} {M1 : Word → BitVec 8}
    (E1 : EvEnv M1) (hc1 : CodeIn M1 CSG checkSignaturesCode)
    (hF : F.toNat % 16 = 0) (hlo : 0xA10 ≤ F.toNat) (hhi : F.toNat + 0x16A0 ≤ 0x40000000)
    (sRo : Sep (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize) (evG F) 0x20B0)
    (iv1 : (s5Hv M1 (BitVec.ofNat 32 (img% sha512IVAddress))).toList = Sha512.h0)
    (sK : Sep keys (32 * nkeys) (evG F) 0x20B0) (hkw : keys.toNat + 32 * nkeys < 2 ^ 32)
    (sB : Sep buf mlen (evG F) 0x20B0) (hbw : buf.toNat + mlen ≤ 0x40000000) (hml : mlen < 2 ^ 31) :
    ∀ (k : Nat) (mx : Machine) (s : Word) (last : Nat),
      (∀ j, j < k → Sep (s + BitVec.ofNat 32 (65 * j)) 65 (evG F) 0x20B0) → s.toNat + 65 * k < 2 ^ 32 →
      St mx.mem CSG mx 0x7A (reg mx) → (∀ x, Sep (evG F) 0x20B0 x 1 → mx.mem x = M1 x) →
      reg mx sp = F + BitVec.ofNat 32 0x16A0 → reg mx 24 = BitVec.ofNat 32 (65 * k) → reg mx 9 = s →
      reg mx a1 = BitVec.ofNat 32 last → last ≤ 256 → reg mx 18 = keys → reg mx 19 = BitVec.ofNat 32 mlen →
      reg mx 20 = BitVec.ofNat 32 nkeys → reg mx 23 = buf →
      ∃ mx', Steps mx mx' ∧ St mx'.mem CSG mx' 0xB8 (reg mx') ∧
        reg mx' a0 = (csLoop M1 keys buf mlen nkeys s k last).zeroExtend 32 ∧
        (∀ x, Sep (evG F) 0x20B0 x 1 → mx'.mem x = M1 x) ∧ reg mx' sp = F + BitVec.ofNat 32 0x16A0 ∧
        reg mx' 3 = reg mx 3 ∧ reg mx' 4 = reg mx 4 ∧ reg mx' 25 = reg mx 25 ∧ reg mx' 26 = reg mx 26 ∧
        reg mx' 27 = reg mx 27 := by
  have hGn : (evG F).toNat = F.toNat - 0xA10 := by
    unfold evG; rw [BitVec.toNat_add, show (0xFFFFF5F0 : Word).toNat = 2 ^ 32 - 0xA10 from rfl]; omega
  have hiR : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (evG F) 0x20B0 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have codeX : ∀ (Mx : Word → BitVec 8), (∀ x, Sep (evG F) 0x20B0 x 1 → Mx x = M1 x) →
      CodeIn Mx CSG checkSignaturesCode := fun Mx h i hi => by
    rw [h _ (hiR _ (code_hi (by decide) (by decide) hi))]; exact hc1 i hi
  have roX : ∀ (Mx : Word → BitVec 8), (∀ x, Sep (evG F) 0x20B0 x 1 → Mx x = M1 x) → RoAgree Mx M1 :=
    fun Mx h i hi => h _ (by
      have := (sRo.sub (c := i) (l := 1) hi).symm
      rwa [ofNat_add_ofNat] at this)
  intro k
  induction k with
  | zero =>
    intro mx s last _ _ st hR hsp h24 _ _ _ _ _ _ _
    obtain ⟨n1, d1, u1⟩ := st.taken (codeX _ hR) 0xB4 csg_at_7a (by decide)
      (by rw [h24, show reg mx x0 = 0 from st.zero]; decide)
    obtain ⟨n2, d2, u2⟩ := u1.aluImm (codeX _ hR) csg_at_b4 (off' := 0xB8) (by decide)
    refine ⟨n2, .cons d1 (.single d2), by rw [u2.mem]; exact u2.self, ?_, fun x hx => by rw [u2.mem]; exact hR x hx,
      by rw [u2.regs, updz st.zero (by decide)]; exact hsp, by rw [u2.regs, updz st.zero (by decide)],
      by rw [u2.regs, updz st.zero (by decide)], by rw [u2.regs, updz st.zero (by decide)],
      by rw [u2.regs, updz st.zero (by decide)], by rw [u2.regs, updz st.zero (by decide)]⟩
    rw [u2.regs]; simp +decide only [upd, ite_true, ite_false]; rw [show reg mx x0 = 0 from st.zero]; rfl
  | succ k ih =>
    intro mx s last hsS hsw st hR hsp h24 h9 ha1 hlast h18 h19 h20 h23
    have hz := st.zero
    have hcx := codeX _ hR
    have hS0 : ∀ i, i < 65 → Sep (evG F) 0x20B0 (s + BitVec.ofNat 32 i) 1 := fun i hi => by
      have := ((hsS 0 (by omega)).sub (c := i) (l := 1) hi).symm
      rwa [add_ofNat_assoc, Nat.mul_zero, Nat.zero_add] at this
    have hs0 : Sep (evG F) 0x20B0 s 1 := by have := hS0 0 (by omega); rwa [add_ofNat_zero] at this
    obtain ⟨n1, d1, u1⟩ := st.notTaken hcx 0x7E csg_at_7a (by decide)
      (by
        rw [h24, show reg mx x0 = 0 from hz]
        refine beq_eq_false_iff_ne.mpr fun h => ?_
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact absurd this (by show 65 * (k + 1) ≠ 0; omega))
    obtain ⟨n2, d2, u2⟩ := u1.lbu hcx csg_at_7e (off' := 0x82) (by decide)
    rw [h9, add_lit_zero, hR s hs0] at u2
    obtain ⟨b, hb⟩ : ∃ b, M1 s = b := ⟨_, rfl⟩
    rw [hb] at u2
    have zb : (b.zeroExtend 32 : Word).toNat = b.toNat := by
      show (BitVec.setWidth 32 b).toNat = _; rw [BitVec.toNat_setWidth]; have := b.isLt; omega
    obtain ⟨n3, d3, u3⟩ := u2.aluImm hcx csg_at_82 (off' := 0x84) (by decide)
    have g3 : ∀ r, r ≠ a0 → r ≠ 8 → upd (upd (reg mx) 8 (b.zeroExtend 32)) a0 (aluEval .add (upd (reg mx) 8 (b.zeroExtend 32) x0) 0xF) r = reg mx r :=
      fun r h0 h8 => by rw [updz u2.zero h0, updz hz h8]
    have f38 : upd (upd (reg mx) 8 (b.zeroExtend 32)) a0 (aluEval .add (upd (reg mx) 8 (b.zeroExtend 32) x0) 0xF) 8 = b.zeroExtend 32 := by
      rw [updz u2.zero (by decide)]; simp +decide only [upd, ite_true, ite_false]
    have hb256 := b.isLt
    have err : ∀ (mz : Machine) (fz : Fin 32 → Word), Steps mx mz → St mx.mem CSG mz 0xB8 fz → fz a0 = 0xF →
        fz sp = F + BitVec.ofNat 32 0x16A0 → fz 3 = reg mx 3 → fz 4 = reg mx 4 → fz 25 = reg mx 25 →
        fz 26 = reg mx 26 → fz 27 = reg mx 27 → (b.toNat < last ∨ nkeys ≤ b.toNat) →
        ∃ mx', Steps mx mx' ∧ St mx'.mem CSG mx' 0xB8 (reg mx') ∧
          reg mx' a0 = (csLoop M1 keys buf mlen nkeys s (k + 1) last).zeroExtend 32 ∧
          (∀ x, Sep (evG F) 0x20B0 x 1 → mx'.mem x = M1 x) ∧ reg mx' sp = F + BitVec.ofNat 32 0x16A0 ∧
          reg mx' 3 = reg mx 3 ∧ reg mx' 4 = reg mx 4 ∧ reg mx' 25 = reg mx 25 ∧ reg mx' 26 = reg mx 26 ∧
          reg mx' 27 = reg mx 27 := by
      intro mz fz c sz ha0 hsp' h3 h4 h25 h26 h27 hc
      refine ⟨mz, c, by rw [sz.mem]; exact sz.self, ?_, fun x hx => by rw [sz.mem]; exact hR x hx,
        by rw [sz.regs]; exact hsp', by rw [sz.regs]; exact h3, by rw [sz.regs]; exact h4, by rw [sz.regs]; exact h25,
        by rw [sz.regs]; exact h26, by rw [sz.regs]; exact h27⟩
      rw [sz.regs, ha0]
      show _ = (if (M1 s).toNat < last ∨ nkeys ≤ (M1 s).toNat then (0xF : BitVec 8)
        else if evSpec M1 (keys + BitVec.ofNat 32 (32 * (M1 s).toNat)) (s + 1) buf mlen then
          csLoop M1 keys buf mlen nkeys (s + 0x41) k ((M1 s).toNat + 1) else 0x10).zeroExtend 32
      rw [hb, ite_eq_left hc]; rfl
    by_cases hl : b.toNat < last
    · obtain ⟨n4, d4, u4⟩ := u3.taken hcx 0xB8 csg_at_84 (by decide)
        (by
          rw [f38, g3 a1 (by decide) (by decide), ha1]
          show (b.zeroExtend 32 : Word).ult (BitVec.ofNat 32 last) = true
          exact decide_eq_true (by rw [zb, BitVec.toNat_ofNat]; omega))
      exact err n4 _ (.cons d1 (.cons d2 (.cons d3 (.single d4)))) u4
        (by simp +decide only [upd, ite_true, ite_false])
        (by rw [g3 sp (by decide) (by decide)]; exact hsp) (by rw [g3 3 (by decide) (by decide)])
        (by rw [g3 4 (by decide) (by decide)]) (by rw [g3 25 (by decide) (by decide)])
        (by rw [g3 26 (by decide) (by decide)]) (by rw [g3 27 (by decide) (by decide)]) (Or.inl hl)
    obtain ⟨n4, d4, u4⟩ := u3.notTaken hcx 0x88 csg_at_84 (by decide)
      (by
        rw [f38, g3 a1 (by decide) (by decide), ha1]
        show (b.zeroExtend 32 : Word).ult (BitVec.ofNat 32 last) = false
        exact decide_eq_false (by rw [zb, BitVec.toNat_ofNat]; omega))
    by_cases hn : nkeys ≤ b.toNat
    · obtain ⟨n5, d5, u5⟩ := u4.taken hcx 0xB8 csg_at_88 (by decide)
        (by
          rw [f38, g3 20 (by decide) (by decide), h20]
          show (!(b.zeroExtend 32 : Word).ult (BitVec.ofNat 32 nkeys)) = true
          rw [show (b.zeroExtend 32 : Word).ult (BitVec.ofNat 32 nkeys) = false from
            decide_eq_false (by rw [zb, BitVec.toNat_ofNat]; omega)]; rfl)
      exact err n5 _ (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5))))) u5
        (by simp +decide only [upd, ite_true, ite_false])
        (by rw [g3 sp (by decide) (by decide)]; exact hsp) (by rw [g3 3 (by decide) (by decide)])
        (by rw [g3 4 (by decide) (by decide)]) (by rw [g3 25 (by decide) (by decide)])
        (by rw [g3 26 (by decide) (by decide)]) (by rw [g3 27 (by decide) (by decide)]) (Or.inr hn)
    obtain ⟨n5, d5, u5⟩ := u4.notTaken hcx 0x8C csg_at_88 (by decide)
      (by
        rw [f38, g3 20 (by decide) (by decide), h20]
        show (!(b.zeroExtend 32 : Word).ult (BitVec.ofNat 32 nkeys)) = false
        rw [show (b.zeroExtend 32 : Word).ult (BitVec.ofNat 32 nkeys) = true from
          decide_eq_true (by rw [zb, BitVec.toNat_ofNat]; omega)]; rfl)
    obtain ⟨n6, d6, u6⟩ := u5.aluImm hcx csg_at_8c (off' := 0x90) (by decide)
    obtain ⟨n7, d7, u7⟩ := u6.aluImm hcx csg_at_90 (off' := 0x94) (by decide)
    obtain ⟨n8, d8, u8⟩ := u7.aluImm hcx csg_at_94 (off' := 0x98) (by decide)
    obtain ⟨n9, d9, u9⟩ := u8.alu hcx csg_at_98 (off' := 0x9A) (by decide)
    obtain ⟨n10, d10, u10⟩ := u9.aluImm hcx csg_at_9a (off' := 0x9E) (by decide)
    obtain ⟨n11, d11, u11⟩ := u10.alu hcx csg_at_9e (off' := 0xA0) (by decide)
    obtain ⟨n12, d12, u12⟩ := u11.alu hcx csg_at_a0 (off' := 0xA2) (by decide)
    obtain ⟨pk, hpkd⟩ : ∃ pk, keys + BitVec.ofNat 32 (32 * b.toNat) = pk := ⟨_, rfl⟩
    have hpkn : pk.toNat = keys.toNat + 32 * b.toNat := by
      rw [← hpkd, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have v12a0 : reg n12 a0 = pk := by
      rw [u12.regs]; simp +decide only [upd, ite_true, ite_false]; rw [h18, ← hpkd]
      rw [show aluEval .sll (b.zeroExtend 32) 5 = BitVec.ofNat 32 (32 * b.toNat) from BitVec.eq_of_toNat_eq (by
        show ((b.zeroExtend 32 : Word) <<< ((5 : Word).toNat % 32)).toNat = _
        rw [show ((5 : Word).toNat % 32) = 5 from rfl, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, zb, BitVec.toNat_ofNat]; omega)]
      exact BitVec.add_comm _ _
    have v12a1 : reg n12 a1 = buf := by
      rw [u12.regs]; simp +decide only [upd, ite_true, ite_false]; rw [h23]; exact BitVec.zero_add buf
    have v12a2 : reg n12 a2 = BitVec.ofNat 32 mlen := by
      rw [u12.regs]; simp +decide only [upd, ite_true, ite_false]; rw [h19]; exact BitVec.zero_add _
    have v12a3 : reg n12 a3 = s + 1 := by rw [u12.regs]; simp +decide only [upd, ite_true, ite_false]; rw [h9]; rfl
    have v129 : reg n12 9 = s + 0x41 := by rw [u12.regs]; simp +decide only [upd, ite_true, ite_false]; rw [h9]; rfl
    have v1224 : reg n12 24 = BitVec.ofNat 32 (65 * k) := by
      rw [u12.regs]; simp +decide only [upd, ite_true, ite_false]; rw [h24]
      apply BitVec.eq_of_toNat_eq
      show (BitVec.ofNat 32 (65 * (k + 1)) + 0xFFFFFFBF).toNat = (BitVec.ofNat 32 (65 * k)).toNat
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFBF : Word).toNat = 4294967231 from rfl]
      omega
    have v128 : reg n12 8 = b.zeroExtend 32 := by rw [u12.regs]; simp +decide only [upd, ite_true, ite_false]
    have g12 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ 8 → r ≠ 9 → r ≠ 24 → reg n12 r = reg mx r :=
      fun r h0 h1 h2 h3 h8 h9' h24' => by
        by_cases hr : r.val = 0
        · have : r = 0 := Fin.ext hr
          subst this; rw [u12.self.zero, hz]
        rw [u12.regs]; simp only [upd, hr, h0, h1, h2, h3, h8, h9', h24', ↓reduceIte]
    have u12' := u12.self
    obtain ⟨m13, c13, pc13, mem13, regs13⟩ := u12'.callRa (cb := EV) hcx csg_at_a2 csg_at_a6 (by decide) (by decide)
    have r13 : ∀ r, r ≠ ra → reg m13 r = reg n12 r := fun r h => by rw [regs13]; exact updz u12'.zero h
    have hR13 : ∀ x, Sep (evG F) 0x20B0 x 1 → m13.mem x = M1 x := by rw [mem13]; exact hR
    have sP : Sep pk 32 (evG F) 0x20B0 := by rw [← hpkd]; exact sK.sub (c := 32 * b.toNat) (l := 32) (by omega)
    have sS : Sep (s + 1) 64 (evG F) 0x20B0 := by
      have := (hsS 0 (by omega)).sub (c := 1) (l := 64) (by omega)
      rwa [add_ofNat_assoc, Nat.mul_zero, Nat.zero_add] at this
    have hs1 : (s + 1).toNat = s.toNat + 1 := by
      rw [BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl]; omega
    have C : EvCtx m13.mem F pk (s + 1) buf mlen :=
      ⟨E1.congr (fun x hx => hR13 x (hiR x hx)) (roX _ hR13), hF, hlo, hhi, sRo, sP, sS, sB, by omega,
        by omega, by omega, hbw, hml, by rw [s5Hv_ro (roX _ hR13)]; exact iv1⟩
    obtain ⟨m14, c14, pc14, sp14, rs14, gp14, tp14, a014, mem14⟩ := ed25519Verify_correct m13 C pc13
      (by rw [r13 sp (by decide), g12 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hsp)
      (by rw [r13 a0 (by decide)]; exact v12a0) (by rw [r13 a1 (by decide)]; exact v12a1)
      (by rw [r13 a2 (by decide)]; exact v12a2) (by rw [r13 a3 (by decide)]; exact v12a3)
      (by rw [regs13]; simp +decide only [upd, ite_true, ite_false])
    have hev : evSpec m13.mem pk (s + 1) buf mlen = evSpec M1 pk (s + 1) buf mlen :=
      evSpec_congr (roX _ hR13) (fun i hi => hR13 _ ((sP.sub (c := i) (l := 1) hi).symm))
        (fun i hi => hR13 _ ((sS.sub (c := i) (l := 1) hi).symm)) (fun i hi => hR13 _ ((sB.sub (c := i) (l := 1) hi).symm))
    rw [hev] at a014
    have hR14 : ∀ x, Sep (evG F) 0x20B0 x 1 → m14.mem x = M1 x := fun x hx => (mem14 x hx).trans (hR13 x hx)
    have hc14 := codeX _ hR14
    have t14 : St m14.mem CSG m14 0xAA (reg m14) := ⟨by rw [pc14, regs13]; simp +decide only [upd, ite_true, ite_false],
      rfl, fun _ => rfl⟩
    have kev : ∀ r o, (r, o) ∈ evPs → r ≠ ra → reg m14 r = reg n12 r := fun r o h hr => by
      rw [rs14 r o h, r13 r hr]
    have k14 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ 8 → r ≠ 9 → r ≠ 24 → r ≠ ra →
        (∃ o, (r, o) ∈ evPs) → reg m14 r = reg mx r := fun r h0 h1 h2 h3 h8 h9' h24' hra ⟨o, ho⟩ =>
      (kev r o ho hra).trans (g12 r h0 h1 h2 h3 h8 h9' h24')
    have w148 : reg m14 8 = b.zeroExtend 32 := (kev 8 0x68 (by decide) (by decide)).trans v128
    have w149 : reg m14 9 = s + 0x41 := (kev 9 0x64 (by decide) (by decide)).trans v129
    have w1424 : reg m14 24 = BitVec.ofNat 32 (65 * k) := (kev 24 0x48 (by decide) (by decide)).trans v1224
    have w14sp : reg m14 sp = F + BitVec.ofNat 32 0x16A0 := by
      rw [sp14, r13 sp (by decide), g12 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hsp
    have w143 : reg m14 3 = reg mx 3 := by
      rw [gp14, r13 3 (by decide), g12 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    have w144 : reg m14 4 = reg mx 4 := by
      rw [tp14, r13 4 (by decide), g12 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    have w1425 : reg m14 25 = reg mx 25 := by
      rw [kev 25 0x44 (by decide) (by decide), g12 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]
    have w1426 : reg m14 26 = reg mx 26 := by
      rw [kev 26 0x40 (by decide) (by decide), g12 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]
    have w1427 : reg m14 27 = reg mx 27 := by
      rw [kev 27 0x3C (by decide) (by decide), g12 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]
    obtain ⟨n15, d15, u15⟩ := t14.aluImm hc14 csg_at_aa (off' := 0xAE) (by decide)
    have g15 : ∀ r, r ≠ a1 → upd (reg m14) a1 (aluEval .add (reg m14 8) 1) r = reg m14 r := fun r h => updz t14.zero h
    have hnot : ¬ ((M1 s).toNat < last ∨ nkeys ≤ (M1 s).toNat) := by
      rw [hb]; rintro (h | h)
      · exact hl h
      · exact hn h
    have pre14 : Steps mx m14 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
      (.cons d10 (.cons d11 (.cons d12 (c13.trans c14))))))))))))
    by_cases hv : evSpec M1 pk (s + 1) buf mlen = true
    · rw [ite_eq_left hv] at a014
      obtain ⟨n16, d16, u16⟩ := u15.taken hc14 0x7A csg_at_ae (by decide)
        (by rw [g15 a0 (by decide), a014, upd_zero_cs]; decide)
      have t16 : St n16.mem CSG n16 0x7A (reg n16) := by rw [u16.mem]; exact u16.self
      have r16 : ∀ r, reg n16 r = upd (reg m14) a1 (aluEval .add (reg m14 8) 1) r := u16.regs
      obtain ⟨mx', cx, sx, ax, hRx, spx, gx, tx, x25, x26, x27⟩ := ih n16 (s + 0x41) (b.toNat + 1)
        (fun j hj => by
          have := hsS (j + 1) (by omega)
          rwa [show s + BitVec.ofNat 32 (65 * (j + 1)) = s + 0x41 + BitVec.ofNat 32 (65 * j) by
            rw [show (s + 0x41 : Word) = s + BitVec.ofNat 32 65 from rfl, add_ofNat_assoc,
              show 65 + 65 * j = 65 * (j + 1) by omega]] at this)
        (by rw [BitVec.toNat_add, show (0x41 : Word).toNat = 65 from rfl]; omega) t16
        (by rw [u16.mem]; exact hR14) (by rw [r16, g15 sp (by decide)]; exact w14sp)
        (by rw [r16, g15 24 (by decide)]; exact w1424) (by rw [r16, g15 9 (by decide)]; exact w149)
        (by
          rw [r16]; simp +decide only [upd, ite_true, ite_false]; rw [w148]
          apply BitVec.eq_of_toNat_eq
          show ((b.zeroExtend 32 : Word) + 1).toNat = (BitVec.ofNat 32 (b.toNat + 1)).toNat
          rw [BitVec.toNat_add, zb, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl])
        (by omega)
        (by rw [r16, g15 18 (by decide), kev 18 0x60 (by decide) (by decide),
          g12 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h18)
        (by rw [r16, g15 19 (by decide), kev 19 0x5C (by decide) (by decide),
          g12 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h19)
        (by rw [r16, g15 20 (by decide), kev 20 0x58 (by decide) (by decide),
          g12 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h20)
        (by rw [r16, g15 23 (by decide), kev 23 0x4C (by decide) (by decide),
          g12 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h23)
      refine ⟨mx', pre14.trans (.cons d15 (.cons d16 cx)), sx, ?_, hRx, spx,
        by rw [gx, r16, g15 3 (by decide)]; exact w143, by rw [tx, r16, g15 4 (by decide)]; exact w144,
        by rw [x25, r16, g15 25 (by decide)]; exact w1425, by rw [x26, r16, g15 26 (by decide)]; exact w1426,
        by rw [x27, r16, g15 27 (by decide)]; exact w1427⟩
      rw [ax]
      show _ = (if (M1 s).toNat < last ∨ nkeys ≤ (M1 s).toNat then (0xF : BitVec 8)
        else if evSpec M1 (keys + BitVec.ofNat 32 (32 * (M1 s).toNat)) (s + 1) buf mlen then
          csLoop M1 keys buf mlen nkeys (s + 0x41) k ((M1 s).toNat + 1) else 0x10).zeroExtend 32
      rw [ite_eq_right hnot, hb, hpkd, ite_eq_left hv]
    · rw [ite_eq_right hv] at a014
      obtain ⟨n16, d16, u16⟩ := u15.notTaken hc14 0xB0 csg_at_ae (by decide)
        (by rw [g15 a0 (by decide), a014, upd_zero_cs]; decide)
      obtain ⟨n17, d17, u17⟩ := u16.aluImm hc14 csg_at_b0 (off' := 0xB2) (by decide)
      obtain ⟨n18, d18, u18⟩ := u17.jump hc14 csg_at_b2 (off' := 0xB8) (by decide) (by rw [u17.pc]; decide)
      have hz15 := u15.zero
      refine ⟨n18, pre14.trans (.cons d15 (.cons d16 (.cons d17 (.single d18)))), by rw [u18.mem]; exact u18.self, ?_,
        fun x hx => by rw [u18.mem]; exact hR14 x hx, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [u18.regs]
        show _ = (if (M1 s).toNat < last ∨ nkeys ≤ (M1 s).toNat then (0xF : BitVec 8)
          else if evSpec M1 (keys + BitVec.ofNat 32 (32 * (M1 s).toNat)) (s + 1) buf mlen then
            csLoop M1 keys buf mlen nkeys (s + 0x41) k ((M1 s).toNat + 1) else 0x10).zeroExtend 32
        rw [ite_eq_right hnot, hb, hpkd, ite_eq_right hv]
        simp +decide only [upd, ite_true, ite_false]
      · rw [u18.regs, updz hz15 (by decide), g15 sp (by decide)]; exact w14sp
      · rw [u18.regs, updz hz15 (by decide), g15 3 (by decide)]; exact w143
      · rw [u18.regs, updz hz15 (by decide), g15 4 (by decide)]; exact w144
      · rw [u18.regs, updz hz15 (by decide), g15 25 (by decide)]; exact w1425
      · rw [u18.regs, updz hz15 (by decide), g15 26 (by decide)]; exact w1426
      · rw [u18.regs, updz hz15 (by decide), g15 27 (by decide)]; exact w1427

theorem csLoop_congr {M M' : Word → BitVec 8} {keys buf : Word} {mlen nkeys : Nat} (hro : RoAgree M M')
    (hk : ∀ i, i < 32 * nkeys → M (keys + BitVec.ofNat 32 i) = M' (keys + BitVec.ofNat 32 i))
    (hb : ∀ i, i < mlen → M (buf + BitVec.ofNat 32 i) = M' (buf + BitVec.ofNat 32 i)) :
    ∀ (k : Nat) (s : Word) (last : Nat), (∀ i, i < 65 * k → M (s + BitVec.ofNat 32 i) = M' (s + BitVec.ofNat 32 i)) →
      csLoop M keys buf mlen nkeys s k last = csLoop M' keys buf mlen nkeys s k last
  | 0, _, _, _ => rfl
  | k + 1, s, last, hs => by
    have h0 : M s = M' s := by have := hs 0 (by omega); rwa [add_ofNat_zero] at this
    show (if (M s).toNat < last ∨ nkeys ≤ (M s).toNat then (0xF : BitVec 8)
        else if evSpec M (keys + BitVec.ofNat 32 (32 * (M s).toNat)) (s + 1) buf mlen then
          csLoop M keys buf mlen nkeys (s + 0x41) k ((M s).toNat + 1) else 0x10) =
      (if (M' s).toNat < last ∨ nkeys ≤ (M' s).toNat then (0xF : BitVec 8)
        else if evSpec M' (keys + BitVec.ofNat 32 (32 * (M' s).toNat)) (s + 1) buf mlen then
          csLoop M' keys buf mlen nkeys (s + 0x41) k ((M' s).toNat + 1) else 0x10)
    rw [h0]
    by_cases hc : (M' s).toNat < last ∨ nkeys ≤ (M' s).toNat
    · rw [ite_eq_left hc, ite_eq_left hc]
    rw [ite_eq_right hc, ite_eq_right hc]
    have hidx : (M' s).toNat < nkeys := by
      rcases Nat.lt_or_ge (M' s).toNat nkeys with h | h
      · exact h
      · exact absurd (Or.inr h) hc
    rw [evSpec_congr hro (fun i hi => by rw [add_ofNat_assoc]; exact hk _ (by omega))
      (fun i hi => by rw [show s + 1 + BitVec.ofNat 32 i = s + BitVec.ofNat 32 (1 + i) by
        rw [show (s + 1 : Word) = s + BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]]; exact hs _ (by omega)) hb,
      csLoop_congr hro hk hb k (s + 0x41) ((M' s).toNat + 1) fun i hi => by
        rw [show s + 0x41 + BitVec.ofNat 32 i = s + BitVec.ofNat 32 (65 + i) by
          rw [show (s + 0x41 : Word) = s + BitVec.ofNat 32 65 from rfl, add_ofNat_assoc]]; exact hs _ (by omega)]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 64000000 in
/-- **`check_signatures`, as compiled**: with `ed25519_verify`, `memcpy`,
and `copy_from_slice` where the image puts them, 0x20E0 bytes of stack below
`sp` (16-aligned, below 0x40000000), the signatures, keys, prefix, and
payload apart from that stack, and a 0x1018-byte buffer apart from the stack,
the prefix, the payload, and the read-only data, it returns to `ra` with `sp`, `gp`, `tp`,
and `s0` through `s11` restored, `csResult` in `a0`, and memory outside its
stack as `csMem` says. -/
theorem checkSignatures_correct (m : Machine) {retAddr sigs slen keys klen pre pay plen buf : Word}
    (E : EvEnv m.mem) (hc : CodeIn m.mem CSG checkSignaturesCode)
    (hst : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode)
    (hbd : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode)
    (hcf : CodeIn m.mem (BitVec.ofNat 32 copyFromSliceU8Address) copyFromSliceU8Code)
    (hpc : m.pc = CSG) (ha0 : reg m a0 = sigs) (ha1 : reg m a1 = slen) (ha2 : reg m a2 = keys)
    (ha3 : reg m a3 = klen) (ha4 : reg m a4 = pre) (ha5 : reg m a5 = pay) (ha6 : reg m a6 = plen)
    (ha7 : reg m 17 = buf) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 16 = 0) (hsl : 0x20E0 ≤ (reg m sp).toNat) (hsw : (reg m sp).toNat ≤ 0x40000000)
    (sRo : Sep (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize) (reg m sp + 0xFFFFDF20) 0x20E0)
    (iv : (s5Hv m.mem (BitVec.ofNat 32 (img% sha512IVAddress))).toList = Sha512.h0)
    (sSig : Sep sigs slen.toNat (reg m sp + 0xFFFFDF20) 0x20E0) (hsigw : sigs.toNat + slen.toNat < 2 ^ 32)
    (sK : Sep keys (32 * (klen.toNat / 32)) (reg m sp + 0xFFFFDF20) 0x20E0)
    (hkw : keys.toNat + 32 * (klen.toNat / 32) < 2 ^ 32)
    (sPre : Sep pre 21 (reg m sp + 0xFFFFDF20) 0x20E0) (hprew : pre.toNat + 21 < 2 ^ 32)
    (sPay : plen.toNat ≤ 0x1002 → Sep pay plen.toNat (reg m sp + 0xFFFFDF20) 0x20E0)
    (hpayw : plen.toNat ≤ 0x1002 → pay.toNat + plen.toNat < 2 ^ 32)
    (sBuf : Sep buf 0x1018 (reg m sp + 0xFFFFDF20) 0x20E0) (hbw : buf.toNat + 0x1018 ≤ 0x40000000)
    (bPre : Sep buf 21 pre 21) (bPay : plen.toNat ≤ 0x1002 → Sep (buf + 0x16) plen.toNat pay plen.toNat)
    (bRo : Sep buf 0x1018 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize)) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      (∀ q, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      reg m' a0 = (csResult m.mem sigs slen keys klen pre pay plen buf).zeroExtend 32 ∧
      ∀ x, Sep (reg m sp + 0xFFFFDF20) 0x20E0 x 1 → m'.mem x = csMem m.mem slen pre pay plen buf x := by
  obtain ⟨S, hSd⟩ : ∃ S, reg m sp + 0xFFFFDF20 = S := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G, reg m sp + 0xFFFFFFD0 = G := ⟨_, rfl⟩
  rw [hSd] at sRo sSig sK sPre sPay sBuf ⊢
  have hSn : S.toNat = (reg m sp).toNat - 0x20E0 := by
    rw [← hSd, BitVec.toNat_add, show (0xFFFFDF20 : Word).toNat = 2 ^ 32 - 0x20E0 from rfl]; omega
  have hGn : G.toNat = (reg m sp).toNat - 0x30 := by
    rw [← hGd, BitVec.toNat_add, show (0xFFFFFFD0 : Word).toNat = 2 ^ 32 - 0x30 from rfl]; omega
  have hGS : G = S + BitVec.ofNat 32 0x20B0 := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hGn, hSn]; omega)
  have hspG : G + 0x30 = reg m sp := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, show (0x30 : Word).toNat = 0x30 from rfl, hGn]; omega)
  have hGa : G.toNat % 4 = 0 := by omega
  have fr : ∀ c l, c + l ≤ 0x30 → ∀ (x : Word) (n : Nat), Sep S 0x20E0 x n → Sep (G + BitVec.ofNat 32 c) l x n :=
    fun c l h x n hx => by rw [hGS, add_ofNat_assoc]; exact hx.sub (c := 0x20B0 + c) (l := l) (by omega)
  have hiS : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep S 0x20E0 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have gLow : ∀ c, c + 4 ≤ 0x30 → (G + BitVec.ofNat 32 c).toNat + 4 ≤ 0x40000000 := fun c h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have s0 : St m.mem CSG m 0 (reg m) := ⟨by rw [hpc]; rfl, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, e1, t1⟩ := s0.aluImm hc csg_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFD0 = G from hGd] at t1
  have u1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp G r = reg m r := fun r h => updz hz h
  obtain ⟨m2, e2, t2⟩ := t1.sw hc csg_at_2 (off' := 0x4) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x2C) (by decide))
  rw [u1sp, f1 ra (by decide)] at t2
  have hc2 := hc.store32 (v := reg m ra) (lowSep (gLow 0x2C (by omega)) (by decide) (by decide))
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 csg_at_4 (off' := 0x6) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x28) (by decide))
  rw [u1sp, f1 8 (by decide)] at t3
  have hc3 := hc2.store32 (v := reg m 8) (lowSep (gLow 0x28 (by omega)) (by decide) (by decide))
  obtain ⟨m4, e4, t4⟩ := t3.sw hc3 csg_at_6 (off' := 0x8) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x24) (by decide))
  rw [u1sp, f1 9 (by decide)] at t4
  have hc4 := hc3.store32 (v := reg m 9) (lowSep (gLow 0x24 (by omega)) (by decide) (by decide))
  obtain ⟨m5, e5, t5⟩ := t4.sw hc4 csg_at_8 (off' := 0xA) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x20) (by decide))
  rw [u1sp, f1 18 (by decide)] at t5
  have hc5 := hc4.store32 (v := reg m 18) (lowSep (gLow 0x20 (by omega)) (by decide) (by decide))
  obtain ⟨m6, e6, t6⟩ := t5.sw hc5 csg_at_a (off' := 0xC) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x1C) (by decide))
  rw [u1sp, f1 19 (by decide)] at t6
  have hc6 := hc5.store32 (v := reg m 19) (lowSep (gLow 0x1C (by omega)) (by decide) (by decide))
  obtain ⟨m7, e7, t7⟩ := t6.sw hc6 csg_at_c (off' := 0xE) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x18) (by decide))
  rw [u1sp, f1 20 (by decide)] at t7
  have hc7 := hc6.store32 (v := reg m 20) (lowSep (gLow 0x18 (by omega)) (by decide) (by decide))
  obtain ⟨m8, e8, t8⟩ := t7.sw hc7 csg_at_e (off' := 0x10) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x14) (by decide))
  rw [u1sp, f1 21 (by decide)] at t8
  have hc8 := hc7.store32 (v := reg m 21) (lowSep (gLow 0x14 (by omega)) (by decide) (by decide))
  obtain ⟨m9, e9, t9⟩ := t8.sw hc8 csg_at_10 (off' := 0x12) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x10) (by decide))
  rw [u1sp, f1 22 (by decide)] at t9
  have hc9 := hc8.store32 (v := reg m 22) (lowSep (gLow 0x10 (by omega)) (by decide) (by decide))
  obtain ⟨m10, e10, t10⟩ := t9.sw hc9 csg_at_12 (off' := 0x14) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0xC) (by decide))
  rw [u1sp, f1 23 (by decide)] at t10
  have hc10 := hc9.store32 (v := reg m 23) (lowSep (gLow 0xC (by omega)) (by decide) (by decide))
  obtain ⟨m11, e11, t11⟩ := t10.sw hc10 csg_at_14 (off' := 0x16) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x8) (by decide))
  rw [u1sp, f1 24 (by decide)] at t11
  obtain ⟨M10, hM10⟩ : ∃ M10, memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (m.mem) (G + 0x2C) (reg m ra)) (G + 0x28) (reg m 8)) (G + 0x24) (reg m 9)) (G + 0x20) (reg m 18)) (G + 0x1C) (reg m 19)) (G + 0x18) (reg m 20)) (G + 0x14) (reg m 21)) (G + 0x10) (reg m 22)) (G + 0xC) (reg m 23)) (G + 0x8) (reg m 24) = M10 := ⟨_, rfl⟩
  rw [hM10] at t11
  have M10out : ∀ x, Sep S 0x20E0 x 1 → M10 x = m.mem x := fun x hx => by
    rw [← hM10]
    exact (memStore32_get_sep (fr 0x8 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0xC 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x10 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x14 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x18 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x1C 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x20 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x24 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x28 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x2C 4 (by omega) x 1 hx)))))))))))
  have fl2c : memLoad32 M10 (G + 0x2C) = reg m ra := by
    rw [← hM10]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x14) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x18) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x1C) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x24) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x28) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl28 : memLoad32 M10 (G + 0x28) = reg m 8 := by
    rw [← hM10]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x14) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x18) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x1C) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x24) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl24 : memLoad32 M10 (G + 0x24) = reg m 9 := by
    rw [← hM10]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x14) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x18) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x1C) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl20 : memLoad32 M10 (G + 0x20) = reg m 18 := by
    rw [← hM10]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x20) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x20) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x20) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x14) (n := 4) (d := 0x20) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x18) (n := 4) (d := 0x20) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x1C) (n := 4) (d := 0x20) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl1c : memLoad32 M10 (G + 0x1C) = reg m 19 := by
    rw [← hM10]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x14) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x18) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl18 : memLoad32 M10 (G + 0x18) = reg m 20 := by
    rw [← hM10]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x18) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x18) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x18) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x14) (n := 4) (d := 0x18) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl14 : memLoad32 M10 (G + 0x14) = reg m 21 := by
    rw [← hM10]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x14) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x14) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x14) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl10 : memLoad32 M10 (G + 0x10) = reg m 22 := by
    rw [← hM10]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x10) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x10) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have flc : memLoad32 M10 (G + 0xC) = reg m 23 := by
    rw [← hM10]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0xC) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl8 : memLoad32 M10 (G + 0x8) = reg m 24 := by
    rw [← hM10]
    exact memLoad32_store32_same _ _ _
  have epi : ∀ (Mx : Word → BitVec 8) (mx : Machine), St Mx CSG mx 0xB8 (reg mx) → CodeIn Mx CSG checkSignaturesCode →
      reg mx sp = G →
      (∀ c, 8 ≤ c → c + 4 ≤ 0x30 → memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 M10 (G + BitVec.ofNat 32 c)) →
      reg mx 3 = reg m 3 → reg mx 4 = reg m 4 → reg mx 25 = reg m 25 → reg mx 26 = reg m 26 → reg mx 27 = reg m 27 →
      ∃ m', Steps mx m' ∧ m'.pc = retAddr ∧
        (∀ q, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        reg m' a0 = reg mx a0 ∧ m'.mem = Mx := by
    intro Mx mx s hcx hs hF h3 h4 h25 h26 h27
    obtain ⟨n1, d1, u1⟩ := s.lw hcx csg_at_b8 (off' := 0xBA) (by decide)
      (by rw [hs]; exact aligned_add hGa (k := 0x2C) (by decide))
    rw [hs, show memLoad32 Mx (G + 0x2C) = reg m ra from (hF 0x2C (by omega) (by omega)).trans fl2c] at u1
    have q1 : ∀ r, r ≠ ra → reg n1 r = reg mx r := fun r h => by rw [u1.regs]; exact updz s.zero h
    have w1 : reg n1 ra = reg m ra := by rw [u1.regs]; simp +decide only [upd, ite_true, ite_false]
    have p1 : reg n1 sp = G := by rw [q1 sp (by decide)]; exact hs
    obtain ⟨n2, d2, u2⟩ := u1.self.lw hcx csg_at_ba (off' := 0xBC) (by decide)
      (by rw [p1]; exact aligned_add hGa (k := 0x28) (by decide))
    rw [p1, show memLoad32 Mx (G + 0x28) = reg m 8 from (hF 0x28 (by omega) (by omega)).trans fl28] at u2
    have q2 : ∀ r, r ≠ 8 → reg n2 r = reg n1 r := fun r h => by rw [u2.regs]; exact updz u1.self.zero h
    have w2 : reg n2 8 = reg m 8 := by rw [u2.regs]; simp +decide only [upd, ite_true, ite_false]
    have p2 : reg n2 sp = G := by rw [q2 sp (by decide)]; exact p1
    obtain ⟨n3, d3, u3⟩ := u2.self.lw hcx csg_at_bc (off' := 0xBE) (by decide)
      (by rw [p2]; exact aligned_add hGa (k := 0x24) (by decide))
    rw [p2, show memLoad32 Mx (G + 0x24) = reg m 9 from (hF 0x24 (by omega) (by omega)).trans fl24] at u3
    have q3 : ∀ r, r ≠ 9 → reg n3 r = reg n2 r := fun r h => by rw [u3.regs]; exact updz u2.self.zero h
    have w3 : reg n3 9 = reg m 9 := by rw [u3.regs]; simp +decide only [upd, ite_true, ite_false]
    have p3 : reg n3 sp = G := by rw [q3 sp (by decide)]; exact p2
    obtain ⟨n4, d4, u4⟩ := u3.self.lw hcx csg_at_be (off' := 0xC0) (by decide)
      (by rw [p3]; exact aligned_add hGa (k := 0x20) (by decide))
    rw [p3, show memLoad32 Mx (G + 0x20) = reg m 18 from (hF 0x20 (by omega) (by omega)).trans fl20] at u4
    have q4 : ∀ r, r ≠ 18 → reg n4 r = reg n3 r := fun r h => by rw [u4.regs]; exact updz u3.self.zero h
    have w4 : reg n4 18 = reg m 18 := by rw [u4.regs]; simp +decide only [upd, ite_true, ite_false]
    have p4 : reg n4 sp = G := by rw [q4 sp (by decide)]; exact p3
    obtain ⟨n5, d5, u5⟩ := u4.self.lw hcx csg_at_c0 (off' := 0xC2) (by decide)
      (by rw [p4]; exact aligned_add hGa (k := 0x1C) (by decide))
    rw [p4, show memLoad32 Mx (G + 0x1C) = reg m 19 from (hF 0x1C (by omega) (by omega)).trans fl1c] at u5
    have q5 : ∀ r, r ≠ 19 → reg n5 r = reg n4 r := fun r h => by rw [u5.regs]; exact updz u4.self.zero h
    have w5 : reg n5 19 = reg m 19 := by rw [u5.regs]; simp +decide only [upd, ite_true, ite_false]
    have p5 : reg n5 sp = G := by rw [q5 sp (by decide)]; exact p4
    obtain ⟨n6, d6, u6⟩ := u5.self.lw hcx csg_at_c2 (off' := 0xC4) (by decide)
      (by rw [p5]; exact aligned_add hGa (k := 0x18) (by decide))
    rw [p5, show memLoad32 Mx (G + 0x18) = reg m 20 from (hF 0x18 (by omega) (by omega)).trans fl18] at u6
    have q6 : ∀ r, r ≠ 20 → reg n6 r = reg n5 r := fun r h => by rw [u6.regs]; exact updz u5.self.zero h
    have w6 : reg n6 20 = reg m 20 := by rw [u6.regs]; simp +decide only [upd, ite_true, ite_false]
    have p6 : reg n6 sp = G := by rw [q6 sp (by decide)]; exact p5
    obtain ⟨n7, d7, u7⟩ := u6.self.lw hcx csg_at_c4 (off' := 0xC6) (by decide)
      (by rw [p6]; exact aligned_add hGa (k := 0x14) (by decide))
    rw [p6, show memLoad32 Mx (G + 0x14) = reg m 21 from (hF 0x14 (by omega) (by omega)).trans fl14] at u7
    have q7 : ∀ r, r ≠ 21 → reg n7 r = reg n6 r := fun r h => by rw [u7.regs]; exact updz u6.self.zero h
    have w7 : reg n7 21 = reg m 21 := by rw [u7.regs]; simp +decide only [upd, ite_true, ite_false]
    have p7 : reg n7 sp = G := by rw [q7 sp (by decide)]; exact p6
    obtain ⟨n8, d8, u8⟩ := u7.self.lw hcx csg_at_c6 (off' := 0xC8) (by decide)
      (by rw [p7]; exact aligned_add hGa (k := 0x10) (by decide))
    rw [p7, show memLoad32 Mx (G + 0x10) = reg m 22 from (hF 0x10 (by omega) (by omega)).trans fl10] at u8
    have q8 : ∀ r, r ≠ 22 → reg n8 r = reg n7 r := fun r h => by rw [u8.regs]; exact updz u7.self.zero h
    have w8 : reg n8 22 = reg m 22 := by rw [u8.regs]; simp +decide only [upd, ite_true, ite_false]
    have p8 : reg n8 sp = G := by rw [q8 sp (by decide)]; exact p7
    obtain ⟨n9, d9, u9⟩ := u8.self.lw hcx csg_at_c8 (off' := 0xCA) (by decide)
      (by rw [p8]; exact aligned_add hGa (k := 0xC) (by decide))
    rw [p8, show memLoad32 Mx (G + 0xC) = reg m 23 from (hF 0xC (by omega) (by omega)).trans flc] at u9
    have q9 : ∀ r, r ≠ 23 → reg n9 r = reg n8 r := fun r h => by rw [u9.regs]; exact updz u8.self.zero h
    have w9 : reg n9 23 = reg m 23 := by rw [u9.regs]; simp +decide only [upd, ite_true, ite_false]
    have p9 : reg n9 sp = G := by rw [q9 sp (by decide)]; exact p8
    obtain ⟨n10, d10, u10⟩ := u9.self.lw hcx csg_at_ca (off' := 0xCC) (by decide)
      (by rw [p9]; exact aligned_add hGa (k := 0x8) (by decide))
    rw [p9, show memLoad32 Mx (G + 0x8) = reg m 24 from (hF 0x8 (by omega) (by omega)).trans fl8] at u10
    have q10 : ∀ r, r ≠ 24 → reg n10 r = reg n9 r := fun r h => by rw [u10.regs]; exact updz u9.self.zero h
    have w10 : reg n10 24 = reg m 24 := by rw [u10.regs]; simp +decide only [upd, ite_true, ite_false]
    have p10 : reg n10 sp = G := by rw [q10 sp (by decide)]; exact p9
    obtain ⟨n11, d11, u11⟩ := u10.self.aluImm hcx csg_at_cc (off' := 0xCE) (by decide)
    obtain ⟨n12, d12, pc12, mem12, regs12⟩ := u11.jalr hcx csg_at_ce
    have z10 : ∀ r, r ≠ ra → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 23 → r ≠ 24 →
        reg n10 r = reg mx r := fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
      rw [q10 r h10, q9 r h9, q8 r h8, q7 r h7, q6 r h6, q5 r h5, q4 r h4, q3 r h3, q2 r h2, q1 r h1]
    have vra : reg n10 ra = reg m ra := by rw [q10 ra (by decide), q9 ra (by decide), q8 ra (by decide), q7 ra (by decide), q6 ra (by decide), q5 ra (by decide), q4 ra (by decide), q3 ra (by decide), q2 ra (by decide)]; exact w1
    have v8 : reg n10 8 = reg m 8 := by rw [q10 8 (by decide), q9 8 (by decide), q8 8 (by decide), q7 8 (by decide), q6 8 (by decide), q5 8 (by decide), q4 8 (by decide), q3 8 (by decide)]; exact w2
    have v9 : reg n10 9 = reg m 9 := by rw [q10 9 (by decide), q9 9 (by decide), q8 9 (by decide), q7 9 (by decide), q6 9 (by decide), q5 9 (by decide), q4 9 (by decide)]; exact w3
    have v18 : reg n10 18 = reg m 18 := by rw [q10 18 (by decide), q9 18 (by decide), q8 18 (by decide), q7 18 (by decide), q6 18 (by decide), q5 18 (by decide)]; exact w4
    have v19 : reg n10 19 = reg m 19 := by rw [q10 19 (by decide), q9 19 (by decide), q8 19 (by decide), q7 19 (by decide), q6 19 (by decide)]; exact w5
    have v20 : reg n10 20 = reg m 20 := by rw [q10 20 (by decide), q9 20 (by decide), q8 20 (by decide), q7 20 (by decide)]; exact w6
    have v21 : reg n10 21 = reg m 21 := by rw [q10 21 (by decide), q9 21 (by decide), q8 21 (by decide)]; exact w7
    have v22 : reg n10 22 = reg m 22 := by rw [q10 22 (by decide), q9 22 (by decide)]; exact w8
    have v23 : reg n10 23 = reg m 23 := by rw [q10 23 (by decide)]; exact w9
    have v24 : reg n10 24 = reg m 24 := w10
    have r12 : ∀ r, r ≠ sp → reg n12 r = reg n10 r := fun r h => by rw [regs12]; exact updz u10.self.zero h
    refine ⟨n12, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10
      (.cons d11 (.single d12))))))))))), ?_, fun q hq => ?_, ?_, by rw [mem12]⟩
    · rw [pc12, add_lit_zero, updz u10.self.zero (show ra ≠ sp by decide), vra, hra, hret]
    · have hq' : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 8 ∨ q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 20 ∨ q = 21 ∨ q = 22 ∨ q = 23 ∨
          q = 24 ∨ q = 25 ∨ q = 26 ∨ q = 27 := by revert q; decide
      rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [regs12]; simp +decide only [upd, ite_true, ite_false]; rw [p10, ← hspG]; rfl
      · rw [r12 3 (by decide), z10 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h3
      · rw [r12 4 (by decide), z10 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h4
      · rw [r12 8 (by decide)]; exact v8
      · rw [r12 9 (by decide)]; exact v9
      · rw [r12 18 (by decide)]; exact v18
      · rw [r12 19 (by decide)]; exact v19
      · rw [r12 20 (by decide)]; exact v20
      · rw [r12 21 (by decide)]; exact v21
      · rw [r12 22 (by decide)]; exact v22
      · rw [r12 23 (by decide)]; exact v23
      · rw [r12 24 (by decide)]; exact v24
      · rw [r12 25 (by decide), z10 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h25
      · rw [r12 26 (by decide), z10 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h26
      · rw [r12 27 (by decide), z10 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h27
    · rw [r12 a0 (by decide), z10 a0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have codeM : ∀ {b : Word} {code : List Nat}, 0x40000000 ≤ b.toNat → b.toNat + code.length ≤ 2 ^ 32 →
      CodeIn m.mem b code → CodeIn M10 b code := fun hb hbl hc' i hi => by
    rw [M10out _ (hiS _ (code_hi hb hbl hi))]; exact hc' i hi
  have hc10 := codeM (by decide) (by decide) hc
  have frameM : ∀ (Mx : Word → BitVec 8), (∀ c, 8 ≤ c → c + 4 ≤ 0x30 → memLoad32 Mx (G + BitVec.ofNat 32 c) =
      memLoad32 M10 (G + BitVec.ofNat 32 c)) → ∀ c, 8 ≤ c → c + 4 ≤ 0x30 →
      memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 M10 (G + BitVec.ofNat 32 c) := fun _ h => h
  have exitAt : ∀ (Mx : Word → BitVec 8) (mx : Machine), Steps m mx → St Mx CSG mx 0xB8 (reg mx) →
      CodeIn Mx CSG checkSignaturesCode → reg mx sp = G →
      (∀ c, 8 ≤ c → c + 4 ≤ 0x30 → memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 M10 (G + BitVec.ofNat 32 c)) →
      reg mx 3 = reg m 3 → reg mx 4 = reg m 4 → reg mx 25 = reg m 25 → reg mx 26 = reg m 26 → reg mx 27 = reg m 27 →
      reg mx a0 = (csResult m.mem sigs slen keys klen pre pay plen buf).zeroExtend 32 →
      (∀ x, Sep S 0x20E0 x 1 → Mx x = csMem m.mem slen pre pay plen buf x) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
        (∀ q, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        reg m' a0 = (csResult m.mem sigs slen keys klen pre pay plen buf).zeroExtend 32 ∧
        ∀ x, Sep S 0x20E0 x 1 → m'.mem x = csMem m.mem slen pre pay plen buf x := by
    intro Mx mx c s hcx hs hF h3 h4 h25 h26 h27 ha hm
    obtain ⟨m', c', pc', k', a0', mem'⟩ := epi Mx mx s hcx hs hF h3 h4 h25 h26 h27
    exact ⟨m', c.trans c', pc', k', a0'.trans ha, fun x hx => by rw [mem']; exact hm x hx⟩
  obtain ⟨m12, e12, t12⟩ := t11.alu hc10 csg_at_16 (off' := 0x18) (by decide)
  obtain ⟨m13, e13, t13⟩ := t12.alu hc10 csg_at_18 (off' := 0x1A) (by decide)
  obtain ⟨m14, e14, t14⟩ := t13.aluImm hc10 csg_at_1a (off' := 0x1E) (by decide)
  obtain ⟨m15, e15, t15⟩ := t14.aluImm hc10 csg_at_1e (off' := 0x20) (by decide)
  have v15a0 : reg m15 a0 = 5 := by rw [t15.regs]; simp +decide only [upd, ite_true, ite_false]
  have v15a1 : reg m15 a1 = slen := by rw [t15.regs]; simp +decide [upd, ha1]
  have v15a2 : reg m15 a2 = 0x82 := by rw [t15.regs]; simp +decide only [upd, ite_true, ite_false]
  have v15k : ∀ r, r ≠ a0 → r ≠ a2 → r ≠ 9 → r ≠ 18 → r ≠ sp → reg m15 r = reg m r := fun r h0 h2 h9 h18 hsp' => by
    rw [t15.regs]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd, hz]
    · simp [upd, hr, h0, h2, h9, h18, hsp']
  have v159 : reg m15 9 = sigs := by rw [t15.regs]; simp +decide [upd, aluEval, ha0]
  have v1518 : reg m15 18 = keys := by rw [t15.regs]; simp +decide [upd, aluEval, ha2]
  have v15sp : reg m15 sp = G := by rw [t15.regs]; simp +decide [upd]
  have u15 := t15.self
  have pre15 : Steps m m15 := .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (.cons e9
    (.cons e10 (.cons e11 (.cons e12 (.cons e13 (.cons e14 (.single e15))))))))))))))
  have frame10 : ∀ c, 8 ≤ c → c + 4 ≤ 0x30 → memLoad32 M10 (G + BitVec.ofNat 32 c) = memLoad32 M10 (G + BitVec.ofNat 32 c) :=
    fun _ _ _ => rfl
  by_cases h82 : slen.toNat < 0x82
  · obtain ⟨m16, e16, t16⟩ := u15.taken hc10 0xB8 csg_at_20 (by decide)
      (by rw [v15a1, v15a2]; exact decide_eq_true (by show slen.toNat < (0x82 : Word).toNat; exact h82))
    refine exitAt M10 m16 (pre15.trans (.single e16)) t16.self hc10 (by rw [t16.regs]; exact v15sp)
      (fun _ _ _ => rfl) (by rw [t16.regs, v15k 3 (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [t16.regs, v15k 4 (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [t16.regs, v15k 25 (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [t16.regs, v15k 26 (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [t16.regs, v15k 27 (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [t16.regs, v15a0]; unfold csResult; rw [ite_eq_left (Or.inl h82)]; rfl)
      (fun x hx => by unfold csMem; rw [ite_eq_left (Or.inl h82)]; exact M10out x hx)
  obtain ⟨m16, e16, t16⟩ := u15.notTaken hc10 0x24 csg_at_20 (by decide)
    (by rw [v15a1, v15a2]; exact decide_eq_false (by show ¬ slen.toNat < (0x82 : Word).toNat; exact h82))
  obtain ⟨m17, e17, t17⟩ := t16.aluImm hc10 csg_at_24 (off' := 0x28) (by decide)
  obtain ⟨m18, e18, t18⟩ := t17.alu hc10 csg_at_28 (off' := 0x2C) (by decide)
  obtain ⟨m19, e19, t19⟩ := t18.aluImm hc10 csg_at_2c (off' := 0x30) (by decide)
  obtain ⟨m20, e20, t20⟩ := t19.alu hc10 csg_at_30 (off' := 0x32) (by decide)
  obtain ⟨m21, e21, t21⟩ := t20.alu hc10 csg_at_32 (off' := 0x36) (by decide)
  have hq65 : 65 * (slen.toNat / 65) ≤ slen.toNat := Nat.mul_div_le _ _
  have hdiv : aluEval .divu slen 0x41 = BitVec.ofNat 32 (slen.toNat / 65) := by
    show (if (0x41 : Word) = 0 then BitVec.allOnes 32 else BitVec.ofNat 32 (slen.toNat / (0x41 : Word).toNat)) = _
    rw [ite_eq_right (by decide)]; rfl
  have h65 : aluEval .add (BitVec.ofNat 32 (slen.toNat / 65)) (aluEval .sll (BitVec.ofNat 32 (slen.toNat / 65)) 6) =
      BitVec.ofNat 32 (65 * (slen.toNat / 65)) := BitVec.eq_of_toNat_eq (by
    show (BitVec.ofNat 32 (slen.toNat / 65) + (BitVec.ofNat 32 (slen.toNat / 65)) <<< ((6 : Word).toNat % 32)).toNat = _
    rw [show ((6 : Word).toNat % 32) = 6 from rfl, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := slen.isLt; omega)
  have hmod : aluEval .sub slen (BitVec.ofNat 32 (65 * (slen.toNat / 65))) = BitVec.ofNat 32 (slen.toNat % 65) :=
    BitVec.eq_of_toNat_eq (by
      show (slen - BitVec.ofNat 32 (65 * (slen.toNat / 65))).toNat = _
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; have := slen.isLt; omega)
  have v21a1 : reg m21 a1 = BitVec.ofNat 32 (slen.toNat % 65) := by
    rw [t21.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [v15a1, show reg m15 x0 = 0 from u15.zero, show aluEval .add (0 : Word) 65 = 0x41 from rfl, hdiv, h65, hmod]
  have v2124 : reg m21 24 = BitVec.ofNat 32 (65 * (slen.toNat / 65)) := by
    rw [t21.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [v15a1, show reg m15 x0 = 0 from u15.zero, show aluEval .add (0 : Word) 65 = 0x41 from rfl, hdiv, h65]
  have v21k : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ 24 → reg m21 r = reg m15 r := fun r h1 h2 h24 => by
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; rw [t21.self.zero, u15.zero]
    rw [t21.regs]; simp only [upd, hr, h1, h2, h24, ↓reduceIte]
  have u21 := t21.self
  have pre21 : Steps m m21 := pre15.trans (.cons e16 (.cons e17 (.cons e18 (.cons e19 (.cons e20 (.single e21))))))
  have k21 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ 9 → r ≠ 18 → r ≠ 24 → r ≠ sp → reg m21 r = reg m r :=
    fun r h0 h1 h2 h9 h18 h24 hsp' => (v21k r h1 h2 h24).trans (v15k r h0 h2 h9 h18 hsp')
  by_cases hm65 : ¬ slen.toNat % 65 = 0
  · obtain ⟨m22, e22, t22⟩ := u21.taken hc10 0xB8 csg_at_36 (by decide)
      (by
        rw [v21a1, show reg m21 x0 = 0 from u21.zero]
        refine bne_iff_ne.mpr fun h => hm65 ?_
        have := congrArg BitVec.toNat h; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this)
    refine exitAt M10 m22 (pre21.trans (.single e22)) t22.self hc10
      (by rw [t22.regs, v21k sp (by decide) (by decide) (by decide)]; exact v15sp) (fun _ _ _ => rfl)
      (by rw [t22.regs, k21 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [t22.regs, k21 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [t22.regs, k21 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [t22.regs, k21 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [t22.regs, k21 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [t22.regs, v21k a0 (by decide) (by decide) (by decide), v15a0]; unfold csResult; rw [ite_eq_left (Or.inr hm65)]; rfl)
      (fun x hx => by unfold csMem; rw [ite_eq_left (Or.inr hm65)]; exact M10out x hx)
  replace hm65 := Decidable.of_not_not hm65
  have hcond1 : ¬ (slen.toNat < 0x82 ∨ slen.toNat % 65 ≠ 0) := by
    rintro (h | h)
    · exact h82 h
    · exact h hm65
  obtain ⟨m22, e22, t22⟩ := u21.notTaken hc10 0x38 csg_at_36 (by decide)
    (by
      rw [v21a1, show reg m21 x0 = 0 from u21.zero, hm65]
      show (BitVec.ofNat 32 0 != 0) = false
      rfl)
  obtain ⟨m23, e23, t23⟩ := t22.alu hc10 csg_at_38 (off' := 0x3A) (by decide)
  obtain ⟨m24, e24, t24⟩ := t23.lui hc10 csg_at_3a (off' := 0x3C) (by decide)
  obtain ⟨m25, e25, t25⟩ := t24.aluImm hc10 csg_at_3c (off' := 0x3E) (by decide)
  have v25a0 : reg m25 a0 = 0x1002 := by rw [t25.regs]; simp +decide only [upd, ite_true, ite_false]
  have v25a6 : reg m25 a6 = plen := by
    rw [t25.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [k21 a6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ha6
  have v2521 : reg m25 21 = plen := by
    rw [t25.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [k21 a6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ha6]
    exact BitVec.zero_add plen
  have v25k : ∀ r, r ≠ a0 → r ≠ 21 → reg m25 r = reg m21 r := fun r h0 h21 => by
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; rw [t25.self.zero, u21.zero]
    rw [t25.regs]; simp only [upd, hr, h0, h21, ↓reduceIte]
  have u25 := t25.self
  have pre25 : Steps m m25 := pre21.trans (.cons e22 (.cons e23 (.cons e24 (.single e25))))
  by_cases hpl : ¬ plen.toNat ≤ 0x1002
  · obtain ⟨m26, e26, t26⟩ := u25.notTaken hc10 0x42 csg_at_3e (by decide)
      (by
        rw [v25a0, v25a6]
        show (!((0x1002 : Word).ult plen)) = false
        rw [show (0x1002 : Word).ult plen = true from decide_eq_true (by
          show (0x1002 : Word).toNat < plen.toNat; rw [show (0x1002 : Word).toNat = 0x1002 from rfl]; omega)]; rfl)
    obtain ⟨m27, e27, t27⟩ := t26.aluImm hc10 csg_at_42 (off' := 0x44) (by decide)
    obtain ⟨m28, e28, t28⟩ := t27.jump hc10 csg_at_44 (off' := 0xB8) (by decide) (by rw [t27.pc]; decide)
    have k28 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ 9 → r ≠ 18 → r ≠ 21 → r ≠ 24 → r ≠ sp → reg m28 r = reg m r :=
      fun r h0 h1 h2 h9 h18 h21 h24 hsp' => by
        rw [t28.regs, updz u25.zero h0, v25k r h0 h21]; exact k21 r h0 h1 h2 h9 h18 h24 hsp'
    refine exitAt M10 m28 (pre25.trans (.cons e26 (.cons e27 (.single e28)))) t28.self hc10
      (by rw [t28.regs, updz u25.zero (by decide), v25k sp (by decide) (by decide), v21k sp (by decide) (by decide)
        (by decide)]; exact v15sp) (fun _ _ _ => rfl)
      (k28 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (k28 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (k28 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (k28 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (k28 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (by
        rw [t28.regs]; simp +decide only [upd, ite_true, ite_false]
        unfold csResult; rw [ite_eq_right hcond1, ite_eq_left (by omega : 0x1002 < plen.toNat)]; rfl)
      (fun x hx => by unfold csMem; rw [ite_eq_right hcond1, ite_eq_left (by omega : 0x1002 < plen.toNat)]; exact M10out x hx)
  replace hpl := Decidable.of_not_not hpl
  have hcond2 : ¬ (0x1002 < plen.toNat) := by omega
  obtain ⟨m26, e26, t26⟩ := u25.taken hc10 0x46 csg_at_3e (by decide)
    (by
      rw [v25a0, v25a6]
      show (!((0x1002 : Word).ult plen)) = true
      rw [show (0x1002 : Word).ult plen = false from decide_eq_false (by
        show ¬ (0x1002 : Word).toNat < plen.toNat; rw [show (0x1002 : Word).toNat = 0x1002 from rfl]; omega)]; rfl)
  obtain ⟨m27, e27, t27⟩ := t26.alu hc10 csg_at_46 (off' := 0x48) (by decide)
  obtain ⟨m28, e28, t28⟩ := t27.alu hc10 csg_at_48 (off' := 0x4A) (by decide)
  obtain ⟨m29, e29, t29⟩ := t28.alu hc10 csg_at_4a (off' := 0x4C) (by decide)
  obtain ⟨m30, e30, t30⟩ := t29.aluImm hc10 csg_at_4c (off' := 0x50) (by decide)
  obtain ⟨m31, e31, t31⟩ := t30.aluImm hc10 csg_at_50 (off' := 0x52) (by decide)
  obtain ⟨m32, e32, t32⟩ := t31.alu hc10 csg_at_52 (off' := 0x54) (by decide)
  obtain ⟨m33, e33, t33⟩ := t32.alu hc10 csg_at_54 (off' := 0x56) (by decide)
  have k25m : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ 9 → r ≠ 18 → r ≠ 21 → r ≠ 24 → r ≠ sp → reg m25 r = reg m r :=
    fun r h0 h1 h2 h9 h18 h21 h24 hsp' => (v25k r h0 h21).trans (k21 r h0 h1 h2 h9 h18 h24 hsp')
  have g33 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ 19 → r ≠ 20 → r ≠ 22 → r ≠ 23 → reg m33 r = reg m25 r :=
    fun r h0 h1 h2 h19 h20 h22 h23 => by
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; rw [t33.self.zero, u25.zero]
      rw [t33.regs]; simp only [upd, hr, h0, h1, h2, h19, h20, h22, h23, ↓reduceIte]
  have m25r : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ 9 → r ≠ 18 → r ≠ 21 → r ≠ 24 → r ≠ sp → r ≠ 19 → r ≠ 20 →
      r ≠ 22 → r ≠ 23 → reg m33 r = reg m r := fun r h0 h1 h2 h9 h18 h21 h24 hsp' h19 h20 h22 h23 =>
    (g33 r h0 h1 h2 h19 h20 h22 h23).trans (k25m r h0 h1 h2 h9 h18 h21 h24 hsp')
  have v33a0 : reg m33 a0 = buf := by
    rw [t33.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [v25k 17 (by decide) (by decide), k21 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ha7]; exact BitVec.zero_add buf
  have v33a1 : reg m33 a1 = pre := by
    rw [t33.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [v25k a4 (by decide) (by decide), k21 a4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ha4]; exact BitVec.zero_add pre
  have v33a2 : reg m33 a2 = BitVec.ofNat 32 21 := by rw [t33.regs]; simp +decide only [upd, ite_true, ite_false]
  have v3323 : reg m33 23 = buf := by
    rw [t33.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [v25k 17 (by decide) (by decide), k21 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ha7]; exact BitVec.zero_add buf
  have v3322 : reg m33 22 = pay := by
    rw [t33.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [v25k a5 (by decide) (by decide), k21 a5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ha5]; exact BitVec.zero_add pay
  have v3320 : reg m33 20 = klen := by
    rw [t33.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [v25k a3 (by decide) (by decide), k21 a3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ha3]; exact BitVec.zero_add klen
  have v3319 : reg m33 19 = plen + 0x16 := by
    rw [t33.regs]; simp +decide only [upd, ite_true, ite_false]; rw [v2521]; rfl
  have v3321 : reg m33 21 = plen := by rw [g33 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v2521
  have v339 : reg m33 9 = sigs := by
    rw [g33 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v25k 9 (by decide) (by decide),
      v21k 9 (by decide) (by decide) (by decide)]; exact v159
  have v3318 : reg m33 18 = keys := by
    rw [g33 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v25k 18 (by decide) (by decide),
      v21k 18 (by decide) (by decide) (by decide)]; exact v1518
  have v3324 : reg m33 24 = BitVec.ofNat 32 (65 * (slen.toNat / 65)) := by
    rw [g33 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v25k 24 (by decide) (by decide)]
    exact v2124
  have v33sp : reg m33 sp = G := by
    rw [g33 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v25k sp (by decide) (by decide),
      v21k sp (by decide) (by decide) (by decide)]; exact v15sp
  have u33 := t33.self
  have pre33 : Steps m m33 := pre25.trans (.cons e26 (.cons e27 (.cons e28 (.cons e29 (.cons e30 (.cons e31 (.cons e32
    (.single e33))))))))
  obtain ⟨m34, c34, pc34, mem34, regs34⟩ := u33.callRa (cb := BitVec.ofNat 32 memcpyStubAddress) hc10 csg_at_56 csg_at_5a
    (by decide) (by decide)
  have r34 : ∀ r, r ≠ ra → reg m34 r = reg m33 r := fun r h => by rw [regs34]; exact updz u33.zero h
  have hG16 : G + 0xFFFFFFF0 = S + BitVec.ofNat 32 0x20A0 := by
    rw [hGS, show (0xFFFFFFF0 : Word) = BitVec.ofNat 32 0xFFFFFFF0 from rfl, BitVec.add_assoc, ofNat_add_ofNat]
    apply congrArg; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]
  have hG16n : (G + 0xFFFFFFF0).toNat = G.toNat - 16 := by
    rw [BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]; omega
  have stk16 : ∀ {a : Word} {n : Nat}, Sep a n S 0x20E0 → Sep a n (G + 0xFFFFFFF0) 16 := fun h => by
    rw [hG16]; exact h.subR (c := 0x20A0) (l := 16) (by omega)
  have hbufn : buf.toNat + 0x1018 ≤ 0x40000000 := hbw
  obtain ⟨m35, c35, pc35, sp35, a035, mem35, k35⟩ := memcpy_correct m34 (BitVec.ofNat 32 memcpyStubAddress)
    (CSG + BitVec.ofNat 32 (0x56 + 8)) buf pre 21 (by show CodeIn m34.mem _ _; rw [mem34]; exact codeM (by decide) (by decide) hst)
    (by decide) pc34 (by rw [r34 a0 (by decide)]; exact v33a0) (by rw [r34 a1 (by decide)]; exact v33a1)
    (by rw [r34 a2 (by decide)]; exact v33a2) (by rw [regs34]; simp +decide only [upd, ite_true, ite_false])
    (even_clear _ (by decide))
    ⟨by rw [mem34]; exact codeM (by decide) (by decide) hbd, lowSep (by omega) (by decide) (by decide),
      by rw [r34 sp (by decide), v33sp]; exact lowSep (by rw [hG16n]; omega) (by decide) (by decide),
      by rw [r34 sp (by decide), v33sp]; exact stk16 (by have := sBuf.sub (c := 0) (l := 21) (by omega); rwa [add_ofNat_zero] at this),
      by rw [r34 sp (by decide), v33sp]; exact stk16 sPre, bPre,
      by rw [r34 sp (by decide), v33sp, hG16n]; omega, by rw [r34 sp (by decide), v33sp, hG16n]; omega,
      by omega, hprew⟩
  rw [r34 sp (by decide), v33sp] at mem35 sp35
  have t35 : St m35.mem CSG m35 0x5E (reg m35) := ⟨by rw [pc35], rfl, fun _ => rfl⟩
  have hR35 : ∀ x, Sep (G + 0xFFFFFFF0) 16 x 1 → m35.mem x = copyBytes M10 buf pre 21 x := by
    rw [mem34] at mem35; exact mem35
  have k35' : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → r ≠ 5 → r ≠ 6 → r ≠ 7 →
      r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ ra → r ≠ sp → reg m35 r = reg m33 r :=
    fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hra hsp' =>
      (k35 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hsp').trans (r34 r hra)
  have code35 : ∀ {b : Word} {code : List Nat}, 0x40000000 ≤ b.toNat → b.toNat + code.length ≤ 2 ^ 32 →
      CodeIn m.mem b code → CodeIn m35.mem b code := by
    intro b code hb hbl hc' i hi
    have hx := code_hi hb hbl hi
    rw [hR35 _ (lowSep (by rw [hG16n]; omega) hx (by have := (b + BitVec.ofNat 32 i).isLt; omega)), copyBytes]
    rw [ite_eq_right (by
      intro h
      have h1 := (b + BitVec.ofNat 32 i - buf).isLt
      rw [BitVec.toNat_sub] at h
      omega)]
    exact codeM hb hbl hc' i hi
  have hc35 := code35 (by decide) (by decide) hc
  have hb15 : (buf + 0x15).toNat = buf.toNat + 0x15 := by
    rw [BitVec.toNat_add, show (0x15 : Word).toNat = 0x15 from rfl]; omega
  have hb16 : (buf + 0x16).toNat = buf.toNat + 0x16 := by
    rw [BitVec.toNat_add, show (0x16 : Word).toNat = 0x16 from rfl]; omega
  have v3523 : reg m35 23 = buf := by rw [k35' 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v3323
  obtain ⟨m36, e36, t36⟩ := t35.aluImm hc35 csg_at_5e (off' := 0x62) (by decide)
  have u36 := t36.self
  have r36 : ∀ r, r ≠ a0 → reg m36 r = reg m35 r := fun r h => by rw [t36.regs]; exact updz t35.zero h
  have v36a0 : reg m36 a0 = buf + 0x16 := by
    rw [t36.regs]; simp +decide only [upd, ite_true, ite_false]; rw [v3523]; rfl
  obtain ⟨m37, e37, t37⟩ := u36.sbG hc35 csg_at_62 (off' := 0x66) (by decide) (a := buf + 0x15) (v := 0)
    (by rw [r36 23 (by decide), v3523]) u36.zero
  rw [show (0 : Word).extractLsb' 0 8 = (0 : BitVec 8) from rfl] at t37
  have code37 : ∀ {b : Word} {code : List Nat}, 0x40000000 ≤ b.toNat → b.toNat + code.length ≤ 2 ^ 32 →
      CodeIn m.mem b code → CodeIn (memStore8 m35.mem (buf + 0x15) 0) b code := by
    intro b code hb hbl hc'
    exact (code35 hb hbl hc').store8 (lowSep (by rw [hb15]; omega) hb hbl)
  have hc37 := code37 (by decide) (by decide) hc
  have u37 := t37.self
  obtain ⟨m38, e38, t38⟩ := u37.alu hc37 csg_at_66 (off' := 0x68) (by decide)
  have u38 := t38.self
  obtain ⟨m39, e39, t39⟩ := u38.alu hc37 csg_at_68 (off' := 0x6A) (by decide)
  have u39 := t39.self
  obtain ⟨m40, e40, t40⟩ := u39.alu hc37 csg_at_6a (off' := 0x6C) (by decide)
  have u40 := t40.self
  obtain ⟨m41, c41, pc41, mem41, regs41⟩ := u40.callRa (cb := BitVec.ofNat 32 copyFromSliceU8Address) hc37
    csg_at_6c csg_at_70 (by decide) (by decide)
  have w41 : ∀ r, r ≠ ra → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m41 r = reg m36 r := fun r h0 h1 h2 h3 => by
    rw [regs41, updz u40.zero h0, t40.regs, updz u39.zero h3, t39.regs, updz u38.zero h2, t38.regs,
      updz u37.zero h1, t37.regs]
  have w41a1 : reg m41 a1 = reg m36 21 := by
    rw [regs41, updz u40.zero (by decide), t40.regs, updz u39.zero (by decide), t39.regs, updz u38.zero (by decide),
      t38.regs]; simp +decide only [upd, ite_true, ite_false]; rw [u37.zero, t37.regs]; exact BitVec.zero_add _
  have w41a2 : reg m41 a2 = reg m36 22 := by
    rw [regs41, updz u40.zero (by decide), t40.regs, updz u39.zero (by decide), t39.regs]
    simp +decide only [upd, ite_true, ite_false]; rw [u38.zero, t38.regs, updz u37.zero (by decide), t37.regs]
    exact BitVec.zero_add _
  have w41a3 : reg m41 a3 = reg m36 21 := by
    rw [regs41, updz u40.zero (by decide), t40.regs]
    simp +decide only [upd, ite_true, ite_false]; rw [u39.zero, t39.regs, updz u38.zero (by decide), t38.regs,
      updz u37.zero (by decide), t37.regs]
    exact BitVec.zero_add _
  have v3621 : reg m36 21 = BitVec.ofNat 32 plen.toNat := by
    rw [r36 21 (by decide), k35' 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v3321]
    exact (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt plen.isLt])).symm
  have hsp41 : reg m41 sp = G := by
    rw [w41 sp (by decide) (by decide) (by decide) (by decide), r36 sp (by decide)]; exact sp35
  have hpl' : plen.toNat ≤ 0x1002 := by omega
  have hGm : G.toNat % 16 = 0 := by rw [hGn]; omega
  obtain ⟨m42, c42, pc42, sp42, a042, mem42, k42⟩ := copyFromSliceU8_correct m41
    (W := BitVec.ofNat 32 copyFromSliceU8Address) (retAddr := CSG + BitVec.ofNat 32 (0x6C + 8))
    (dst := buf + 0x16) (src := pay) (n := plen.toNat) (by decide)
    (by rw [mem41]; exact code37 (by decide) (by decide) hcf)
    (by rw [mem41, show (BitVec.ofNat 32 copyFromSliceU8Address + 0x761E : Word) = BitVec.ofNat 32 memcpyStubAddress
      from by decide]; exact code37 (by decide) (by decide) hst)
    pc41 (by rw [w41 a0 (by decide) (by decide) (by decide) (by decide)]; exact v36a0) (by rw [w41a1]; exact v3621)
    (by rw [w41a2, r36 22 (by decide), k35' 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v3322) (by rw [w41a3]; exact v3621)
    (by rw [regs41]; simp +decide only [upd, ite_true, ite_false]) (even_clear _ (by decide))
    (by
      rw [hsp41, mem41, show (BitVec.ofNat 32 copyFromSliceU8Address + 0x761E + 8 : Word) =
        BitVec.ofNat 32 memcpyStubAddress + 8 from by decide]
      exact ⟨code37 (by decide) (by decide) hbd, lowSep (by rw [hb16]; omega) (by decide) (by decide),
        lowSep (by rw [hG16n]; omega) (by decide) (by decide),
        stk16 (sBuf.sub (c := 0x16) (l := plen.toNat) (by omega) : Sep (buf + 0x16) _ _ _), stk16 (sPay hpl'),
        bPay hpl', by rw [hG16n]; omega, by rw [hG16n]; omega, by rw [hb16]; omega, hpayw hpl'⟩)
  have oT : ∀ x : Word, BitVec.ofNat 32 x.toNat = x := fun x =>
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])
  have hsc : ∀ y, Sep S 0x20E0 y 1 → Sep (G + 0xFFFFFFF0) 16 y 1 := fun y h => by
    rw [hG16]; exact h.sub (c := 0x20A0) (l := 16) (by omega)
  have mem42' : ∀ y, Sep (G + 0xFFFFFFF0) 16 y 1 →
      m42.mem y = copyBytes (memStore8 m35.mem (buf + 0x15) 0) (buf + 0x16) pay plen.toNat y := by
    intro y hy; rw [mem42 y (by rw [hsp41]; exact hy), mem41]
  have F42 : ∀ y, Sep (G + 0xFFFFFFF0) 16 y 1 → Sep buf 0x1018 y 1 → m42.mem y = M10 y := by
    intro y hy hb
    rw [mem42' y hy, copyBytes_sep (dst := buf + 0x16) (n := plen.toNat)
      (hb.sub (c := 0x16) (l := plen.toNat) (by omega)) (Nat.le_refl _),
      memStore8_ne (fun e => hb 0x15 (by omega) 0 (by omega) (by rw [add_ofNat_zero, e]; try rfl)), hR35 y hy,
      copyBytes_sep (n := 21) (by have := hb.sub (c := 0) (l := 21) (by omega); rwa [add_ofNat_zero] at this)
        (Nat.le_refl _)]
  have R : ∀ y, Sep S 0x20E0 y 1 →
      memStore8 m35.mem (buf + 0x15) 0 y = memStore8 (copyBytes m.mem buf pre 21) (buf + 0x15) 0 y := by
    intro y hy
    apply memStore8_congr
    rw [hR35 y (hsc y hy)]
    apply copyBytes_pt (M10out y hy)
    intro hlt
    apply M10out
    rw [← oT (y - buf)]
    exact (sPre.sub (c := (y - buf).toNat) (l := 1) (by omega)).symm
  have Q : ∀ y, Sep S 0x20E0 y 1 → m42.mem y = csMsgMem m.mem buf pre pay plen.toNat y := by
    intro y hy
    rw [mem42' y (hsc y hy)]; unfold csMsgMem
    apply copyBytes_pt (R y hy)
    intro hlt
    apply R
    rw [← oT (y - (buf + 0x16))]
    exact ((sPay hpl').sub (c := (y - (buf + 0x16)).toNat) (l := 1) (by omega)).symm
  have P : ∀ y, Sep S 0x20E0 y 1 → Sep buf 0x1018 y 1 → m42.mem y = m.mem y := fun y hy hb =>
    (F42 y (hsc y hy) hb).trans (M10out y hy)
  have hi42 : ∀ x : Word, 0x40000000 ≤ x.toNat → m42.mem x = m.mem x := fun x hx =>
    P x (hiS x hx) (lowSep (by omega) hx (by have := x.isLt; omega))
  have hro42 : RoAgree m42.mem m.mem := fun i hi => by
    rw [← ofNat_add_ofNat]
    exact P _ (sRo.sub (c := i) (l := 1) (by omega)).symm (bRo.subR (c := i) (l := 1) (by omega))
  have hc42 : CodeIn m42.mem CSG checkSignaturesCode := fun i hi => by
    rw [hi42 _ (code_hi (by decide) (by decide) hi)]; exact hc i hi
  have t42 : St m42.mem CSG m42 0x74 (reg m42) := ⟨by rw [pc42], rfl, fun _ => rfl⟩
  obtain ⟨m43, e43, t43⟩ := t42.aluImm hc42 csg_at_74 (off' := 0x76) (by decide)
  have u43 := t43.self
  obtain ⟨m44, e44, t44⟩ := u43.aluImm hc42 csg_at_76 (off' := 0x7A) (by decide)
  have r44 : ∀ r, r ≠ a1 → r ≠ 20 → reg m44 r = reg m42 r := fun r h1 h20 => by
    rw [t44.regs, updz u43.zero h20, t43.regs, updz t42.zero h1]
  have g42 : ∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → r ≠ 5 →
      r ≠ 6 → r ≠ 7 → r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ sp → reg m42 r = reg m33 r :=
    fun r hra h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hsp' => by
      rw [k42 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hsp', w41 r hra h1 h2 h3, r36 r h0]
      exact k35' r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hra hsp'
  have v44a1 : reg m44 a1 = BitVec.ofNat 32 0 := by
    rw [t44.regs, updz u43.zero (by decide), t43.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [t42.zero]; rfl
  have v44_20 : reg m44 20 = BitVec.ofNat 32 (klen.toNat / 32) := by
    rw [t44.regs]; simp +decide only [upd, ite_true, ite_false]
    rw [t43.regs, updz t42.zero (by decide), g42 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v3320]
    apply BitVec.eq_of_toNat_eq; rw [srl5_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hFn : (G + 0xFFFFE960).toNat = G.toNat - 0x16A0 := by
    rw [BitVec.toNat_add, show (0xFFFFE960 : Word).toNat = 2 ^ 32 - 0x16A0 from rfl]; omega
  have hevS : evG (G + 0xFFFFE960) = S := BitVec.eq_of_toNat_eq (by
    unfold evG; rw [BitVec.toNat_add, hFn, show (0xFFFFF5F0 : Word).toNat = 2 ^ 32 - 0xA10 from rfl, hSn]; omega)
  have hspF : G = (G + 0xFFFFE960) + BitVec.ofNat 32 0x16A0 := by
    rw [BitVec.add_assoc, show (0xFFFFE960 : Word) + BitVec.ofNat 32 0x16A0 = 0 from by decide]; exact (BitVec.add_zero G).symm
  have shr : ∀ {a : Word} {n : Nat}, Sep a n S 0x20E0 → Sep a n (evG (G + 0xFFFFE960)) 0x20B0 := by
    intro a n h; rw [hevS]; have := h.subR (c := 0) (l := 0x20B0) (by omega); rwa [add_ofNat_zero] at this
  obtain ⟨mL, cL, tL, aL, memL, spL, kL3, kL4, kL25, kL26, kL27⟩ := cs_loop (F := G + 0xFFFFE960) (keys := keys)
    (buf := buf) (mlen := plen.toNat + 0x16) (nkeys := klen.toNat / 32) (M1 := m42.mem)
    (E.congr hi42 hro42) hc42 (by rw [hFn]; omega) (by rw [hFn]; omega) (by rw [hFn]; omega) (shr sRo)
    (by rw [s5Hv_ro hro42]; exact iv) (shr sK) hkw
    (shr (by have := sBuf.sub (c := 0) (l := plen.toNat + 0x16) (by omega); rwa [add_ofNat_zero] at this))
    (by omega) (by omega)
    (slen.toNat / 65) m44 sigs 0 (fun j hj => shr (sSig.sub (c := 65 * j) (l := 65) (by omega))) (by omega)
    ⟨t44.pc, rfl, fun _ => rfl⟩ (fun x _ => by rw [t44.mem])
    (by rw [r44 sp (by decide) (by decide), sp42, hsp41]; exact hspF)
    (by rw [r44 24 (by decide) (by decide), g42 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v3324)
    (by rw [r44 9 (by decide) (by decide), g42 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v339)
    v44a1 (by omega)
    (by rw [r44 18 (by decide) (by decide), g42 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v3318)
    (by
      rw [r44 19 (by decide) (by decide), g42 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v3319]
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x16 : Word).toNat = 0x16 from rfl])
    v44_20
    (by rw [r44 23 (by decide) (by decide), g42 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v3323)
  have outL : ∀ x, Sep S 0x20B0 x 1 → mL.mem x = m42.mem x := fun x hx => memL x (by rw [hevS]; exact hx)
  refine exitAt mL.mem mL (pre33.trans (c34.trans (c35.trans (.cons e36 (.cons e37 (.cons e38 (.cons e39 (.cons e40
    (c41.trans (c42.trans (.cons e43 (.cons e44 cL)))))))))))) tL
    (fun i hi => by
      have hx : 0x40000000 ≤ (CSG + BitVec.ofNat 32 i).toNat := code_hi (by decide) (by decide) hi
      rw [outL _ (lowSep (by rw [hSn]; omega) hx (by have := (CSG + BitVec.ofNat 32 i).isLt; omega))]
      exact hc42 i hi)
    (by rw [spL]; exact hspF.symm)
    (fun c hc8 hc30 => memLoad32_congr (fun j hj => by
      have hy : G + BitVec.ofNat 32 c + BitVec.ofNat 32 j = S + BitVec.ofNat 32 (0x20B0 + (c + j)) := by
        rw [add_ofNat_assoc, hGS, add_ofNat_assoc]
      rw [hy, outL _ (by
          have := sep_offsets S (c := 0) (n := 0x20B0) (d := 0x20B0 + (c + j)) (k := 1) (Or.inl (by omega))
            (by omega) (by omega)
          rwa [add_ofNat_zero] at this),
        F42 _ (by rw [hG16]; exact sep_offsets S (Or.inl (by omega)) (by omega) (by omega))
          (sBuf.subR (c := 0x20B0 + (c + j)) (l := 1) (by omega))]))
    (kL3.trans ((r44 3 (by decide) (by decide)).trans ((g42 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (m25r 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))))) (kL4.trans ((r44 4 (by decide) (by decide)).trans ((g42 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (m25r 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))))) (kL25.trans ((r44 25 (by decide) (by decide)).trans ((g42 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (m25r 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))))) (kL26.trans ((r44 26 (by decide) (by decide)).trans ((g42 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (m25r 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))))) (kL27.trans ((r44 27 (by decide) (by decide)).trans ((g42 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (m25r 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))))
    (by
      rw [aL]; unfold csResult; rw [ite_eq_right hcond1, ite_eq_right hcond2]
      rw [csLoop_congr (M' := csMsgMem m.mem buf pre pay plen.toNat)
        (fun i hi => by rw [← ofNat_add_ofNat]; exact Q _ (sRo.sub (c := i) (l := 1) (by omega)).symm)
        (fun i hi => Q _ (sK.sub (c := i) (l := 1) (by omega)).symm)
        (fun i hi => Q _ (sBuf.sub (c := i) (l := 1) (by omega)).symm)
        (slen.toNat / 65) sigs 0 (fun i hi => Q _ (sSig.sub (c := i) (l := 1) (by omega)).symm)])
    (fun x hx => by
      unfold csMem; rw [ite_eq_right hcond1, ite_eq_right hcond2,
        outL x (by have := hx.sub (c := 0) (l := 0x20B0) (by omega); rwa [add_ofNat_zero] at this)]
      exact Q x hx)

end C3.RV32
