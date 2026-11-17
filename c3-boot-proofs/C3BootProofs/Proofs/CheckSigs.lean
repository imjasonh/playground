import C3BootProofs.Proofs.Ed25519VerifyC
import C3BootProofs.Proofs.KeySet

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

abbrev CSG : Word := BitVec.ofNat 32 checkSignaturesAddress

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
  have roC : ∀ {A : Nat} {code : List Nat}, 0x3FCC4000 ≤ A → A + code.length ≤ 0x3FCC5400 →
      CodeIn M (BitVec.ofNat 32 A) code → CodeIn M' (BitVec.ofNat 32 A) code := by
    intro A code h1 h2 hc i hi
    have := hro (A - 0x3FCC4000 + i) (by omega)
    rw [show 0x3FCC4000 + (A - 0x3FCC4000 + i) = A + i by omega] at this
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
    s5Hv M (BitVec.ofNat 32 0x3FCC4AF8) = s5Hv M' (BitVec.ofNat 32 0x3FCC4AF8) := by
  have L : ∀ c, c + 4 ≤ 0x40 → memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + BitVec.ofNat 32 c) =
      memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + BitVec.ofNat 32 c) := fun c hc => by
    rw [ofNat_add_ofNat]; exact ro_ld hro _ (by omega) (by omega)
  have L0 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0x0) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0x0) :=
    L 0 (by omega)
  have L4 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0x4) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0x4) :=
    L 4 (by omega)
  have L8 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0x8) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0x8) :=
    L 8 (by omega)
  have L12 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0xC) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0xC) :=
    L 12 (by omega)
  have L16 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0x10) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0x10) :=
    L 16 (by omega)
  have L20 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0x14) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0x14) :=
    L 20 (by omega)
  have L24 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0x18) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0x18) :=
    L 24 (by omega)
  have L28 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0x1C) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0x1C) :=
    L 28 (by omega)
  have L32 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0x20) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0x20) :=
    L 32 (by omega)
  have L36 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0x24) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0x24) :=
    L 36 (by omega)
  have L40 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0x28) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0x28) :=
    L 40 (by omega)
  have L44 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0x2C) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0x2C) :=
    L 44 (by omega)
  have L48 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0x30) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0x30) :=
    L 48 (by omega)
  have L52 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0x34) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0x34) :=
    L 52 (by omega)
  have L56 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0x38) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0x38) :=
    L 56 (by omega)
  have L60 : memLoad32 M (BitVec.ofNat 32 0x3FCC4AF8 + 0x3C) = memLoad32 M' (BitVec.ofNat 32 0x3FCC4AF8 + 0x3C) :=
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

end C3.RV32



