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

set_option maxRecDepth 40000 in
set_option maxHeartbeats 32000000 in
/-- The signature loop, from offset 0x7A to the epilogue with `a0` holding
the result. -/
theorem cs_loop {F keys buf : Word} {mlen nkeys : Nat} {M1 : Word → BitVec 8}
    (E1 : EvEnv M1) (hc1 : CodeIn M1 CSG checkSignaturesCode)
    (hF : F.toNat % 16 = 0) (hlo : 0xA10 ≤ F.toNat) (hhi : F.toNat + 0x16A0 ≤ 0x40000000)
    (sRo : Sep (BitVec.ofNat 32 0x3FCC4000) 0x1400 (evG F) 0x20B0)
    (iv1 : (s5Hv M1 (BitVec.ofNat 32 0x3FCC4AF8)).toList = Sha512.h0)
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

end C3.RV32

