import C3BootProofs.Proofs.SvExtLoop
import C3BootProofs.Proofs.SvTsaLink

/-!
# The leaf's extensions the code read, as `readExtensions`

The code's loop over the extensions (`sv_extStep`) as `readExtensionList`:
each pass reads one extension, checks its criticality and that its OID is
new, and dispatches on the OID, setting a flag or a policy slot. The flags
at 0x34 and 0x30 are `keyUsage` and `codeSigning`; the five slots are the
five identity-policy strings.
-/

namespace C3.RV32.Sv

open C3.Image

/-- The code's flags and slots, against the specification's `ExtState`. -/
def extRel (M : Word → BitVec 8) (st : ExtState) (f30 f34 sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 : Word) : Prop :=
  (f30 = 0 ∨ f30 = 1) ∧ (f34 = 0 ∨ f34 = 1) ∧ (f34 = 1 → st.keyUsage = true) ∧ (f30 = 1 → st.codeSigning = true) ∧
  st.policy.length = 5 ∧
  (sl0 ≠ 0 → st.policy[0]? = some (some (memBytes M sl0 sl1.toNat))) ∧
  (sl2 ≠ 0 → st.policy[1]? = some (some (memBytes M sl2 sl3.toNat))) ∧
  (sl4 ≠ 0 → st.policy[2]? = some (some (memBytes M sl4 sl5.toNat))) ∧
  (sl6 ≠ 0 → st.policy[3]? = some (some (memBytes M sl6 sl7.toNat))) ∧
  (sl8 ≠ 0 → st.policy[4]? = some (some (memBytes M sl8 sl9.toNat)))

/-- The constants the extensions loop compares OIDs with, as the
specification's OIDs. -/
structure ExtConsts (M : Word → BitVec 8) : Prop where
  ku : memBytes M (BitVec.ofNat 32 0x3FCC4889) 3 = oidKeyUsage
  san : memBytes M (BitVec.ofNat 32 0x3FCC488C) 3 = oidSubjectAltName
  bc : memBytes M (BitVec.ofNat 32 0x3FCC488F) 3 = oidBasicConstraints
  eku : memBytes M (BitVec.ofNat 32 0x3FCC4892) 3 = oidExtKeyUsage
  cs : memBytes M (BitVec.ofNat 32 0x3FCC4820) 8 = oidCodeSigning
  p0 : memBytes M (BitVec.ofNat 32 0x3FCC48B8) 10 = oidFulcio 8
  p1 : memBytes M (BitVec.ofNat 32 0x3FCC48C2) 10 = oidFulcio 9
  p2 : memBytes M (BitVec.ofNat 32 0x3FCC48CC) 10 = oidFulcio 15
  p3 : memBytes M (BitVec.ofNat 32 0x3FCC48D6) 10 = oidFulcio 17
  p4 : memBytes M (BitVec.ofNat 32 0x3FCC48E0) 10 = oidFulcio 20

theorem extList_nil {earlier : Bytes} {fuel : Nat} {st : ExtState} : readExtensionList earlier fuel [] st = some st := by
  cases fuel <;> rfl

theorem memBytes_cons {M : Word → BitVec 8} {p : Word} {n : Nat} (h : n ≠ 0) :
    ∃ a l, memBytes M p n = a :: l := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  exact ⟨_, _, memBytes_succ M p n'⟩

theorem beq_false_of_ne {a b : Bytes} (h : ¬ a = b) : (a == b) = false :=
  Bool.eq_false_iff.mpr fun e => h (beq_iff_eq.mp e)

theorem idxOf_none {x : Bytes} (h0 : ¬ x = oidFulcio 8) (h1 : ¬ x = oidFulcio 9) (h2 : ¬ x = oidFulcio 15)
    (h3 : ¬ x = oidFulcio 17) (h4 : ¬ x = oidFulcio 20) : List.idxOf? x policyOids = none := by
  unfold policyOids
  simp only [List.idxOf?, List.findIdx?, List.findIdx?.go]
  simp only [beq_false_of_ne (Ne.symm h0), beq_false_of_ne (Ne.symm h1), beq_false_of_ne (Ne.symm h2),
    beq_false_of_ne (Ne.symm h3), beq_false_of_ne (Ne.symm h4), Bool.false_eq_true, ↓reduceIte]

theorem extRel_policy {st : ExtState} {i : Nat} {s : Bytes} (hi : i < 5) (hl : st.policy.length = 5) :
    (st.policy.set i (some s))[i]? = some (some s) ∧ (st.policy.set i (some s)).length = 5 ∧
      ∀ j, j ≠ i → (st.policy.set i (some s))[j]? = st.policy[j]? := by
  refine ⟨?_, by rw [List.length_set, hl], fun j hj => ?_⟩
  · rw [List.getElem?_set_self (by omega)]
  · rw [List.getElem?_set_ne (Ne.symm hj)]

set_option maxHeartbeats 8000000 in
/-- The code's dispatch on an extension's OID, as `readExtensionList`'s,
for any continuation that keeps the relation between the flags and slots. -/
theorem ext_dispatch {M : Word → BitVec 8}
    {B out bp x9 x21 x25 x26 p0 L w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 : Word} {v : Nat → Word}
    {f30 f34 rem cur a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 op ol x3c x38 : Word} {tl8 : DerTlv}
    {d30 d34 d20 d24 d28 d2c d30' d34' d38 d3c d40 d44 : Word} {st : ExtState} {cont : ExtState → Option ExtState}
    {Q : ExtState → Prop} (K : ExtConsts M)
    (hdisp : (((memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4889) 3) ∧ ∃ tl16_1, derElement 0x3 (memBytes M (x3c) (x38).toNat) = .ok tl16_1 ∧ (2 ≤ (BitVec.ofNat 32 tl16_1.len).toNat) ∧ (BitVec.ofNat 32 (kuUnused (M (((((x3c) + BitVec.ofNat 32 tl16_1.header)) + ((BitVec.ofNat 32 tl16_1.len))) + BitVec.ofNat 32 0xFFFFFFFF))) = (M ((x3c) + BitVec.ofNat 32 tl16_1.header)).zeroExtend 32) ∧ (((x38) - BitVec.ofNat 32 (tl16_1.header + tl16_1.len)) = 0) ∧ (¬ (M (((x3c) + BitVec.ofNat 32 tl16_1.header) + 0x1)).toNat < 0x80) ∧ d30 = f30 ∧ d34 = BitVec.ofNat 32 0x1 ∧ d20 = a0 ∧ d24 = a1 ∧ d28 = a2 ∧ d2c = a3 ∧ d30' = a4 ∧ d34' = a5 ∧ d38 = a6 ∧ d3c = a7 ∧ d40 = a8 ∧ d44 = a9) ∨ ((¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4889) 3)) ∧ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4892) 3) ∧ ∃ tl19_1, derElement 0x30 (memBytes M (x3c) (x38).toNat) = .ok tl19_1 ∧ ((x38) - BitVec.ofNat 32 (tl19_1.header + tl19_1.len) = 0) ∧ ∃ k_2 found'_2 cp'_2 cl'_2, svChain (sv_ekuStep B out bp x9 x21 x25 x26 f30 f34 rem p0 L ((cur) + BitVec.ofNat 32 (tl8.header + tl8.len)) a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 ((rem) - BitVec.ofNat 32 (tl8.header + tl8.len)) v M) k_2 ((BitVec.ofNat 32 0x0), ((x3c) + BitVec.ofNat 32 tl19_1.header), (BitVec.ofNat 32 tl19_1.len)) (found'_2, cp'_2, cl'_2) ∧ cl'_2 = 0 ∧ (found'_2 &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ d30 = BitVec.ofNat 32 0x1 ∧ d34 = f34 ∧ d20 = a0 ∧ d24 = a1 ∧ d28 = a2 ∧ d2c = a3 ∧ d30' = a4 ∧ d34' = a5 ∧ d38 = a6 ∧ d3c = a7 ∧ d40 = a8 ∧ d44 = a9) ∨ ((¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4889) 3)) ∧ (¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4892) 3)) ∧ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC488F) 3) ∧ ∃ tl24_1, derElement 0x30 (memBytes M (x3c) (x38).toNat) = .ok tl24_1 ∧ ((x38) - BitVec.ofNat 32 (tl24_1.header + tl24_1.len) = 0) ∧ ((((BitVec.ofNat 32 tl24_1.len) = 0)) ∨ ((¬ ((BitVec.ofNat 32 tl24_1.len) = 0)) ∧ (M ((x3c) + BitVec.ofNat 32 tl24_1.header) ≠ BitVec.ofNat 8 1) ∧ (M ((x3c) + BitVec.ofNat 32 tl24_1.header) = BitVec.ofNat 8 2) ∧ ∃ ip10 il10, derIntOf (memBytes M (((x3c) + BitVec.ofNat 32 tl24_1.header)) ((BitVec.ofNat 32 tl24_1.len)).toNat) (((x3c) + BitVec.ofNat 32 tl24_1.header)) (derElement 2 (memBytes M (((x3c) + BitVec.ofNat 32 tl24_1.header)) ((BitVec.ofNat 32 tl24_1.len)).toNat)) = .ok (ip10, il10) ∧ ∃ ti10, derElement 2 (memBytes M (((x3c) + BitVec.ofNat 32 tl24_1.header)) ((BitVec.ofNat 32 tl24_1.len)).toNat) = .ok ti10 ∧ (((BitVec.ofNat 32 tl24_1.len)) - BitVec.ofNat 32 (ti10.header + ti10.len) = 0))) ∧ d30 = f30 ∧ d34 = f34 ∧ d20 = a0 ∧ d24 = a1 ∧ d28 = a2 ∧ d2c = a3 ∧ d30' = a4 ∧ d34' = a5 ∧ d38 = a6 ∧ d3c = a7 ∧ d40 = a8 ∧ d44 = a9) ∨ ((¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4889) 3)) ∧ (¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4892) 3)) ∧ (¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC488F) 3)) ∧ (memBytes M (BitVec.ofNat 32 0x3FCC48B8) 10 = memBytes M op ol.toNat) ∧ ∃ tl35, derTlv (memBytes M (x3c) (x38).toNat) = .ok tl35 ∧ (BitVec.ofNat 8 tl35.tag = BitVec.ofNat 8 0xC) ∧ ((x38) - BitVec.ofNat 32 (tl35.header + tl35.len) = 0) ∧ d30 = f30 ∧ d34 = f34 ∧ d20 = (x3c) + BitVec.ofNat 32 tl35.header ∧ d24 = BitVec.ofNat 32 tl35.len ∧ d28 = a2 ∧ d2c = a3 ∧ d30' = a4 ∧ d34' = a5 ∧ d38 = a6 ∧ d3c = a7 ∧ d40 = a8 ∧ d44 = a9) ∨ ((¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4889) 3)) ∧ (¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4892) 3)) ∧ (¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC488F) 3)) ∧ (¬ (memBytes M (BitVec.ofNat 32 0x3FCC48B8) 10 = memBytes M op ol.toNat)) ∧ (memBytes M (BitVec.ofNat 32 0x3FCC48C2) 10 = memBytes M op ol.toNat) ∧ ∃ tl43, derTlv (memBytes M (x3c) (x38).toNat) = .ok tl43 ∧ (BitVec.ofNat 8 tl43.tag = BitVec.ofNat 8 0xC) ∧ ((x38) - BitVec.ofNat 32 (tl43.header + tl43.len) = 0) ∧ d30 = f30 ∧ d34 = f34 ∧ d20 = a0 ∧ d24 = a1 ∧ d28 = (x3c) + BitVec.ofNat 32 tl43.header ∧ d2c = BitVec.ofNat 32 tl43.len ∧ d30' = a4 ∧ d34' = a5 ∧ d38 = a6 ∧ d3c = a7 ∧ d40 = a8 ∧ d44 = a9) ∨ ((¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4889) 3)) ∧ (¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4892) 3)) ∧ (¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC488F) 3)) ∧ (¬ (memBytes M (BitVec.ofNat 32 0x3FCC48B8) 10 = memBytes M op ol.toNat)) ∧ (¬ (memBytes M (BitVec.ofNat 32 0x3FCC48C2) 10 = memBytes M op ol.toNat)) ∧ (memBytes M (BitVec.ofNat 32 0x3FCC48CC) 10 = memBytes M op ol.toNat) ∧ ∃ tl51, derTlv (memBytes M (x3c) (x38).toNat) = .ok tl51 ∧ (BitVec.ofNat 8 tl51.tag = BitVec.ofNat 8 0xC) ∧ ((x38) - BitVec.ofNat 32 (tl51.header + tl51.len) = 0) ∧ d30 = f30 ∧ d34 = f34 ∧ d20 = a0 ∧ d24 = a1 ∧ d28 = a2 ∧ d2c = a3 ∧ d30' = (x3c) + BitVec.ofNat 32 tl51.header ∧ d34' = BitVec.ofNat 32 tl51.len ∧ d38 = a6 ∧ d3c = a7 ∧ d40 = a8 ∧ d44 = a9) ∨ ((¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4889) 3)) ∧ (¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4892) 3)) ∧ (¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC488F) 3)) ∧ (¬ (memBytes M (BitVec.ofNat 32 0x3FCC48B8) 10 = memBytes M op ol.toNat)) ∧ (¬ (memBytes M (BitVec.ofNat 32 0x3FCC48C2) 10 = memBytes M op ol.toNat)) ∧ (¬ (memBytes M (BitVec.ofNat 32 0x3FCC48CC) 10 = memBytes M op ol.toNat)) ∧ (memBytes M (BitVec.ofNat 32 0x3FCC48D6) 10 = memBytes M op ol.toNat) ∧ ∃ tl59, derTlv (memBytes M (x3c) (x38).toNat) = .ok tl59 ∧ (BitVec.ofNat 8 tl59.tag = BitVec.ofNat 8 0xC) ∧ ((x38) - BitVec.ofNat 32 (tl59.header + tl59.len) = 0) ∧ d30 = f30 ∧ d34 = f34 ∧ d20 = a0 ∧ d24 = a1 ∧ d28 = a2 ∧ d2c = a3 ∧ d30' = a4 ∧ d34' = a5 ∧ d38 = (x3c) + BitVec.ofNat 32 tl59.header ∧ d3c = BitVec.ofNat 32 tl59.len ∧ d40 = a8 ∧ d44 = a9) ∨ ((¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4889) 3)) ∧ (¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4892) 3)) ∧ (¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC488F) 3)) ∧ (¬ (memBytes M (BitVec.ofNat 32 0x3FCC48B8) 10 = memBytes M op ol.toNat)) ∧ (¬ (memBytes M (BitVec.ofNat 32 0x3FCC48C2) 10 = memBytes M op ol.toNat)) ∧ (¬ (memBytes M (BitVec.ofNat 32 0x3FCC48CC) 10 = memBytes M op ol.toNat)) ∧ (¬ (memBytes M (BitVec.ofNat 32 0x3FCC48D6) 10 = memBytes M op ol.toNat)) ∧ (memBytes M (BitVec.ofNat 32 0x3FCC48E0) 10 = memBytes M op ol.toNat) ∧ ∃ tl67, derTlv (memBytes M (x3c) (x38).toNat) = .ok tl67 ∧ (BitVec.ofNat 8 tl67.tag = BitVec.ofNat 8 0xC) ∧ ((x38) - BitVec.ofNat 32 (tl67.header + tl67.len) = 0) ∧ d30 = f30 ∧ d34 = f34 ∧ d20 = a0 ∧ d24 = a1 ∧ d28 = a2 ∧ d2c = a3 ∧ d30' = a4 ∧ d34' = a5 ∧ d38 = a6 ∧ d3c = a7 ∧ d40 = (x3c) + BitVec.ofNat 32 tl67.header ∧ d44 = BitVec.ofNat 32 tl67.len) ∨ ((¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4889) 3)) ∧ (¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4892) 3)) ∧ (¬ (memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC488F) 3)) ∧ (¬ (memBytes M (BitVec.ofNat 32 0x3FCC48B8) 10 = memBytes M op ol.toNat)) ∧ (¬ (memBytes M (BitVec.ofNat 32 0x3FCC48C2) 10 = memBytes M op ol.toNat)) ∧ (¬ (memBytes M (BitVec.ofNat 32 0x3FCC48CC) 10 = memBytes M op ol.toNat)) ∧ (¬ (memBytes M (BitVec.ofNat 32 0x3FCC48D6) 10 = memBytes M op ol.toNat)) ∧ (¬ (memBytes M (BitVec.ofNat 32 0x3FCC48E0) 10 = memBytes M op ol.toNat)) ∧ d30 = f30 ∧ d34 = f34 ∧ d20 = a0 ∧ d24 = a1 ∧ d28 = a2 ∧ d2c = a3 ∧ d30' = a4 ∧ d34' = a5 ∧ d38 = a6 ∧ d3c = a7 ∧ d40 = a8 ∧ d44 = a9)))
    (hcont : ∀ st'', extRel M st'' d30 d34 d20 d24 d28 d2c d30' d34' d38 d3c d40 d44 → ∃ st', cont st'' = some st' ∧ Q st')
    (hr : extRel M st f30 f34 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) :
    ∃ st', (if (memBytes M op ol.toNat == oidKeyUsage) = true then
        (keyUsageSigns (memBytes M x3c x38.toNat)).bind fun d => (require d).bind fun _ =>
          (pure ({ keyUsage := true, codeSigning := st.codeSigning, policy := st.policy } : ExtState) : Option ExtState).bind fun st => cont st
      else if (memBytes M op ol.toNat == oidExtKeyUsage) = true then
        (extKeyUsageCodeSigning (memBytes M x3c x38.toNat)).bind fun d => (require d).bind fun _ =>
          (pure ({ keyUsage := st.keyUsage, codeSigning := true, policy := st.policy } : ExtState) : Option ExtState).bind fun st => cont st
      else if (memBytes M op ol.toNat == oidBasicConstraints) = true then
        (basicConstraintsCa (memBytes M x3c x38.toNat)).bind fun d => (require !d).bind fun _ =>
          (pure st : Option ExtState).bind fun st => cont st
      else match List.idxOf? (memBytes M op ol.toNat) policyOids with
        | some i => (policyString (memBytes M x3c x38.toNat)).bind fun s =>
            (pure ({ keyUsage := st.keyUsage, codeSigning := st.codeSigning, policy := st.policy.set i (some s) } : ExtState) : Option ExtState).bind
              fun st => cont st
        | none => (pure st : Option ExtState).bind fun st => cont st) = some st' ∧ Q st' := by
  obtain ⟨r30, r34, rku, rcs, rlen, r0, r1, r2, r3, r4⟩ := hr
  rcases hdisp with
    ⟨hku, tl16, k0, k1, k2, k3, k4, e30, e34, e20, e24, e28, e2c, e30', e34', e38, e3c, e40, e44⟩ |
    ⟨nku, heku, tl19, k0, k1, kk, found, cp, cl, hch, hcl, hfd, e30, e34, e20, e24, e28, e2c, e30', e34', e38, e3c,
      e40, e44⟩ |
    ⟨nku, neku, hbc, tl24, k0, k1, hbr, e30, e34, e20, e24, e28, e2c, e30', e34', e38, e3c, e40, e44⟩ |
    ⟨nku, neku, nbc, hp0, tl, k0, k1, k2, e30, e34, e20, e24, e28, e2c, e30', e34', e38, e3c, e40, e44⟩ |
    ⟨nku, neku, nbc, np0, hp1, tl, k0, k1, k2, e30, e34, e20, e24, e28, e2c, e30', e34', e38, e3c, e40, e44⟩ |
    ⟨nku, neku, nbc, np0, np1, hp2, tl, k0, k1, k2, e30, e34, e20, e24, e28, e2c, e30', e34', e38, e3c, e40, e44⟩ |
    ⟨nku, neku, nbc, np0, np1, np2, hp3, tl, k0, k1, k2, e30, e34, e20, e24, e28, e2c, e30', e34', e38, e3c, e40, e44⟩ |
    ⟨nku, neku, nbc, np0, np1, np2, np3, hp4, tl, k0, k1, k2, e30, e34, e20, e24, e28, e2c, e30', e34', e38, e3c, e40,
      e44⟩ |
    ⟨nku, neku, nbc, np0, np1, np2, np3, np4, e30, e34, e20, e24, e28, e2c, e30', e34', e38, e3c, e40, e44⟩
  · subst e30 e34 e20 e24 e28 e2c e30' e34' e38 e3c e40 e44
    rw [ite_eq_left (beq_iff_eq.mpr (hku.trans K.ku)), keyUsageSigns_code k0 k1 k2 k3 k4]
    simp only [Option.bind_some, require_true, Option.pure_def]
    exact hcont _ ⟨r30, .inr rfl, fun _ => rfl, rcs, rlen, r0, r1, r2, r3, r4⟩
  · subst e30 e34 e20 e24 e28 e2c e30' e34' e38 e3c e40 e44
    rw [ite_eq_right (by rw [ne_of_beq_false nku K.ku]; exact Bool.false_ne_true),
      ite_eq_left (beq_iff_eq.mpr (heku.trans K.eku)),
      extKeyUsageCodeSigning_code K.cs (fun s s' h => h) k0 k1 hch hcl hfd]
    simp only [Option.bind_some, require_true, Option.pure_def]
    exact hcont _ ⟨.inr rfl, r34, rku, fun _ => rfl, rlen, r0, r1, r2, r3, r4⟩
  · subst e30 e34 e20 e24 e28 e2c e30' e34' e38 e3c e40 e44
    have hbc' : basicConstraintsCa (memBytes M x3c x38.toNat) = some false := by
      rcases hbr with h0 | ⟨-, -, -, ip, il, hi, ti, hti, hz⟩
      · have hB := derTlv_mem_bound (derElement_tlv k0)
        have hl : tl24.len < 2 ^ 32 := by have := x38.isLt; omega
        exact basicConstraintsCa_empty k0 k1 (by have := congrArg BitVec.toNat h0; rwa [ofNat_toNat_lt hl] at this)
      · exact basicConstraintsCa_int k0 k1 hi hti hz
    rw [ite_eq_right (by rw [ne_of_beq_false nku K.ku]; exact Bool.false_ne_true),
      ite_eq_right (by rw [ne_of_beq_false neku K.eku]; exact Bool.false_ne_true),
      ite_eq_left (beq_iff_eq.mpr (hbc.trans K.bc)), hbc']
    simp only [Option.bind_some, Bool.not_false, require_true, Option.pure_def]
    exact hcont _ ⟨r30, r34, rku, rcs, rlen, r0, r1, r2, r3, r4⟩
  · subst e30 e34 e20 e24 e28 e2c e30' e34' e38 e3c e40 e44
    have hoid : memBytes M op ol.toNat = oidFulcio 8 := hp0.symm.trans K.p0
    rw [hoid, show (oidFulcio 8 == oidKeyUsage) = false by decide, show (oidFulcio 8 == oidExtKeyUsage) = false by decide,
      show (oidFulcio 8 == oidBasicConstraints) = false by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show List.idxOf? (oidFulcio 8) policyOids = some 0 by decide]
    simp only
    rw [policyString_code k0 k1 k2]
    simp only [Option.bind_some, Option.pure_def]
    have P := extRel_policy (st := st) (i := 0) (s := memBytes M (x3c + BitVec.ofNat 32 tl.header)
      (BitVec.ofNat 32 tl.len).toNat) (by decide) rlen
    exact hcont _ ⟨r30, r34, rku, rcs, P.2.1, fun _ => by rw [P.1], fun h => by rw [P.2.2 1 (by decide)]; exact r1 h, fun h => by rw [P.2.2 2 (by decide)]; exact r2 h, fun h => by rw [P.2.2 3 (by decide)]; exact r3 h, fun h => by rw [P.2.2 4 (by decide)]; exact r4 h⟩
  · subst e30 e34 e20 e24 e28 e2c e30' e34' e38 e3c e40 e44
    have hoid : memBytes M op ol.toNat = oidFulcio 9 := hp1.symm.trans K.p1
    rw [hoid, show (oidFulcio 9 == oidKeyUsage) = false by decide, show (oidFulcio 9 == oidExtKeyUsage) = false by decide,
      show (oidFulcio 9 == oidBasicConstraints) = false by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show List.idxOf? (oidFulcio 9) policyOids = some 1 by decide]
    simp only
    rw [policyString_code k0 k1 k2]
    simp only [Option.bind_some, Option.pure_def]
    have P := extRel_policy (st := st) (i := 1) (s := memBytes M (x3c + BitVec.ofNat 32 tl.header)
      (BitVec.ofNat 32 tl.len).toNat) (by decide) rlen
    exact hcont _ ⟨r30, r34, rku, rcs, P.2.1, fun h => by rw [P.2.2 0 (by decide)]; exact r0 h, fun _ => by rw [P.1], fun h => by rw [P.2.2 2 (by decide)]; exact r2 h, fun h => by rw [P.2.2 3 (by decide)]; exact r3 h, fun h => by rw [P.2.2 4 (by decide)]; exact r4 h⟩
  · subst e30 e34 e20 e24 e28 e2c e30' e34' e38 e3c e40 e44
    have hoid : memBytes M op ol.toNat = oidFulcio 15 := hp2.symm.trans K.p2
    rw [hoid, show (oidFulcio 15 == oidKeyUsage) = false by decide, show (oidFulcio 15 == oidExtKeyUsage) = false by decide,
      show (oidFulcio 15 == oidBasicConstraints) = false by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show List.idxOf? (oidFulcio 15) policyOids = some 2 by decide]
    simp only
    rw [policyString_code k0 k1 k2]
    simp only [Option.bind_some, Option.pure_def]
    have P := extRel_policy (st := st) (i := 2) (s := memBytes M (x3c + BitVec.ofNat 32 tl.header)
      (BitVec.ofNat 32 tl.len).toNat) (by decide) rlen
    exact hcont _ ⟨r30, r34, rku, rcs, P.2.1, fun h => by rw [P.2.2 0 (by decide)]; exact r0 h, fun h => by rw [P.2.2 1 (by decide)]; exact r1 h, fun _ => by rw [P.1], fun h => by rw [P.2.2 3 (by decide)]; exact r3 h, fun h => by rw [P.2.2 4 (by decide)]; exact r4 h⟩
  · subst e30 e34 e20 e24 e28 e2c e30' e34' e38 e3c e40 e44
    have hoid : memBytes M op ol.toNat = oidFulcio 17 := hp3.symm.trans K.p3
    rw [hoid, show (oidFulcio 17 == oidKeyUsage) = false by decide, show (oidFulcio 17 == oidExtKeyUsage) = false by decide,
      show (oidFulcio 17 == oidBasicConstraints) = false by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show List.idxOf? (oidFulcio 17) policyOids = some 3 by decide]
    simp only
    rw [policyString_code k0 k1 k2]
    simp only [Option.bind_some, Option.pure_def]
    have P := extRel_policy (st := st) (i := 3) (s := memBytes M (x3c + BitVec.ofNat 32 tl.header)
      (BitVec.ofNat 32 tl.len).toNat) (by decide) rlen
    exact hcont _ ⟨r30, r34, rku, rcs, P.2.1, fun h => by rw [P.2.2 0 (by decide)]; exact r0 h, fun h => by rw [P.2.2 1 (by decide)]; exact r1 h, fun h => by rw [P.2.2 2 (by decide)]; exact r2 h, fun _ => by rw [P.1], fun h => by rw [P.2.2 4 (by decide)]; exact r4 h⟩
  · subst e30 e34 e20 e24 e28 e2c e30' e34' e38 e3c e40 e44
    have hoid : memBytes M op ol.toNat = oidFulcio 20 := hp4.symm.trans K.p4
    rw [hoid, show (oidFulcio 20 == oidKeyUsage) = false by decide, show (oidFulcio 20 == oidExtKeyUsage) = false by decide,
      show (oidFulcio 20 == oidBasicConstraints) = false by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show List.idxOf? (oidFulcio 20) policyOids = some 4 by decide]
    simp only
    rw [policyString_code k0 k1 k2]
    simp only [Option.bind_some, Option.pure_def]
    have P := extRel_policy (st := st) (i := 4) (s := memBytes M (x3c + BitVec.ofNat 32 tl.header)
      (BitVec.ofNat 32 tl.len).toNat) (by decide) rlen
    exact hcont _ ⟨r30, r34, rku, rcs, P.2.1, fun h => by rw [P.2.2 0 (by decide)]; exact r0 h, fun h => by rw [P.2.2 1 (by decide)]; exact r1 h, fun h => by rw [P.2.2 2 (by decide)]; exact r2 h, fun h => by rw [P.2.2 3 (by decide)]; exact r3 h, fun _ => by rw [P.1]⟩
  · subst e30 e34 e20 e24 e28 e2c e30' e34' e38 e3c e40 e44
    rw [ite_eq_right (by rw [ne_of_beq_false nku K.ku]; exact Bool.false_ne_true),
      ite_eq_right (by rw [ne_of_beq_false neku K.eku]; exact Bool.false_ne_true),
      ite_eq_right (by rw [ne_of_beq_false nbc K.bc]; exact Bool.false_ne_true),
      idxOf_none (fun e => np0 (K.p0.trans e.symm)) (fun e => np1 (K.p1.trans e.symm)) (fun e => np2 (K.p2.trans e.symm))
        (fun e => np3 (K.p3.trans e.symm)) (fun e => np4 (K.p4.trans e.symm))]
    simp only [Option.bind_some, Option.pure_def]
    exact hcont _ ⟨r30, r34, rku, rcs, rlen, r0, r1, r2, r3, r4⟩

set_option maxHeartbeats 8000000 in
theorem extList_chain {M : Word → BitVec 8}
    {B out bp x9 x21 x25 x26 p0 L w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 : Word} {v : Nat → Word}
    (K : ExtConsts M) :
    ∀ k {f30 f34 rem cur a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 f30' f34' cur' b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Word}
      {fuel : Nat} {st : ExtState},
      svChain (sv_extStep B out bp x9 x21 x25 x26 p0 L w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 v M) k
        (f30, f34, rem, cur, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9)
        (f30', f34', 0, cur', b0, b1, b2, b3, b4, b5, b6, b7, b8, b9) →
      rem.toNat ≤ fuel → rem.toNat ≤ L.toNat → cur = p0 + (L - rem) →
      extRel M st f30 f34 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 →
      ∃ st', readExtensionList (memBytes M p0 (L - rem).toNat) fuel (memBytes M cur rem.toNat) st = some st' ∧
        extRel M st' f30' f34' b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 := by
  intro k
  induction k with
  | zero =>
    intro f30 f34 rem cur a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 f30' f34' cur' b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 fuel st h _ _ _ hr
    cases h
    exact ⟨st, extList_nil, hr⟩
  | succ k ih =>
    intro f30 f34 rem cur a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 f30' f34' cur' b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 fuel st h hf hle hp hr
    obtain ⟨m, hm, hc⟩ := h
    obtain ⟨hne, -, tl8, h8, op19, ol19, hc19, to19, ho19, x38, x3c, hx2, -, d30, d34, d20, d24, d28, d2c, d30', d34',
      d38, d3c, d40, d44, hdisp, -, -, -, -, -, hs⟩ := hm
    subst hs
    simp only at hne h8 hc19 ho19 hx2 hdisp hc
    have hB8 := derTlv_mem_bound (derElement_tlv h8)
    have h28 := derTlv_header (derElement_tlv h8)
    have hrem : rem.toNat ≠ 0 := fun e => hne (BitVec.eq_of_toNat_eq e)
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    rw [ho19] at hc19
    obtain ⟨e19a, e19b⟩ := derContent_ok rfl hc19
    have hrest : (rem - BitVec.ofNat 32 (tl8.header + tl8.len)).toNat ≤ fuel' := by rw [subK_toNat hB8]; omega
    have hle' : (rem - BitVec.ofNat 32 (tl8.header + tl8.len)).toNat ≤ L.toNat := by rw [subK_toNat hB8]; omega
    have hp' := ptr_step (BitVec.ofNat 32 (tl8.header + tl8.len)) hp
    have hearl := memBytes_earlier (M := M) (p0 := p0) hle hB8
    rw [← hp] at hearl
    have hLr : (L - rem).toNat = L.toNat - rem.toNat := by rw [BitVec.toNat_sub]; have := rem.isLt; omega
    obtain ⟨a, l, hl⟩ := memBytes_cons (M := M) (p := cur) hrem
    rw [hl, readExtensionList.eq_3, ← hl, readElem_mem h8]
    simp only [Option.bind_eq_bind, Option.bind_some, elemAt]
    rw [readOid_mem ho19]
    simp only [Option.bind_some, restAt]
    rw [hearl]
    have hcont : ∀ st'', extRel M st'' d30 d34 d20 d24 d28 d2c d30' d34' d38 d3c d40 d44 →
        ∃ st', readExtensionList (memBytes M p0 (L - (rem - BitVec.ofNat 32 (tl8.header + tl8.len))).toNat) fuel'
          (memBytes M (cur + BitVec.ofNat 32 (tl8.header + tl8.len)) (rem - BitVec.ofNat 32 (tl8.header + tl8.len)).toNat)
          st'' = some st' ∧ extRel M st' f30' f34' b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 :=
      fun st'' hr'' => ih hc hrest hle' hp' hr''
    rcases hx2 with hF | ⟨hnz, h1, hbool, tb7, hb7, vp14, vl14, hc14, te14, h14, hz14, hlo, hcrit, ex38, ex3c⟩ |
      ⟨hnz, hn1, vp8, vl8, hc8, te8, h8', hz8, hlo, ex38, ex3c⟩
    · exact hF.elim
    · have hl0 : (BitVec.ofNat 32 tl8.len - BitVec.ofNat 32 (to19.header + to19.len)).toNat ≠ 0 :=
        fun e => hnz (BitVec.eq_of_toNat_eq e)
      obtain ⟨n', hn'⟩ : ∃ n', (BitVec.ofNat 32 tl8.len - BitVec.ofNat 32 (to19.header + to19.len)).toNat = n' + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_ne_zero hl0).symm⟩
      have hh : (memBytes M (cur + BitVec.ofNat 32 tl8.header + BitVec.ofNat 32 (to19.header + to19.len))
          (BitVec.ofNat 32 tl8.len - BitVec.ofNat 32 (to19.header + to19.len)).toNat).head? = some 1 := by
        rw [hn', memBytes_succ, h1]; rfl
      rw [hh]
      simp only [show (some 1 == some 1) = true by decide, ↓reduceIte]
      rw [readBooleanTrue_mem hb7 hbool]
      simp only [Option.bind_some, restAt]
      rw [readOctetString_mem h14, restAt_nil hz14]
      simp only [Option.bind_some, require_isEmpty_nil]
      rw [memBytes_length, hLr, ← e19a, ← e19b, listsOid_mem hlo]
      simp only [Option.bind_some]
      have hca : criticalAllowed.contains (memBytes M op19 ol19.toNat) = true := by
        rcases hcrit with h | h | h | h
        · rw [← h, K.ku]; decide
        · rw [← h, K.san]; decide
        · rw [← h, K.bc]; decide
        · rw [← h, K.eku]; decide
      rw [hca]
      simp only [Bool.not_false, Bool.not_true, Bool.and_false, Bool.and_self, require_true, Option.bind_some]
      rw [h14] at hc14
      obtain ⟨e14a, e14b⟩ := derContent_ok rfl hc14
      rw [← e14a, ← e14b, ← ex3c, ← ex38]
      exact ext_dispatch K hdisp hcont hr
    · have hl0 : (BitVec.ofNat 32 tl8.len - BitVec.ofNat 32 (to19.header + to19.len)).toNat ≠ 0 :=
        fun e => hnz (BitVec.eq_of_toNat_eq e)
      obtain ⟨n', hn'⟩ : ∃ n', (BitVec.ofNat 32 tl8.len - BitVec.ofNat 32 (to19.header + to19.len)).toNat = n' + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_ne_zero hl0).symm⟩
      have hh : (List.head? (memBytes M (cur + BitVec.ofNat 32 tl8.header + BitVec.ofNat 32 (to19.header + to19.len))
          (BitVec.ofNat 32 tl8.len - BitVec.ofNat 32 (to19.header + to19.len)).toNat) == some 1) = false := by
        rw [hn', memBytes_succ, List.head?_cons]
        apply Bool.eq_false_iff.mpr
        intro e
        apply hn1
        have := Option.some.inj (beq_iff_eq.mp e)
        exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)
      rw [hh]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [readOctetString_mem h8', restAt_nil hz8]
      simp only [Option.bind_some, require_isEmpty_nil]
      rw [memBytes_length, hLr, ← e19a, ← e19b, listsOid_mem hlo]
      simp only [Option.bind_some, Bool.not_false, Bool.false_and, Bool.and_self, require_true]
      rw [h8'] at hc8
      obtain ⟨e8a, e8b⟩ := derContent_ok rfl hc8
      rw [← e8a, ← e8b, ← ex3c, ← ex38]
      exact ext_dispatch K hdisp hcont hr

theorem flags_set : ∀ {c f30 f34 : Word}, (c = 0 ∨ c = 1) → (f30 = 0 ∨ f30 = 1) → (f34 = 0 ∨ f34 = 1) →
    c &&& (f30 &&& f34) ≠ 0 → c = 1 ∧ f30 = 1 ∧ f34 = 1 := by
  intro c f30 f34 hc h30 h34 h
  rcases hc with rfl | rfl <;> rcases h30 with rfl | rfl <;> rcases h34 with rfl | rfl <;>
    first | exact ⟨rfl, rfl, rfl⟩ | exact absurd rfl h

theorem ult_zero {x : Word} : ((if BitVec.ult 0 x then (1 : Word) else 0) = 0 ∨ (if BitVec.ult 0 x then (1 : Word) else 0) = 1) := by
  by_cases h : BitVec.ult 0 x = true
  · rw [ite_eq_left h]; exact .inr rfl
  · rw [ite_eq_right h]; exact .inl rfl

theorem ult_zero_ne {x : Word} (h : (if BitVec.ult 0 x then (1 : Word) else 0) = 1) : x ≠ 0 := by
  intro e
  subst e
  exact absurd h (by decide)

theorem five_slots {l : List (Option Bytes)} {a b c d e : Bytes} (hl : l.length = 5) (h0 : l[0]? = some (some a))
    (h1 : l[1]? = some (some b)) (h2 : l[2]? = some (some c)) (h3 : l[3]? = some (some d)) (h4 : l[4]? = some (some e)) :
    l.mapM id = some [a, b, c, d, e] := by
  match l, hl with
  | [x0, x1, x2, x3, x4], _ =>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1 h2 h3 h4
    subst h0 h1 h2 h3 h4
    rfl

set_option maxHeartbeats 4000000 in
/-- The leaf's extensions the code read, as `readExtensions`: the five
identity-policy strings are the bytes of the five slots the loop ends with. -/
theorem readExtensions_code {M : Word → BitVec 8}
    {B out bp x9 x21 x25 x26 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 : Word} {v : Nat → Word}
    {pE lE a1 a3 a5 a7 a9 f30' f34' cur' b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Word} {tl25 : DerTlv} {k : Nat}
    (K : ExtConsts M)
    (h37 : derElement 0x30 (memBytes M pE lE.toNat) = .ok tl25)
    (h38 : lE - BitVec.ofNat 32 (tl25.header + tl25.len) = 0)
    (hch : svChain (sv_extStep B out bp x9 x21 x25 x26 (pE + BitVec.ofNat 32 tl25.header) (BitVec.ofNat 32 tl25.len)
      w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 v M) k
      (BitVec.ofNat 32 0x0, BitVec.ofNat 32 0x0, BitVec.ofNat 32 tl25.len, pE + BitVec.ofNat 32 tl25.header,
        BitVec.ofNat 32 0x0, a1, BitVec.ofNat 32 0x0, a3, BitVec.ofNat 32 0x0, a5, BitVec.ofNat 32 0x0, a7,
        BitVec.ofNat 32 0x0, a9)
      (f30', f34', 0, cur', b0, b1, b2, b3, b4, b5, b6, b7, b8, b9))
    (h0 : b0 ≠ 0) (h2 : b2 ≠ 0) (h4 : b4 ≠ 0) (h6 : b6 ≠ 0)
    (hfl : (if BitVec.ult 0 b8 then (1 : Word) else 0) &&& (f30' &&& f34') ≠ 0) :
    readExtensions (memBytes M pE lE.toNat) =
      some [memBytes M b0 b1.toNat, memBytes M b2 b3.toNat, memBytes M b4 b5.toNat, memBytes M b6 b7.toNat,
        memBytes M b8 b9.toNat] := by
  have hB := derTlv_mem_bound (derElement_tlv h37)
  have hl : tl25.len < 2 ^ 32 := by have := lE.isLt; omega
  have hr0 : extRel M {} (BitVec.ofNat 32 0x0) (BitVec.ofNat 32 0x0) (BitVec.ofNat 32 0x0) a1 (BitVec.ofNat 32 0x0) a3
      (BitVec.ofNat 32 0x0) a5 (BitVec.ofNat 32 0x0) a7 (BitVec.ofNat 32 0x0) a9 :=
    ⟨.inl rfl, .inl rfl, fun e => absurd e (by decide), fun e => absurd e (by decide), rfl,
      fun e => absurd rfl e, fun e => absurd rfl e, fun e => absurd rfl e, fun e => absurd rfl e, fun e => absurd rfl e⟩
  obtain ⟨st', hgo, r30, r34, rku, rcs, rlen, r0, r1, r2, r3, r4⟩ :=
    extList_chain K k hch (fuel := (BitVec.ofNat 32 tl25.len).toNat) (Nat.le_refl _) (Nat.le_refl _)
      (by rw [BitVec.sub_self, BitVec.add_zero]) hr0
  rw [BitVec.sub_self, show (0#32 : Word).toNat = 0 from rfl, memBytes_zero] at hgo
  obtain ⟨c1, f1, f2⟩ := flags_set ult_zero r30 r34 hfl
  unfold readExtensions
  rw [readElem_mem h37, restAt_nil h38]
  simp only [Option.bind_eq_bind, Option.bind_some, require_isEmpty_nil, elemAt]
  rw [memBytes_length, hgo]
  simp only [Option.bind_some]
  rw [rku f2, rcs f1, show (true && true) = true from rfl, require_true]
  simp only [Option.bind_some]
  exact five_slots rlen (r0 h0) (r1 h2) (r2 h4) (r3 h6) (r4 (ult_zero_ne c1))

end C3.RV32.Sv
