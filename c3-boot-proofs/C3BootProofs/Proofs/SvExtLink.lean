import C3BootProofs.Proofs.SvLeafLink
import C3BootProofs.Proofs.SvKu
import C3BootProofs.Proofs.SvSeg
import C3BootProofs.Spec.X509

/-!
# The leaf's extension values the code read, as `Spec/X509.lean` reads them

`keyUsageSigns`, `basicConstraintsCa`, and `policyString`, each from what
the success condition of `sigstore::verify` says the code read from an
extension's value, the `vl` bytes at `vp`.
-/

namespace C3.RV32.Sv

open C3.Image

set_option maxRecDepth 100000 in
theorem trailingZeros8_kuUnused : ∀ b : BitVec 8, trailingZeros8 b.toNat = kuUnused b := by decide

theorem kuUnused_le : ∀ b : BitVec 8, kuUnused b ≤ 8 := by decide

theorem byte_zeroExtend_toNat (b : BitVec 8) : (b.zeroExtend 32).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (by decide))

theorem memBytes_getLast? (M : Word → BitVec 8) (q : Word) (k : Nat) :
    (memBytes M q (k + 1)).getLast? = some (M (q + BitVec.ofNat 32 k)).toNat := by
  rw [memBytes_split M q k 1]
  show (memBytes M q k ++ [(M (q + BitVec.ofNat 32 k + BitVec.ofNat 32 0)).toNat]).getLast? = _
  rw [List.getLast?_concat, add_ofNat_zero]

/-- A `KeyUsage` value with `digitalSignature` set, as the code checks it. -/
theorem keyUsageSigns_code {M : Word → BitVec 8} {vp vl : Word} {tl : DerTlv}
    (h0 : derElement 0x3 (memBytes M vp vl.toNat) = .ok tl)
    (h1 : 2 ≤ (BitVec.ofNat 32 tl.len).toNat)
    (h2 : BitVec.ofNat 32 (kuUnused (M (vp + BitVec.ofNat 32 tl.header + BitVec.ofNat 32 tl.len + BitVec.ofNat 32 0xFFFFFFFF))) =
      (M (vp + BitVec.ofNat 32 tl.header)).zeroExtend 32)
    (h3 : vl - BitVec.ofNat 32 (tl.header + tl.len) = 0)
    (h4 : ¬ (M (vp + BitVec.ofNat 32 tl.header + 0x1)).toNat < 0x80) :
    keyUsageSigns (memBytes M vp vl.toNat) = some true := by
  have hB := derTlv_mem_bound (derElement_tlv h0)
  have hl : tl.len < 2 ^ 32 := by have := vl.isLt; omega
  rw [ofNat_toNat_lt hl] at h1
  obtain ⟨k, hk⟩ : ∃ k, tl.len = k + 2 := ⟨tl.len - 2, by omega⟩
  have hlast : vp + BitVec.ofNat 32 tl.header + BitVec.ofNat 32 tl.len + BitVec.ofNat 32 0xFFFFFFFF =
      vp + BitVec.ofNat 32 tl.header + 1 + BitVec.ofNat 32 k := by
    rw [hk]; bv_omega
  have hu : kuUnused (M (vp + BitVec.ofNat 32 tl.header + 1 + BitVec.ofNat 32 k)) =
      (M (vp + BitVec.ofNat 32 tl.header)).toNat := by
    rw [hlast] at h2
    have := congrArg BitVec.toNat h2
    rw [ofNat_toNat_lt (Nat.lt_of_le_of_lt (kuUnused_le _) (by decide)), byte_zeroExtend_toNat] at this
    exact this
  unfold keyUsageSigns readNamedBits
  rw [readElem_mem h0, restAt_nil h3]
  simp only [Option.bind_eq_bind, Option.bind_some, elemAt]
  rw [ofNat_toNat_lt hl, hk, memBytes_succ]
  simp only
  rw [memBytes_getLast?]
  simp only
  rw [trailingZeros8_kuUnused, hu, beq_iff_eq.mpr rfl]
  simp only [↓reduceIte, Option.bind_some, require_isEmpty_nil]
  rw [memBytes_succ]
  show some (decide ((M (vp + BitVec.ofNat 32 tl.header + 1)).toNat ≥ 0x80)) = _
  rw [decide_eq_true (Nat.not_lt.mp h4)]

theorem tag_of_byte' {n m : Nat} (hl : n < 256) (hm : m < 256) (h : BitVec.ofNat 8 n = BitVec.ofNat 8 m) : n = m := by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hm] at this
  exact this

/-- An identity-policy value, one `UTF8String`, as the code checks it. -/
theorem policyString_code {M : Word → BitVec 8} {vp vl : Word} {tl : DerTlv}
    (h0 : derTlv (memBytes M vp vl.toNat) = .ok tl)
    (h1 : BitVec.ofNat 8 tl.tag = BitVec.ofNat 8 0xC)
    (h2 : vl - BitVec.ofNat 32 (tl.header + tl.len) = 0) :
    policyString (memBytes M vp vl.toNat) =
      some (memBytes M (vp + BitVec.ofNat 32 tl.header) (BitVec.ofNat 32 tl.len).toNat) := by
  have ht : tl.tag = 0xC := tag_of_byte' (derTlv_mem_tag h0) (by decide) h1
  unfold policyString
  rw [readTlv_mem h0, restAt_nil h2]
  simp only [Option.bind_eq_bind, Option.bind_some, elemAt]
  rw [ht, show ((0xC == 0x0c) && ([] : Bytes).isEmpty) = true by decide, require_true]
  rfl

/-- An empty `BasicConstraints` sequence: not a CA. -/
theorem basicConstraintsCa_empty {M : Word → BitVec 8} {vp vl : Word} {tl : DerTlv}
    (h0 : derElement 0x30 (memBytes M vp vl.toNat) = .ok tl)
    (h1 : vl - BitVec.ofNat 32 (tl.header + tl.len) = 0)
    (h2 : tl.len = 0) :
    basicConstraintsCa (memBytes M vp vl.toNat) = some false := by
  unfold basicConstraintsCa
  rw [readElem_mem h0, restAt_nil h1]
  simp only [Option.bind_eq_bind, Option.bind_some, require_isEmpty_nil, elemAt]
  rw [h2]
  rfl

/-- A `BasicConstraints` sequence that holds only a `pathLenConstraint`: not
a CA. -/
theorem basicConstraintsCa_int {M : Word → BitVec 8} {vp vl ip il : Word} {tl ti : DerTlv}
    (h0 : derElement 0x30 (memBytes M vp vl.toNat) = .ok tl)
    (h1 : vl - BitVec.ofNat 32 (tl.header + tl.len) = 0)
    (h4 : derIntOf (memBytes M (vp + BitVec.ofNat 32 tl.header) (BitVec.ofNat 32 tl.len).toNat) (vp + BitVec.ofNat 32 tl.header)
      (derElement 2 (memBytes M (vp + BitVec.ofNat 32 tl.header) (BitVec.ofNat 32 tl.len).toNat)) = .ok (ip, il))
    (h5 : derElement 2 (memBytes M (vp + BitVec.ofNat 32 tl.header) (BitVec.ofNat 32 tl.len).toNat) = .ok ti)
    (h6 : BitVec.ofNat 32 tl.len - BitVec.ofNat 32 (ti.header + ti.len) = 0) :
    basicConstraintsCa (memBytes M vp vl.toNat) = some false := by
  rw [h5] at h4
  have hhead : (memBytes M (vp + BitVec.ofNat 32 tl.header) (BitVec.ofNat 32 tl.len).toNat).head? = some 2 := by
    have := derElement_tag h5
    exact this
  unfold basicConstraintsCa
  rw [readElem_mem h0, restAt_nil h1]
  simp only [Option.bind_eq_bind, Option.bind_some, require_isEmpty_nil, elemAt]
  rw [hhead, show (some 2 == some 1) = false by decide]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (some 2 == some 2) = true by decide]
  simp only [↓reduceIte]
  obtain ⟨hr, -, -⟩ := readInteger_mem h5 h4
  rw [hr, restAt_nil h6]
  rfl

theorem flag_or (f : Word) (c : Prop) [Decidable c] :
    decide ((f ||| (if c then (1 : Word) else 0)) &&& 1 ≠ 0) = (decide (f &&& 1 ≠ 0) || decide c) := by
  by_cases hc : c
  · rw [ite_eq_left hc, decide_eq_true hc, Bool.or_true]
    apply decide_eq_true
    intro h
    have := congrArg (fun x => x.getLsbD 0) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] at this
    simp at this
  · have h0 : f ||| (0 : Word) = f := BitVec.or_zero
    rw [ite_eq_right hc, decide_eq_false hc, Bool.or_false, h0]

theorem beq_decide (a b : Bytes) : (a == b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; rw [decide_eq_true rfl]; exact beq_iff_eq.mpr rfl
  · rw [decide_eq_false h]; exact Bool.eq_false_iff.mpr (fun e => h (beq_iff_eq.mp e))

theorem ekuGo_cons_eq {L : Bytes} {fuel : Nat} {found : Bool} (hne : L ≠ []) :
    extKeyUsageCodeSigning.go (fuel + 1) L found =
      (do let (oid, r) ← readOid L; extKeyUsageCodeSigning.go fuel r (found || oid == oidCodeSigning)) := by
  cases L with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

theorem ekuGo_nil {fuel : Nat} {found : Bool} : extKeyUsageCodeSigning.go fuel [] found = some found := by
  cases fuel <;> rfl

/-- The `ExtKeyUsage` loop: a run of `k` steps over the OIDs from `cp`, each
an OID, that ends with no bytes left. -/
theorem ekuGo_chain {M : Word → BitVec 8} {R : Word × Word × Word → Word × Word × Word → Prop}
    (hcs : memBytes M (BitVec.ofNat 32 0x3FCC4820) 8 = oidCodeSigning)
    (hR : ∀ s s', R s s' → s.2.2 ≠ 0 ∧ ∃ op ol, derContent s.2.1 (derOid (memBytes M s.2.1 s.2.2.toNat)) = .ok (op, ol) ∧
      ∃ to, derOid (memBytes M s.2.1 s.2.2.toNat) = .ok to ∧
        s' = (s.1 ||| (if memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4820) 8 then 1 else 0),
          s.2.1 + BitVec.ofNat 32 (to.header + to.len), s.2.2 - BitVec.ofNat 32 (to.header + to.len))) :
    ∀ k {f cp cl f' cp' : Word} {fuel : Nat}, svChain R k (f, cp, cl) (f', cp', 0) → cl.toNat ≤ fuel →
      extKeyUsageCodeSigning.go fuel (memBytes M cp cl.toNat) (decide (f &&& 1 ≠ 0)) = some (decide (f' &&& 1 ≠ 0)) := by
  intro k
  induction k with
  | zero =>
    intro f cp cl f' cp' fuel h _
    cases h
    exact ekuGo_nil
  | succ k ih =>
    intro f cp cl f' cp' fuel h hf
    obtain ⟨m, hRm, hc⟩ := h
    obtain ⟨hne, op, ol, hco, to, hto, hm⟩ := hR _ _ hRm
    subst hm
    simp only at hne hco hto hc
    obtain ⟨e1, e2⟩ := derContent_ok rfl (hto ▸ hco)
    have hB := derTlv_mem_bound (derElement_tlv (derOid_ok_elem hto))
    have h2 := derTlv_header (derElement_tlv (derOid_ok_elem hto))
    have hcl : cl.toNat ≠ 0 := fun e => hne (BitVec.eq_of_toNat_eq e)
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    have hL : memBytes M cp cl.toNat ≠ [] := by
      intro e
      have := congrArg List.length e
      rw [memBytes_length] at this
      exact hcl this
    rw [ekuGo_cons_eq hL, readOid_mem hto]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [← e1, ← e2, beq_decide, ← hcs, ← flag_or]
    exact ih hc (by rw [subK_toNat hB]; omega)

/-- An `ExtKeyUsage` value that lists `codeSigning`, as the code checks it. -/
theorem extKeyUsageCodeSigning_code {M : Word → BitVec 8} {R : Word × Word × Word → Word × Word × Word → Prop}
    {vp vl found' cp' cl' : Word} {tl : DerTlv} {k : Nat}
    (hcs : memBytes M (BitVec.ofNat 32 0x3FCC4820) 8 = oidCodeSigning)
    (hR : ∀ s s', R s s' → s.2.2 ≠ 0 ∧ ∃ op ol, derContent s.2.1 (derOid (memBytes M s.2.1 s.2.2.toNat)) = .ok (op, ol) ∧
      ∃ to, derOid (memBytes M s.2.1 s.2.2.toNat) = .ok to ∧
        s' = (s.1 ||| (if memBytes M op ol.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4820) 8 then 1 else 0),
          s.2.1 + BitVec.ofNat 32 (to.header + to.len), s.2.2 - BitVec.ofNat 32 (to.header + to.len)))
    (h0 : derElement 0x30 (memBytes M vp vl.toNat) = .ok tl)
    (h1 : vl - BitVec.ofNat 32 (tl.header + tl.len) = 0)
    (h2 : svChain R k (BitVec.ofNat 32 0x0, vp + BitVec.ofNat 32 tl.header, BitVec.ofNat 32 tl.len) (found', cp', cl'))
    (h3 : cl' = 0) (h4 : found' &&& BitVec.ofNat 32 0x1 ≠ 0) :
    extKeyUsageCodeSigning (memBytes M vp vl.toNat) = some true := by
  subst h3
  have hB := derTlv_mem_bound (derElement_tlv h0)
  have hl : tl.len < 2 ^ 32 := by have := vl.isLt; omega
  unfold extKeyUsageCodeSigning
  rw [readElem_mem h0, restAt_nil h1]
  simp only [Option.bind_eq_bind, Option.bind_some, require_isEmpty_nil, elemAt]
  have := ekuGo_chain hcs hR k h2 (fuel := (memBytes M (vp + BitVec.ofNat 32 tl.header) (BitVec.ofNat 32 tl.len).toNat).length)
    (Nat.le_of_eq (memBytes_length _ _ _).symm)
  rw [show decide (BitVec.ofNat 32 0x0 &&& 1 ≠ 0) = false by decide, decide_eq_true (show found' &&& 1 ≠ 0 from h4)] at this
  exact this

end C3.RV32.Sv
