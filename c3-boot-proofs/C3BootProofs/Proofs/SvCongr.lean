import C3BootProofs.Proofs.SvDer4

/-!
# `sigstore::verify`: reads of bytes no step writes

The stages state each check over the memory at the start of the stage.
A callee reads the bytes of the bundle and of the trust root through the
memory at the call, which agrees with the start on everything outside the
stack. These lemmas move a read from one memory to the other.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

theorem sv_pt {B rp : Word} {rl : Nat} {M M0 : Word → BitVec 8} (fR : ∀ x, SvR B x → M x = M0 x)
    (h : SvIn B rp rl) : ∀ i, i < rl → M (rp + BitVec.ofNat 32 i) = M0 (rp + BitVec.ofNat 32 i) :=
  fun i hi => fR _ (h.sep.sub (c := i) (l := 1) (by omega)).symm

/-- Bytes outside the stack read the same in two memories that agree there. -/
theorem sv_mb {B rp : Word} {rl : Nat} {M M0 : Word → BitVec 8} (fR : ∀ x, SvR B x → M x = M0 x)
    (h : SvIn B rp rl) : memBytes M rp rl = memBytes M0 rp rl :=
  memBytes_congr (sv_pt fR h)

theorem mb_sub {M M' : Word → BitVec 8} {p : Word} {n : Nat}
    (h : ∀ i, i < n → M (p + BitVec.ofNat 32 i) = M' (p + BitVec.ofNat 32 i)) {c l : Nat} (hl : c + l ≤ n) :
    memBytes M (p + BitVec.ofNat 32 c) l = memBytes M' (p + BitVec.ofNat 32 c) l :=
  memBytes_congr fun i hi => by rw [add_ofNat_assoc]; exact h _ (by omega)

/-- `derAlgOf` reads only the `n` bytes at `p`. -/
theorem derAlgOf_congr {M M0 : Word → BitVec 8} {p : Word} {n : Nat}
    (h : ∀ i, i < n → M (p + BitVec.ofNat 32 i) = M0 (p + BitVec.ofNat 32 i)) : derAlgOf M p n = derAlgOf M0 p n := by
  unfold derAlgOf
  rw [memBytes_congr h]
  cases ht : derElement 0x30 (memBytes M0 p n) with
  | error e => rfl
  | ok t =>
    have hb := derElement_bound ht; rw [memBytes_length] at hb
    simp only
    rw [mb_sub h (c := t.header) (l := t.len) (by omega)]
    cases ho : derOid (memBytes M0 (p + BitVec.ofNat 32 t.header) t.len) with
    | error e => rfl
    | ok o =>
      have hob := derElement_bound (derOid_ok_elem ho); rw [memBytes_length] at hob
      simp only
      rw [add_ofNat_assoc, add_ofNat_assoc,
        mb_sub h (c := t.header + (o.header + o.len)) (l := t.len - (o.header + o.len)) (by omega)]

/-- `derIntIsOf` reads the integer's bytes, inside the reader's. -/
theorem derIntIsOf_congr {B rp rl : Word} {M M0 : Word → BitVec 8} {v : BitVec 8}
    (fR : ∀ x, SvR B x → M x = M0 x) (h : SvIn B rp rl.toNat) :
    derIntIsOf M (memBytes M0 rp rl.toNat) rp (derElement 2 (memBytes M0 rp rl.toNat)) v =
      derIntIsOf M0 (memBytes M0 rp rl.toNat) rp (derElement 2 (memBytes M0 rp rl.toNat)) v := by
  unfold derIntIsOf
  cases ht : derElement 2 (memBytes M0 rp rl.toNat) with
  | error e => rfl
  | ok t =>
    have hc := h.content ht
    simp only [derIntOf]
    by_cases h1 : t.len = 0
    · rw [ite_eq_left h1]
    · by_cases h2 : 2 ≤ t.len ∧ (((memBytes M0 rp rl.toNat).getD t.header 0 = 0 ∧
          (memBytes M0 rp rl.toNat).getD (t.header + 1) 0 < 0x80) ∨
          ((memBytes M0 rp rl.toNat).getD t.header 0 = 0xFF ∧ 0x80 ≤ (memBytes M0 rp rl.toNat).getD (t.header + 1) 0))
      · rw [ite_eq_right h1, ite_eq_left h2]
      · rw [ite_eq_right h1, ite_eq_right h2]
        dsimp only
        rw [show (BitVec.ofNat 32 t.len).toNat = t.len by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hc.fit; omega), sv_mb fR hc]

theorem bits_ok_elem {L : Bytes} {rp : Word} {r : Except DerError DerTlv} {x : Word × Word}
    (h : derBitsOf L rp r = .ok x) : ∃ t, r = .ok t := by
  cases r with
  | error e => simp [derBitsOf] at h
  | ok t => exact ⟨t, rfl⟩

theorem pos_ok_elem {L : Bytes} {rp : Word} {r : Except DerError DerTlv} {x : Word × Word}
    (h : derPosIntOf L rp r = .ok x) : ∃ t, r = .ok t := by
  cases r with
  | error e => simp [derPosIntOf, derIntOf] at h
  | ok t => exact ⟨t, rfl⟩

theorem opt_ok_elem {tag : Nat} {L : Bytes} {t : DerTlv} (h : derOptRes tag L = some (.ok t)) :
    derElement tag L = .ok t := by
  cases L with
  | nil => simp [derOptRes] at h
  | cons b rest =>
    by_cases hb : b = tag
    · simp only [derOptRes, hb, ite_true] at h
      simp only [derElement, hb, ite_true]
      exact Option.some.inj h
    · simp only [derOptRes, hb, ite_false] at h
      cases h

theorem SvIn.ofNatLen {B rp : Word} {n : Nat} (h : SvIn B rp n) : SvIn B rp (BitVec.ofNat 32 n).toNat := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.fit; omega)]; exact h

/-- The content of a read, with its length as the word the reader keeps. -/
theorem SvIn.contentW {B rp rl : Word} {M : Word → BitVec 8} {tag : Nat} {t : DerTlv} (h : SvIn B rp rl.toNat)
    (ht : derElement tag (memBytes M rp rl.toNat) = .ok t) :
    SvIn B (rp + BitVec.ofNat 32 t.header) (BitVec.ofNat 32 t.len).toNat := (h.content ht).ofNatLen

/-- The bytes after a read, with their length as the word the reader keeps. -/
theorem SvIn.restW {B rp rl : Word} {M : Word → BitVec 8} {tag : Nat} {t : DerTlv} (h : SvIn B rp rl.toNat)
    (ht : derElement tag (memBytes M rp rl.toNat) = .ok t) :
    SvIn B (rp + BitVec.ofNat 32 (t.header + t.len)) (rl - BitVec.ofNat 32 (t.header + t.len)).toNat := by
  rw [rest_len ht]; exact h.rest ht

/-- The whole element of a read. -/
theorem SvIn.rawW {B rp rl : Word} {M : Word → BitVec 8} {tag : Nat} {t : DerTlv} (h : SvIn B rp rl.toNat)
    (ht : derElement tag (memBytes M rp rl.toNat) = .ok t) :
    SvIn B rp (BitVec.ofNat 32 (t.header + t.len)).toNat := by
  have hb := derElement_bound ht
  rw [memBytes_length] at hb
  refine SvIn.ofNatLen ⟨?_, h.pos, by have := h.lo; omega⟩
  have := h.sep14.sub (c := 0) (l := t.header + t.len + 14) (by omega)
  rwa [add_ofNat_zero] at this

theorem SvIn.pos_ne {B p : Word} {l : Nat} (h : SvIn B p l) : p ≠ 0 := fun e => by
  have := h.pos; rw [e] at this; exact absurd this (by decide)

/-- The bits of a `BIT STRING` read from bytes outside the stack. -/
theorem SvIn.bitsW {B rp rl p l : Word} {M : Word → BitVec 8} {t : DerTlv} (h : SvIn B rp rl.toNat)
    (ht : derElement 3 (memBytes M rp rl.toNat) = .ok t)
    (hb : derBitsOf (memBytes M rp rl.toNat) rp (.ok t) = .ok (p, l)) : SvIn B p l.toNat := by
  have hc := h.content ht
  simp only [derBitsOf] at hb
  by_cases hk : t.len ≠ 0 ∧ (memBytes M rp rl.toNat).getD t.header 0 = 0
  · rw [ite_eq_left hk] at hb
    cases hb
    have e : rp + BitVec.ofNat 32 (t.header + 1) = rp + BitVec.ofNat 32 t.header + BitVec.ofNat 32 1 := by
      rw [add_ofNat_assoc]
    rw [e]
    refine SvIn.ofNatLen ⟨?_, ?_, ?_⟩
    · have := hc.sep14.sub (c := 1) (l := t.len - 1 + 14) (by omega); exact this
    · have hp := hc.pos; have hf := hc.lo
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · have hf := hc.lo; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · rw [ite_eq_right hk] at hb; cases hb

theorem ii_ok_elem {M : Word → BitVec 8} {L : Bytes} {rp : Word} {r : Except DerError DerTlv} {v : BitVec 8} {x : Bool}
    (h : derIntIsOf M L rp r v = .ok x) : ∃ t, r = .ok t := by
  cases r with
  | error e => simp [derIntIsOf, derIntOf] at h
  | ok t => exact ⟨t, rfl⟩

end C3.RV32.Sv
