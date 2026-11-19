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

end C3.RV32.Sv
