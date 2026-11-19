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

theorem br_bltu_t {a b : Word} (h : a.toNat < b.toNat) : branchTaken .bltu a b = true := by
  simp only [branchTaken, BitVec.ult, decide_eq_true_eq]; exact h
theorem br_bltu_f {a b : Word} (h : ¬ a.toNat < b.toNat) : branchTaken .bltu a b = false := by
  simp only [branchTaken, BitVec.ult, decide_eq_false_iff_not]; exact h

/-- The whole element of a read, with a natural length. -/
theorem SvIn.rawN {B rp rl : Word} {M : Word → BitVec 8} {tag : Nat} {t : DerTlv} (h : SvIn B rp rl.toNat)
    (ht : derElement tag (memBytes M rp rl.toNat) = .ok t) : SvIn B rp (t.header + t.len) := by
  have hb := derElement_bound ht
  rw [memBytes_length] at hb
  refine ⟨?_, h.pos, by have := h.lo; omega⟩
  have := h.sep14.sub (c := 0) (l := t.header + t.len + 14) (by omega)
  rwa [add_ofNat_zero] at this

/-- The OID that `Der::algorithm` reads from bytes outside the stack. -/
theorem SvIn.algOid {B p op : Word} {n ol : Nat} {M : Word → BitVec 8} {w : Option (Word × DerTlv)} (h : SvIn B p n)
    (hq : derAlgOf M p n = .ok ((op, ol), w)) : SvIn B op ol := by
  unfold derAlgOf at hq
  cases ht : derElement 0x30 (memBytes M p n) with
  | error e => rw [ht] at hq; cases hq
  | ok t =>
    rw [ht] at hq
    simp only at hq
    cases ho : derOid (memBytes M (p + BitVec.ofNat 32 t.header) t.len) with
    | error e => rw [ho] at hq; cases hq
    | ok o =>
      rw [ho] at hq
      simp only at hq
      have hc : SvIn B (p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 o.header) o.len :=
        (h.content ht).content (derOid_ok_elem ho)
      split at hq
      · cases hq; exact hc
      · split at hq
        · cases hq
        · split at hq
          · cases hq; exact hc
          · cases hq

/-- A constant's bytes are outside the stack. -/
theorem dataR {B q : Word} {ql : Nat} (F : Fr B 0x3830) (h1 : 0x3FCC4200 ≤ q.toNat) (h2 : q.toNat + ql ≤ 0x3FCC4E60)
    (i : Nat) (hi : i < ql) : SvR B (q + BitVec.ofNat 32 i) := by
  have hs := F.dsep.subR (c := q.toNat - 0x3FCC4200 + i) (l := 1) (by omega)
  have e : (0x3FCC4200 : Word) + BitVec.ofNat 32 (q.toNat - 0x3FCC4200 + i) = q + BitVec.ofNat 32 i := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := q.isLt
    rw [show (0x3FCC4200 : Word).toNat = 1070350848 from rfl]
    omega
  rw [e] at hs
  exact hs

/-- Constants and bundle bytes read the same in two memories that agree
outside the stack. -/
theorem sv_mbRo {B q : Word} {ql : Nat} {M M0 : Word → BitVec 8} (F : Fr B 0x3830)
    (fR : ∀ x, SvR B x → M x = M0 x) (h : SvRo B q ql) : memBytes M q ql = memBytes M0 q ql := by
  rcases h with h | ⟨h1, h2⟩
  · exact sv_mb fR h
  · exact memBytes_congr fun i hi => fR _ (dataR F h1 h2 i hi)

/-- The parameters `Der::algorithm` finds in bytes outside the stack start
at a nonzero address. -/
theorem SvIn.algParams {B p op prp : Word} {n ol : Nat} {u : DerTlv} {M : Word → BitVec 8} (h : SvIn B p n)
    (hq : derAlgOf M p n = .ok ((op, ol), some (prp, u))) : prp + BitVec.ofNat 32 u.header ≠ 0 := by
  unfold derAlgOf at hq
  cases ht : derElement 0x30 (memBytes M p n) with
  | error e => rw [ht] at hq; cases hq
  | ok t =>
    rw [ht] at hq
    simp only at hq
    cases ho : derOid (memBytes M (p + BitVec.ofNat 32 t.header) t.len) with
    | error e => rw [ho] at hq; cases hq
    | ok o =>
      rw [ho] at hq
      simp only at hq
      have hc := h.content ht
      have hob := derElement_bound (derOid_ok_elem ho); rw [memBytes_length] at hob
      split at hq
      · cases hq
      · split at hq
        · cases hq
        · rename_i u' hu
          split at hq
          · simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hq
            obtain ⟨_, h1, h2⟩ := hq
            rw [← h1, ← h2]
            have hub := derTlv_bound hu; rw [memBytes_length] at hub
            intro e
            have h1 := hc.pos; have h2 := hc.lo
            have : (p + BitVec.ofNat 32 t.header + BitVec.ofNat 32 (o.header + o.len) +
                BitVec.ofNat 32 u'.header).toNat = (p + BitVec.ofNat 32 t.header).toNat + (o.header + o.len) + u'.header := by
              rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
            rw [e, show (0 : Word).toNat = 0 from rfl] at this; omega
          · cases hq

/-- A positive integer read from bytes outside the stack starts at a nonzero address. -/
theorem SvIn.serial_ne {B rp rl ip il : Word} {M : Word → BitVec 8} {t : DerTlv} (h : SvIn B rp rl.toNat)
    (ht : derElement 2 (memBytes M rp rl.toNat) = .ok t)
    (hp : derPosIntOf (memBytes M rp rl.toNat) rp (.ok t) = .ok (ip, il)) : ip ≠ 0 := by
  have hn := h.ok_ne ht
  unfold derPosIntOf at hp
  cases hi : derIntOf (memBytes M rp rl.toNat) rp (.ok t) with
  | error e => rw [hi] at hp; cases hp
  | ok pl =>
    rw [hi] at hp
    simp only at hp
    split at hp
    · cases hp
    · cases hp
      simp only [derIntOf] at hi
      split at hi
      · cases hi
      · split at hi
        · cases hi
        · cases hi; exact hn

/-- The first `k` bytes. -/
theorem SvIn.shrink {B rp : Word} {rl k : Nat} (h : SvIn B rp rl) (hk : k ≤ rl) : SvIn B rp k :=
  ⟨by have := h.sep14.sub (c := 0) (l := k + 14) (by omega); rwa [add_ofNat_zero] at this, h.pos,
    by have := h.lo; omega⟩

/-- The bytes after the first `k`. -/
theorem SvIn.drop {B rp : Word} {rl k : Nat} (h : SvIn B rp rl) (hk : k ≤ rl) :
    SvIn B (rp + BitVec.ofNat 32 k) (rl - k) := by
  have e : (rp + BitVec.ofNat 32 k).toNat = rp.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := h.lo; omega
  refine ⟨h.sep14.sub (c := k) (l := rl - k + 14) (by omega), by rw [e]; have := h.pos; omega,
    by rw [e]; have := h.lo; omega⟩

/-- A length below `2 ^ 32` is zero exactly when its word is. -/
theorem ofNat_eq_zero_iff {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n = 0 ↔ n = 0 := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this; exact this
  · intro e; rw [e]; rfl

theorem rest_ne {M : Word → BitVec 8} {p : Word} {n : Nat} {r : Bytes} (hn : n < 2 ^ 32)
    (h : r = memBytes M p n) (hz : ¬ r = []) : BitVec.ofNat 32 n ≠ 0 := fun e => by
  rw [ofNat_eq_zero_iff hn] at e; subst e; exact hz (by rw [h]; rfl)

theorem rest_eq {M : Word → BitVec 8} {p : Word} {n : Nat} {r : Bytes}
    (h : r = memBytes M p n) (hz : r = []) : BitVec.ofNat 32 n = 0 := by
  have := congrArg List.length h; rw [hz, memBytes_length] at this; rw [← this]; rfl

theorem alg_ok_elem {M : Word → BitVec 8} {p : Word} {n : Nat} {x : (Word × Nat) × Option (Word × DerTlv)}
    (h : derAlgOf M p n = .ok x) : ∃ t, derElement 0x30 (memBytes M p n) = .ok t := by
  unfold derAlgOf at h
  cases ht : derElement 0x30 (memBytes M p n) with
  | error e => rw [ht] at h; cases h
  | ok t => exact ⟨t, rfl⟩

/-- The bytes after a read, from a natural length. -/
theorem SvIn.restN {B rp : Word} {rl : Nat} {M : Word → BitVec 8} {tag : Nat} {t : DerTlv} (h : SvIn B rp rl)
    (ht : derElement tag (memBytes M rp rl) = .ok t) :
    SvIn B (rp + BitVec.ofNat 32 (t.header + t.len)) (BitVec.ofNat 32 rl - BitVec.ofNat 32 (t.header + t.len)).toNat := by
  have h' := h.ofNatLen
  have e : (BitVec.ofNat 32 rl).toNat = rl := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.fit; omega)]
  rw [← e] at ht
  exact h'.restW ht

/-- The parameters' content that `Der::algorithm` finds in bytes outside the stack. -/
theorem SvIn.algParamsIn {B p op prp : Word} {n ol : Nat} {u : DerTlv} {M : Word → BitVec 8} (h : SvIn B p n)
    (hq : derAlgOf M p n = .ok ((op, ol), some (prp, u))) : SvIn B (prp + BitVec.ofNat 32 u.header) u.len := by
  unfold derAlgOf at hq
  cases ht : derElement 0x30 (memBytes M p n) with
  | error e => rw [ht] at hq; cases hq
  | ok t =>
    rw [ht] at hq
    simp only at hq
    cases ho : derOid (memBytes M (p + BitVec.ofNat 32 t.header) t.len) with
    | error e => rw [ho] at hq; cases hq
    | ok o =>
      rw [ho] at hq
      simp only at hq
      have hc := h.content ht
      have hob := derElement_bound (derOid_ok_elem ho); rw [memBytes_length] at hob
      split at hq
      · cases hq
      · split at hq
        · cases hq
        · rename_i u' hu
          split at hq
          · simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hq
            obtain ⟨_, h1, h2⟩ := hq
            rw [← h1, ← h2]
            have hub := derTlv_bound hu; rw [memBytes_length] at hub
            have hr := hc.drop (k := o.header + o.len) (by omega)
            have := hr.drop (k := u'.header) (by omega)
            exact this.shrink (by omega)
          · cases hq

theorem sub_lit_ne {x : Word} {c c' : Nat} (hc : c + c' = 2 ^ 32) (h : x ≠ BitVec.ofNat 32 c) :
    x + BitVec.ofNat 32 c' ≠ 0 := fun e => h (by
  apply BitVec.eq_of_toNat_eq
  have h0 := congrArg BitVec.toNat e
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h0 ⊢
  rw [show (0 : Word).toNat = 0 from rfl] at h0
  have := x.isLt; omega)

theorem sub_lit_eq {x : Word} {c c' : Nat} (hc : c + c' = 2 ^ 32) (h : x = BitVec.ofNat 32 c) :
    x + BitVec.ofNat 32 c' = 0 := by
  subst h; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; rw [show (0 : Word).toNat = 0 from rfl]; omega

theorem br_bne_byte_t {b : BitVec 8} {n : Nat} (_hn : n < 256) (h : b ≠ BitVec.ofNat 8 n) :
    branchTaken .bne (b.zeroExtend 32) (BitVec.ofNat 32 n) = true := by
  simp only [branchTaken, bne_iff_ne, ne_eq]
  intro e; apply h; apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this ⊢
  have := b.isLt; omega

theorem br_bne_byte_f {b : BitVec 8} {n : Nat} (hn : n < 256) (h : b = BitVec.ofNat 8 n) :
    branchTaken .bne (b.zeroExtend 32) (BitVec.ofNat 32 n) = false := by
  subst h
  simp only [branchTaken, bne_eq_false_iff_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

/-- An input's first byte is outside the stack. -/
theorem SvIn.r0 {B p : Word} {n : Nat} (h : SvIn B p n) (hn : 0 < n) : SvR B p := by
  have := (h.sep.sub (c := 0) (l := 1) (by omega)).symm; rwa [add_ofNat_zero] at this

end C3.RV32.Sv
