import C3BootProofs.Proofs.TrustedRootReadChainCalls

/-!
# `read_chain`'s calls of the DER readers

`parse_cert` reads a certificate's bytes `L`, which sit at `b` in the
scratch buffer, through DER readers in `read_chain`'s frame. `RcL` holds
the bytes, and `RcRdAt` a reader at `d` whose unread bytes are those of
the model's reader `r` over `L`. Each call's theorem states the callee's
result with the model's functions, such as `rcElem`.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

/-- The certificate bytes `L` at `b`, apart from the stack region. -/
structure RcL (M : Word → BitVec 8) (G b : Word) (L : Bytes) : Prop where
  bytes : memBytes M b L.length = L
  sep : Sep b L.length G 0x740
  pos : 0 < b.toNat
  hw : b.toNat + L.length ≤ 0x40000000

/-- The DER reader at `d` reads the bytes of the reader `r` over the bytes
`L` at `b`. -/
def RcRdAt (M : Word → BitVec 8) (d b : Word) (L : Bytes) (r : RcRd) : Prop :=
  memLoad32 M (d + 8) = b + BitVec.ofNat 32 r.1 ∧ memLoad32 M (d + 0xC) = BitVec.ofNat 32 r.2 ∧
    r.1 + r.2 ≤ L.length

theorem RcL.keep {M M' : Word → BitVec 8} {G b : Word} {L : Bytes} (h : RcL M G b L) (hK : RcKeep G M M') :
    RcL M' G b L :=
  ⟨(memBytes_congr fun j hj =>
      hK _ (rc_g0' ((h.sep.shift hj).symm.sub (c := 0) (l := 0x5C0) (by omega)))
        ((h.sep.shift hj).symm.sub (c := 0x620) (l := 0xEC) (by omega))).trans h.bytes,
    h.sep, h.pos, h.hw⟩

theorem RcL.w {M : Word → BitVec 8} {G b : Word} {L : Bytes} (h : RcL M G b L) {i : Nat} (hi : i ≤ L.length) :
    (b + BitVec.ofNat 32 i).toNat = b.toNat + i := by
  have := h.hw; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem RcL.view {M : Word → BitVec 8} {G b : Word} {L : Bytes} (h : RcL M G b L) {r : RcRd}
    (hr : r.1 + r.2 ≤ L.length) : memBytes M (b + BitVec.ofNat 32 r.1) r.2 = rcView L r := by
  rw [← memBytes_drop_take (n := L.length) hr, h.bytes]; rfl

theorem RcRdAt.len {M : Word → BitVec 8} {G d b : Word} {L : Bytes} {r : RcRd} (hL : RcL M G b L)
    (hr : RcRdAt M d b L r) : (memLoad32 M (d + 0xC)).toNat = r.2 := by
  have := hL.hw; have := hr.2.2
  rw [hr.2.1, BitVec.toNat_ofNat]; omega

theorem RcRdAt.view {M : Word → BitVec 8} {G d b : Word} {L : Bytes} {r : RcRd} (hL : RcL M G b L)
    (hr : RcRdAt M d b L r) :
    memBytes M (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat = rcView L r := by
  rw [hr.len hL, hr.1]; exact hL.view hr.2.2

theorem RcRdAt.keep {M M' : Word → BitVec 8} {d b : Word} {L : Bytes} {r : RcRd} (h : RcRdAt M d b L r)
    (h8 : memLoad32 M' (d + 8) = memLoad32 M (d + 8)) (hC : memLoad32 M' (d + 0xC) = memLoad32 M (d + 0xC)) :
    RcRdAt M' d b L r :=
  ⟨h8.trans h.1, hC.trans h.2.1, h.2.2⟩

theorem rcd_b8 (x : BitVec 8) : BitVec.ofNat 8 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

theorem rcd_sub {a c : Nat} (h : c ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 c = BitVec.ofNat 32 (a - c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem rcd_view_len {L : Bytes} {r : RcRd} (h : r.1 + r.2 ≤ L.length) : (rcView L r).length = r.2 := by
  simp only [rcView, List.length_take, List.length_drop]; omega

theorem rcd_c8 (d : Word) : d + 8 + BitVec.ofNat 32 4 = d + 0xC := by rw [BitVec.add_assoc]; rfl

theorem rcd_adv8 {M : Word → BitVec 8} {d rp rl : Word} (t : DerTlv) :
    memLoad32 (derAdvance M d rp rl (.ok t)) (d + 8) = rp + BitVec.ofNat 32 (t.header + t.len) := by
  simp only [derAdvance]
  rw [show d + 0xC = d + BitVec.ofNat 32 0xC from rfl, show d + 8 = d + BitVec.ofNat 32 8 from rfl,
    memLoad32_store32_sep (sep_offsets d (c := 0xC) (n := 4) (d := 8) (k := 4) (.inr (by decide)) (by decide)
      (by decide)), memLoad32_store32_same]

theorem rcd_advC {M : Word → BitVec 8} {d rp rl : Word} (t : DerTlv) :
    memLoad32 (derAdvance M d rp rl (.ok t)) (d + 0xC) = rl - BitVec.ofNat 32 (t.header + t.len) := by
  simp only [derAdvance]; rw [memLoad32_store32_same]

/-- The reader's words after a store at `o` apart from them. -/
theorem rcd_out8 {M M' : Word → BitVec 8} {o d : Word} {k : Nat} (hod : Sep o k (d + 8) 8)
    (h : ∀ x, Sep o k x 1 → M' x = M x) :
    memLoad32 M' (d + 8) = memLoad32 M (d + 8) ∧ memLoad32 M' (d + 0xC) = memLoad32 M (d + 0xC) := by
  have hC : Sep o k (d + 0xC) 4 := by have := hod.subR (c := 4) (l := 4) (by decide); rwa [rcd_c8] at this
  exact ⟨memLoad32_congr fun j hj => h _ (hod.symm.shift (by omega : j < 8)).symm,
    memLoad32_congr fun j hj => h _ (hC.symm.shift hj).symm⟩

/-- `Der::element`'s result at `o`, with the reader at `d` over the bytes
`L` at `b`. -/
def RcTlvOut (M : Word → BitVec 8) (o d b : Word) (L : Bytes) (r : RcRd) : Except (Option Nat) DerTlv → Prop
  | .error e => memLoad32 M o = 0 ∧ ∀ v, e = some v → M (o + 4) = BitVec.ofNat 8 v
  | .ok t => memLoad32 M o = b + BitVec.ofNat 32 (r.1 + t.header) ∧ memLoad32 M (o + 4) = BitVec.ofNat 32 t.len ∧
      memLoad32 M (o + 8) = b + BitVec.ofNat 32 r.1 ∧ memLoad32 M (o + 0xC) = BitVec.ofNat 32 (t.header + t.len) ∧
      RcRdAt M d b L (rcAdv r t) ∧ t.header + t.len ≤ r.2

theorem rcd_rdAdv {M M' : Word → BitVec 8} {G d b rl : Word} {L : Bytes} {r : RcRd} {t : DerTlv} (hL : RcL M G b L)
    (hr : RcRdAt M d b L r) (hb : t.header + t.len ≤ r.2)
    (h8 : memLoad32 M' (d + 8) = b + BitVec.ofNat 32 r.1 + BitVec.ofNat 32 (t.header + t.len))
    (hC : memLoad32 M' (d + 0xC) = rl - BitVec.ofNat 32 (t.header + t.len)) (hrl : rl = memLoad32 M (d + 0xC)) :
    RcRdAt M' d b L (rcAdv r t) := by
  have := hL.hw; have := hr.2.2
  refine ⟨by rw [h8, add_ofNat_assoc]; rfl, ?_, show r.1 + (t.header + t.len) + (r.2 - (t.header + t.len)) ≤ _ by omega⟩
  rw [hC, hrl, hr.2.1, rcd_sub hb (by omega)]; rfl

theorem rcd_tlvOut {M : Word → BitVec 8} {G o d b : Word} {L : Bytes} {r : RcRd} {tag : Nat} (hL : RcL M G b L)
    (hr : RcRdAt M d b L r) (hod : Sep o 17 (d + 8) 8) :
    RcTlvOut (derTlvMem M o d (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC))
      (derElement tag (memBytes M (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat))) o d b L r (rcElem L tag r) := by
  rw [hr.view hL]
  unfold rcElem
  rcases hE : derElement tag (rcView L r) with e | t
  · exact ⟨derTlvMem_err0 e, fun v hv => by cases hv; rw [derTlvMem_err4, rcd_b8]⟩
  · have hb := derElement_bound hE
    rw [rcd_view_len hr.2.2] at hb
    have ho := rcd_out8 hod (fun x hx => derTlvMem_outside (M := M) (d := d) (rp := memLoad32 M (d + 8))
      (rl := memLoad32 M (d + 0xC)) (.ok t) hx)
    refine ⟨by rw [derTlvMem_ok0, hr.1, add_ofNat_assoc], derTlvMem_ok4 t, by rw [derTlvMem_ok8, hr.1],
      derTlvMem_okC t, rcd_rdAdv hL hr hb (by rw [ho.1, rcd_adv8, hr.1]) (by rw [ho.2, rcd_advC]) rfl, hb⟩

theorem rcd_tlv_saved : ∀ q : Fin 32, q.val ∈ trSaved → tlvClob q = false := by decide

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

theorem RcCtx.f8 (_X : RcCtx M0 G F out fr fp fl p n g0) (c : Nat) :
    F + BitVec.ofNat 32 c + 8 = F + BitVec.ofNat 32 (c + 8) :=
  add_ofNat_assoc F c 8

/-- The call of `Der::element` at `off` with the result at `F + oc` and the
reader at `F + dc`. -/
theorem RcCtx.callElem (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {off oc dc tag : Nat} {hi lo b : Word} {L : Bytes} {r : RcRd}
    (h1 : fetchRel trustedRootReadChainCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootReadChainCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TRC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = RDE)
    (hev : (TRC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = TRC + BitVec.ofNat 32 (off + 8))
    (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hoc : 0x60 ≤ oc ∧ oc + 17 ≤ 0x14C ∧ oc % 4 = 0) (hdc : 0x60 ≤ dc ∧ dc + 16 ≤ 0x14C ∧ dc % 4 = 0)
    (hod : oc + 17 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (ha0 : f a0 = F + BitVec.ofNat 32 oc) (ha1 : f a1 = F + BitVec.ofNat 32 dc) (ha2 : f a2 = BitVec.ofNat 32 tag)
    (htag : tag < 256) (hL : RcL M G b L) (hr : RcRdAt M (F + BitVec.ofNat 32 dc) b L r)
    (k : ∀ m2 : Machine, RcKeep G M m2.mem → RcMemInv M0 G F fr fp fl g0 m2.mem →
      RcTlvOut m2.mem (F + BitVec.ofNat 32 oc) (F + BitVec.ofNat 32 dc) b L r (rcElem L tag r) →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f := by
  have gw := X.gw
  refine X.callK (P := fun m2 => RcTlvOut m2.mem (F + BitVec.ofNat 32 oc) (F + BitVec.ofNat 32 dc) b L r (rcElem L tag r))
    h1 h2 htgt hI (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hK hP hI' => k m2 hK hI' hP)
  have C := X.codeAt hI
  rw [← hmem1] at C
  obtain ⟨m2, c2, pc2, hm2, hk2⟩ := derElement_correct m1 (base := RDE) (out := F + BitVec.ofNat 32 oc)
    (d := F + BitVec.ofNat 32 dc) (tag := tag) (retAddr := TRC + BitVec.ofNat 32 (off + 8)) (by decide) C.del
    (by rw [show RDE + 0x26 = TLV from by decide]; exact C.tlv) hpc1 (by rw [hreg1]; trsimp; exact ha0)
    (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp; exact ha2) htag (by rw [hreg1]; trsimp) hev
    (X.fal hoc.2.2) (X.fal hdc.2.2) (by rw [X.fG]; exact X.glo (by omega) (by decide) (by decide))
    (by rw [X.fG]; exact X.glo (by omega) (by decide) (by decide))
    (by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide))
  rw [hmem1] at hm2
  refine ⟨m2, c2, pc2, ⟨fun x _ xb => ?_, ?_⟩, hk2 sp (by decide), fun q hq => hk2 q (rcd_tlv_saved q hq)⟩
  · rw [hm2, derTlvMem_outside _ (by rw [X.fG]; exact rc_gin xb (by omega) (by omega)),
      derAdvance_outside _ (by rw [X.f8, X.fG]; exact rc_gin xb (by omega) (by omega))]
  · rw [hm2]
    exact rcd_tlvOut hL hr (by rw [X.f8, X.fG, X.fG]; exact X.gsep (by omega) (by omega) (by omega))

end

end C3.RV32
