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

/-- The certificate bytes `L` at `b`, apart from the stack region.
`time::read_time` may read up to 14 bytes past a reader's end, so the 14
bytes after `L` are apart from the stack region too. -/
structure RcL (M : Word → BitVec 8) (G b : Word) (L : Bytes) : Prop where
  bytes : memBytes M b L.length = L
  sep : Sep b (L.length + 14) G 0x740
  pos : 0 < b.toNat
  hw : b.toNat + L.length + 14 ≤ 0x40000000

/-- The DER reader at `d` reads the bytes of the reader `r` over the bytes
`L` at `b`. -/
def RcRdAt (M : Word → BitVec 8) (d b : Word) (L : Bytes) (r : RcRd) : Prop :=
  memLoad32 M (d + 8) = b + BitVec.ofNat 32 r.1 ∧ memLoad32 M (d + 0xC) = BitVec.ofNat 32 r.2 ∧
    r.1 + r.2 ≤ L.length

theorem RcL.keep {M M' : Word → BitVec 8} {G b : Word} {L : Bytes} (h : RcL M G b L) (hK : RcKeep G M M') :
    RcL M' G b L :=
  ⟨(memBytes_congr fun j hj =>
      hK _ (rc_g0' ((h.sep.shift (by omega : j < L.length + 14)).symm.sub (c := 0) (l := 0x5C0) (by omega)))
        ((h.sep.shift (by omega : j < L.length + 14)).symm.sub (c := 0x620) (l := 0xEC) (by omega))).trans h.bytes,
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

/-- A callee changed only the stack below the frame, the `ol` bytes at
`o`, and the `el` bytes at `e`. -/
def RcFr (G : Word) (M M' : Word → BitVec 8) (o : Word) (ol : Nat) (e : Word) (el : Nat) : Prop :=
  ∀ x, Sep G 0x5C0 x 1 → Sep o ol x 1 → Sep e el x 1 → M' x = M x

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

theorem RcCtx.f8 (_X : RcCtx M0 G F out fr fp fl p n g0) (c : Nat) :
    F + BitVec.ofNat 32 c + 8 = F + BitVec.ofNat 32 (c + 8) :=
  add_ofNat_assoc F c 8

theorem RcCtx.keepOf (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {oc ol dc : Nat}
    (hoc : 0x60 ≤ oc ∧ oc + ol ≤ 0x14C) (hdc : 0x60 ≤ dc ∧ dc + 16 ≤ 0x14C)
    (h : RcFr G M M' (F + BitVec.ofNat 32 oc) ol (F + BitVec.ofNat 32 (dc + 8)) 8) : RcKeep G M M' :=
  fun x xa xb => h x xa (by rw [X.fG]; exact rc_gin xb (by omega) (by omega))
    (by rw [X.fG]; exact rc_gin xb (by omega) (by omega))

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
    (k : ∀ m2 : Machine, RcKeep G M m2.mem → RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 17 (F + BitVec.ofNat 32 (dc + 8)) 8 →
      RcMemInv M0 G F fr fp fl g0 m2.mem →
      RcTlvOut m2.mem (F + BitVec.ofNat 32 oc) (F + BitVec.ofNat 32 dc) b L r (rcElem L tag r) →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f := by
  have gw := X.gw
  refine X.callK (P := fun m2 => RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 17 (F + BitVec.ofNat 32 (dc + 8)) 8 ∧
      RcTlvOut m2.mem (F + BitVec.ofNat 32 oc) (F + BitVec.ofNat 32 dc) b L r (rcElem L tag r))
    h1 h2 htgt hI (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hK hP hI' => k m2 hK hP.1 hI' hP.2)
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
  have hF : RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 17 (F + BitVec.ofNat 32 (dc + 8)) 8 := by
    intro x _ xo xd
    rw [hm2, derTlvMem_outside _ xo,
        derAdvance_outside _ (by rw [X.f8]; exact xd)]
  refine ⟨m2, c2, pc2, ⟨X.keepOf ⟨hoc.1, hoc.2.1⟩ ⟨hdc.1, hdc.2.1⟩ hF, hF, ?_⟩, hk2 sp (by decide), fun q hq => hk2 q (rcd_tlv_saved q hq)⟩
  · rw [hm2]
    exact rcd_tlvOut hL hr (by rw [X.f8, X.fG, X.fG]; exact X.gsep (by omega) (by omega) (by omega))

end

/-- Loads from a memory that agrees with `N` outside the range at `S`. -/
theorem rcd_ld {M N : Word → BitVec 8} {S a : Word} {k : Nat} (h : ∀ x, Sep S k x 1 → M x = N x)
    (ha : Sep S k a 4) : memLoad32 M a = memLoad32 N a :=
  memLoad32_congr fun _ hj => h _ (ha.symm.shift hj).symm

theorem rcd_s0 {S o : Word} {k n : Nat} (h : Sep S k o n) (hn : 4 ≤ n) : Sep S k o 4 := by
  have := h.subR (c := 0) (l := 4) hn; rwa [add_ofNat_zero] at this

theorem rcd_o0 (o : Word) {d k : Nat} (hd : 4 ≤ d) (hk : d + k ≤ 2 ^ 32) :
    Sep o 4 (o + BitVec.ofNat 32 d) k := by
  have := sep_offsets o (c := 0) (n := 4) (d := d) (k := k) (.inl hd) (by decide) hk
  rwa [add_ofNat_zero] at this

theorem rcd_nst_err0 {M : Word → BitVec 8} {o rp : Word} (e : DerError) :
    memLoad32 (derNestedMem M o rp (.error e)) o = 0 := by
  simp only [derNestedMem]; exact memLoad32_store32_same _ _ _

theorem rcd_nst_err4 {M : Word → BitVec 8} {o rp : Word} (e : DerError) :
    derNestedMem M o rp (.error e) (o + 4) = derErrByte e := by
  simp only [derNestedMem]
  rw [memStore32_get_sep (x := o + 4) (rcd_o0 o (d := 4) (k := 1) (by decide) (by decide)), memStore8_same]

theorem rcd_nst_ok0 {M : Word → BitVec 8} {o rp : Word} (t : DerTlv) :
    memLoad32 (derNestedMem M o rp (.ok t)) o = rp + BitVec.ofNat 32 t.header := by
  simp only [derNestedMem]; exact memLoad32_store32_same _ _ _

theorem rcd_nst_ok8 {M : Word → BitVec 8} {o rp : Word} (t : DerTlv) :
    memLoad32 (derNestedMem M o rp (.ok t)) (o + 8) = rp + BitVec.ofNat 32 t.header := by
  simp only [derNestedMem]
  rw [show o + 4 = o + BitVec.ofNat 32 4 from rfl, show o + 8 = o + BitVec.ofNat 32 8 from rfl,
    show o + 0xC = o + BitVec.ofNat 32 0xC from rfl,
    memLoad32_store32_sep (rcd_o0 o (d := 8) (k := 4) (by decide) (by decide)),
    memLoad32_store32_sep (sep_offsets o (c := 0xC) (n := 4) (d := 8) (k := 4) (.inr (by decide)) (by decide)
      (by decide)),
    memLoad32_store32_sep (sep_offsets o (c := 4) (n := 4) (d := 8) (k := 4) (.inl (by decide)) (by decide)
      (by decide)), memLoad32_store32_same]

theorem rcd_nst_okC {M : Word → BitVec 8} {o rp : Word} (t : DerTlv) :
    memLoad32 (derNestedMem M o rp (.ok t)) (o + 0xC) = BitVec.ofNat 32 t.len := by
  simp only [derNestedMem]
  rw [show o + 0xC = o + BitVec.ofNat 32 0xC from rfl,
    memLoad32_store32_sep (rcd_o0 o (d := 0xC) (k := 4) (by decide) (by decide)), memLoad32_store32_same]

theorem rcd_nst_out {M : Word → BitVec 8} {o rp x : Word} (res : Except DerError DerTlv) (hx : Sep o 16 x 1) :
    derNestedMem M o rp res x = M x := by
  have h0 : Sep o 4 x 1 := by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  cases res with
  | error e =>
    simp only [derNestedMem]
    rw [memStore32_get_sep h0, memStore8_ne fun e' => hx 4 (by decide) 0 (by decide) (by rw [add_ofNat_zero]; exact e'.symm)]
  | ok t =>
    simp only [derNestedMem]
    rw [memStore32_get_sep h0, memStore32_get_sep (a := o + 0xC) (hx.sub (c := 0xC) (l := 4) (by decide)),
      memStore32_get_sep (a := o + 4) (hx.sub (c := 4) (l := 4) (by decide)),
      memStore32_get_sep (a := o + 8) (hx.sub (c := 8) (l := 4) (by decide))]

/-- `Der::sequence`'s result at `o`, a reader over the sequence's
contents, with the reader at `d` over the bytes `L` at `b`. -/
def RcSeqOut (M : Word → BitVec 8) (o d b : Word) (L : Bytes) (r : RcRd) : Except (Option Nat) DerTlv → Prop
  | .error e => memLoad32 M o = 0 ∧ ∀ v, e = some v → M (o + 4) = BitVec.ofNat 8 v
  | .ok t => memLoad32 M o = b + BitVec.ofNat 32 (r.1 + t.header) ∧ RcRdAt M o b L (rcIn r t) ∧
      RcRdAt M d b L (rcAdv r t) ∧ t.header + t.len ≤ r.2

theorem rcd_seqOut {M M' : Word → BitVec 8} {G S o d b : Word} {L : Bytes} {r : RcRd} (hL : RcL M G b L)
    (hr : RcRdAt M d b L r) (hod : Sep o 16 (d + 8) 8) (hSo : Sep S 0x20 o 16) (hSd : Sep S 0x20 (d + 8) 8)
    (h : ∀ x, Sep S 0x20 x 1 →
      M' x = derNestedMem (derAdvance M d (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC))
        (derElement 0x30 (memBytes M (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat)))
        o (memLoad32 M (d + 8))
        (derElement 0x30 (memBytes M (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat)) x) :
    RcSeqOut M' o d b L r (rcElem L 0x30 r) := by
  rw [hr.view hL] at h
  unfold rcElem
  rcases hE : derElement 0x30 (rcView L r) with e | t
  · rw [hE] at h
    refine ⟨by rw [rcd_ld h (rcd_s0 hSo (by decide)), rcd_nst_err0], fun v hv => ?_⟩
    cases hv
    rw [h (o + 4) (hSo.subR (c := 4) (l := 1) (by decide)), rcd_nst_err4, rcd_b8]
  · rw [hE] at h
    have hb := derElement_bound hE
    rw [rcd_view_len hr.2.2] at hb
    have := hr.2.2
    have hC : Sep S 0x20 (d + 0xC) 4 := by have := hSd.subR (c := 4) (l := 4) (by decide); rwa [rcd_c8] at this
    have ho := rcd_out8 hod (fun x hx => rcd_nst_out (M := derAdvance M d (memLoad32 M (d + 8))
      (memLoad32 M (d + 0xC)) (.ok t)) (o := o) (rp := memLoad32 M (d + 8)) (.ok t) hx)
    refine ⟨by rw [rcd_ld h (rcd_s0 hSo (by decide)), rcd_nst_ok0, hr.1, add_ofNat_assoc],
      ⟨by rw [rcd_ld h (a := o + 8) (hSo.subR (c := 8) (l := 4) (by decide)), rcd_nst_ok8, hr.1, add_ofNat_assoc]; rfl,
        by rw [rcd_ld h (a := o + 0xC) (hSo.subR (c := 0xC) (l := 4) (by decide)), rcd_nst_okC]; rfl,
        show r.1 + t.header + t.len ≤ _ by omega⟩,
      rcd_rdAdv hL hr hb (by rw [rcd_ld h (rcd_s0 hSd (by decide)), ho.1, rcd_adv8, hr.1])
        (by rw [rcd_ld h hC, ho.2, rcd_advC]) rfl, hb⟩

theorem rcd_oid_saved : ∀ q : Fin 32, q.val ∈ trSaved → oidKeep q = true := by decide

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

theorem RcCtx.fC (_X : RcCtx M0 G F out fr fp fl p n g0) (c : Nat) :
    F + BitVec.ofNat 32 c + 0xC = F + BitVec.ofNat 32 (c + 0xC) :=
  add_ofNat_assoc F c 0xC

/-- The call of `Der::sequence` at `off` with the result at `F + oc` and
the reader at `F + dc`. -/
theorem RcCtx.callSeq (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {off oc dc : Nat} {hi lo b : Word} {L : Bytes} {r : RcRd}
    (h1 : fetchRel trustedRootReadChainCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootReadChainCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TRC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = RDS)
    (hev : (TRC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = TRC + BitVec.ofNat 32 (off + 8))
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hoc : 0x60 ≤ oc ∧ oc + 16 ≤ 0x14C ∧ oc % 4 = 0) (hdc : 0x60 ≤ dc ∧ dc + 16 ≤ 0x14C ∧ dc % 4 = 0)
    (hod : oc + 16 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (ha0 : f a0 = F + BitVec.ofNat 32 oc) (ha1 : f a1 = F + BitVec.ofNat 32 dc)
    (hL : RcL M G b L) (hr : RcRdAt M (F + BitVec.ofNat 32 dc) b L r)
    (k : ∀ m2 : Machine, RcKeep G M m2.mem → RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 16 (F + BitVec.ofNat 32 (dc + 8)) 8 →
      RcMemInv M0 G F fr fp fl g0 m2.mem →
      RcSeqOut m2.mem (F + BitVec.ofNat 32 oc) (F + BitVec.ofNat 32 dc) b L r (rcElem L 0x30 r) →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f := by
  have gw := X.gw
  have hw := hL.hw
  have hr2 := hr.2.2
  have eG : F + 0xFFFFFFE0 = G + BitVec.ofNat 32 0x5A0 := X.fneg (k := 0x20) (by decide) (by decide)
  refine X.callK (P := fun m2 => RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 16 (F + BitVec.ofNat 32 (dc + 8)) 8 ∧
      RcSeqOut m2.mem (F + BitVec.ofNat 32 oc) (F + BitVec.ofNat 32 dc) b L r (rcElem L 0x30 r))
    h1 h2 htgt hI (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hK hP hI' => k m2 hK hP.1 hI' hP.2)
  have C := X.codeAt hI
  rw [← hmem1] at C hL
  have hr1 : RcRdAt m1.mem (F + BitVec.ofNat 32 dc) b L r := by rw [hmem1]; exact hr
  have hsp1 : reg m1 sp = F := by rw [hreg1]; trsimp; exact hR.2.1
  obtain ⟨m2, c2, pc2, hsp2, hk2, hm2⟩ := derSequence_correct m1 (Q := RDS) (sp0 := F)
    (out := F + BitVec.ofNat 32 oc) (d := F + BitVec.ofNat 32 dc) (retAddr := TRC + BitVec.ofNat 32 (off + 8))
    (by decide) C.dsq
    ⟨by decide, by rw [show RDS + 0x278 = RDN from by decide]; exact C.nst,
      by rw [show RDS + 0x278 + 0xFFFFFF20 = RDE from by decide]; exact C.del,
      by rw [show RDS + 0x278 + 0xFFFFFF46 = TLV from by decide]; exact C.tlv,
      X.fa4, by rw [X.fn]; omega, X.fal hoc.2.2, X.fal hdc.2.2,
      by rw [eG]; exact X.glo (by decide) (by decide) (by decide),
      by rw [eG]; exact X.glo (by decide) (by decide) (by decide),
      by rw [eG]; exact X.glo (by decide) (by decide) (by decide),
      by rw [X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [eG, X.fG]; exact X.gsep (Or.inr (by omega)) (by omega) (by decide),
      by rw [eG, X.f8, X.fG]; exact X.gsep (Or.inr (by omega)) (by omega) (by decide),
      by rw [hr1.len hL, hr1.1, eG]; exact (hL.sep.sub (c := r.1) (l := r.2) (by omega)).subR (by decide),
      by rw [hr1.1, hL.w (by omega)]; have := hL.pos; omega,
      by rw [hr1.len hL, hr1.1, hL.w (by omega)]; omega⟩
    hpc1 hsp1 (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp) hev
  rw [eG] at hm2
  have hF : RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 16 (F + BitVec.ofNat 32 (dc + 8)) 8 := by
    intro x xa xo xd
    rw [hm2 x (rc_gin (rc_g0 xa) (by decide) (by decide)), rcd_nst_out _ xo,
        derAdvance_outside _ (by rw [X.f8]; exact xd), hmem1]
  refine ⟨m2, c2, pc2, ⟨X.keepOf ⟨hoc.1, hoc.2.1⟩ ⟨hdc.1, hdc.2.1⟩ hF, hF, ?_⟩, by rw [hsp2, hsp1], fun q hq => hk2 q (rcd_oid_saved q hq)⟩
  · exact rcd_seqOut hL hr1 (by rw [X.f8, X.fG, X.fG]; exact X.gsep (by omega) (by omega) (by omega))
      (by rw [X.fG]; exact X.gsep (Or.inl (by omega)) (by decide) (by omega))
      (by rw [X.f8, X.fG]; exact X.gsep (Or.inl (by omega)) (by decide) (by omega)) hm2

end

/-- `Der::bit_string`'s result at `o`, the bits' address and length, with
the reader at `d` over the bytes `L` at `b`. -/
def RcBitsOut (M : Word → BitVec 8) (o d b : Word) (L : Bytes) (r : RcRd) : Except (Option Nat) DerTlv → Prop
  | .error e => memLoad32 M o = 0 ∧ ∀ v, e = some v → M (o + 4) = BitVec.ofNat 8 v
  | .ok t =>
    if t.len ≠ 0 ∧ (rcView L r).getD t.header 0 = 0 then
      memLoad32 M o = b + BitVec.ofNat 32 (r.1 + t.header + 1) ∧ memLoad32 M (o + 4) = BitVec.ofNat 32 (t.len - 1) ∧
        RcRdAt M d b L (rcAdv r t) ∧ t.header + t.len ≤ r.2
    else memLoad32 M o = 0 ∧ M (o + 4) = BitVec.ofNat 8 0x14

theorem rcd_bitsOut {M M' : Word → BitVec 8} {G S o d b : Word} {L : Bytes} {r : RcRd} (hL : RcL M G b L)
    (hr : RcRdAt M d b L r) (hod : Sep o 8 (d + 8) 8) (hSo : Sep S 0x20 o 8) (hSd : Sep S 0x20 (d + 8) 8)
    (h : ∀ x, Sep S 0x20 x 1 →
      M' x = derSliceMem (derAdvance M d (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC))
        (derElement 3 (memBytes M (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat))) o
        (derBitsOf (memBytes M (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat) (memLoad32 M (d + 8))
          (derElement 3 (memBytes M (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat))) x) :
    RcBitsOut M' o d b L r (rcElem L 3 r) := by
  rw [hr.view hL] at h
  unfold rcElem
  rcases hE : derElement 3 (rcView L r) with e | t
  · rw [hE] at h
    refine ⟨by rw [rcd_ld h (rcd_s0 hSo (by decide)), slice_ld0]; rfl, fun v hv => ?_⟩
    cases hv
    rw [h (o + 4) (hSo.subR (c := 4) (l := 1) (by decide))]
    exact (slice_b4 e).trans (rcd_b8 _).symm
  · rw [hE] at h
    have hb := derElement_bound hE
    rw [rcd_view_len hr.2.2] at hb
    have := hr.2.2
    have hC : Sep S 0x20 (d + 0xC) 4 := by have := hSd.subR (c := 4) (l := 4) (by decide); rwa [rcd_c8] at this
    simp only [derBitsOf] at h
    show if _ then _ else _
    split
    · rename_i hc
      rw [ite_eq_left hc] at h
      have ho := rcd_out8 hod (fun x hx => slice_out (M := derAdvance M d (memLoad32 M (d + 8))
        (memLoad32 M (d + 0xC)) (.ok t)) (out := o)
        (.ok (memLoad32 M (d + 8) + BitVec.ofNat 32 (t.header + 1), BitVec.ofNat 32 (t.len - 1))) hx)
      refine ⟨by rw [rcd_ld h (rcd_s0 hSo (by decide)), slice_ld0, hr.1, add_ofNat_assoc, Nat.add_assoc],
        by rw [rcd_ld h (a := o + 4) (hSo.subR (c := 4) (l := 4) (by decide)), slice_ld4],
        rcd_rdAdv hL hr hb (by rw [rcd_ld h (rcd_s0 hSd (by decide)), ho.1, rcd_adv8, hr.1])
          (by rw [rcd_ld h hC, ho.2, rcd_advC]) rfl, hb⟩
    · rename_i hc
      rw [ite_eq_right hc] at h
      exact ⟨by rw [rcd_ld h (rcd_s0 hSo (by decide)), slice_ld0],
        by rw [h (o + 4) (hSo.subR (c := 4) (l := 1) (by decide)), slice_b4]; decide⟩

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

/-- The call of `Der::bit_string` at `off` with the result at `F + oc` and
the reader at `F + dc`. -/
theorem RcCtx.callBits (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {off oc dc : Nat} {hi lo b : Word} {L : Bytes} {r : RcRd}
    (h1 : fetchRel trustedRootReadChainCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootReadChainCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TRC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = RDB)
    (hev : (TRC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = TRC + BitVec.ofNat 32 (off + 8))
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hoc : 0x60 ≤ oc ∧ oc + 8 ≤ 0x14C ∧ oc % 4 = 0) (hdc : 0x60 ≤ dc ∧ dc + 16 ≤ 0x14C ∧ dc % 4 = 0)
    (hod : oc + 8 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (ha0 : f a0 = F + BitVec.ofNat 32 oc) (ha1 : f a1 = F + BitVec.ofNat 32 dc)
    (hL : RcL M G b L) (hr : RcRdAt M (F + BitVec.ofNat 32 dc) b L r)
    (k : ∀ m2 : Machine, RcKeep G M m2.mem → RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 8 (F + BitVec.ofNat 32 (dc + 8)) 8 →
      RcMemInv M0 G F fr fp fl g0 m2.mem →
      RcBitsOut m2.mem (F + BitVec.ofNat 32 oc) (F + BitVec.ofNat 32 dc) b L r (rcElem L 3 r) →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f := by
  have gw := X.gw
  have hw := hL.hw
  have hr2 := hr.2.2
  have eG : F + 0xFFFFFFE0 = G + BitVec.ofNat 32 0x5A0 := X.fneg (k := 0x20) (by decide) (by decide)
  refine X.callK (P := fun m2 => RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 8 (F + BitVec.ofNat 32 (dc + 8)) 8 ∧
      RcBitsOut m2.mem (F + BitVec.ofNat 32 oc) (F + BitVec.ofNat 32 dc) b L r (rcElem L 3 r))
    h1 h2 htgt hI (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hK hP hI' => k m2 hK hP.1 hI' hP.2)
  have C := X.codeAt hI
  rw [← hmem1] at C hL
  have hr1 : RcRdAt m1.mem (F + BitVec.ofNat 32 dc) b L r := by rw [hmem1]; exact hr
  have hsp1 : reg m1 sp = F := by rw [hreg1]; trsimp; exact hR.2.1
  obtain ⟨m2, c2, pc2, hsp2, hk2, hm2⟩ := derBitString_correct m1 (P := RDB) (sp0 := F)
    (out := F + BitVec.ofNat 32 oc) (d := F + BitVec.ofNat 32 dc) (retAddr := TRC + BitVec.ofNat 32 (off + 8))
    ⟨by decide, by decide, C.dbs,
      by rw [show RDB + 0xFFFFD3A0 = RDE from by decide]; exact C.del,
      by rw [show RDB + 0xFFFFD3A0 + 0x26 = TLV from by decide]; exact C.tlv,
      X.fa4, by rw [X.fn]; omega, X.fal hoc.2.2, X.fal hdc.2.2,
      by rw [eG]; exact X.glo (by decide) (by decide) (by decide),
      by rw [eG]; exact X.glo (by decide) (by decide) (by decide),
      by rw [eG]; exact X.glo (by decide) (by decide) (by decide),
      by rw [X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [eG, X.fG]; exact X.gsep (Or.inr (by omega)) (by omega) (by decide),
      by rw [eG, X.f8, X.fG]; exact X.gsep (Or.inr (by omega)) (by omega) (by decide),
      by rw [hr1.len hL, hr1.1, eG]; exact (hL.sep.sub (c := r.1) (l := r.2) (by omega)).subR (by decide),
      by rw [hr1.1, hL.w (by omega)]; have := hL.pos; omega,
      by rw [hr1.len hL, hr1.1, hL.w (by omega)]; omega⟩
    (by rw [hr1.len hL, hr1.1, X.f8, X.fG]; exact (hL.sep.sub (c := r.1) (l := r.2) (by omega)).symm.sub (by omega))
    hpc1 hsp1 (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp) hev
  rw [eG] at hm2
  have hF : RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 8 (F + BitVec.ofNat 32 (dc + 8)) 8 := by
    intro x xa xo xd
    rw [hm2 x (rc_gin (rc_g0 xa) (by decide) (by decide)), slice_out _ xo,
        derAdvance_outside _ (by rw [X.f8]; exact xd), hmem1]
  refine ⟨m2, c2, pc2, ⟨X.keepOf ⟨hoc.1, hoc.2.1⟩ ⟨hdc.1, hdc.2.1⟩ hF, hF, ?_⟩, by rw [hsp2, hsp1], fun q hq => hk2 q (rcd_oid_saved q hq)⟩
  · exact rcd_bitsOut hL hr1 (by rw [X.f8, X.fG, X.fG]; exact X.gsep (by omega) (by omega) (by omega))
      (by rw [X.fG]; exact X.gsep (Or.inl (by omega)) (by decide) (by omega))
      (by rw [X.f8, X.fG]; exact X.gsep (Or.inl (by omega)) (by decide) (by omega)) hm2

end

/-- `Der::optional`'s result at `o`: its discriminant byte, the error byte,
and the reader at `d` over the bytes `L` at `b`. -/
def RcOptOut (M : Word → BitVec 8) (o d b : Word) (L : Bytes) (r : RcRd) :
    Option (Except DerError DerTlv) → Prop
  | none => M o = 0 ∧ RcRdAt M d b L r
  | some (.error e) => M o = 1 ∧ M (o + 1) = derErrByte e
  | some (.ok t) => M o = 0 ∧ RcRdAt M d b L (rcAdv r t) ∧ t.header + t.len ≤ r.2

theorem rcd_ne0 {o x : Word} {k : Nat} (hx : Sep o k x 1) (hk : 0 < k) : x ≠ o := fun e =>
  hx 0 hk 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)

theorem rcd_o4 (o : Word) : Sep (o + 4) 4 o 1 := by
  have := sep_offsets o (c := 4) (n := 4) (d := 0) (k := 1) (.inr (by decide)) (by decide) (by decide)
  rwa [add_ofNat_zero] at this

theorem rcd_o1 (o : Word) : Sep o 1 (o + 1) 1 := by
  have := sep_offsets o (c := 0) (n := 1) (d := 1) (k := 1) (.inl (by decide)) (by decide) (by decide)
  rwa [add_ofNat_zero] at this

theorem rcd_opt_out {M : Word → BitVec 8} {o F' d rp rl x : Word} (res : Option (Except DerError DerTlv))
    (ho : Sep o 0x18 x 1) (hf : Sep (F' + 4) 17 x 1) (hd : Sep (d + 8) 8 x 1) :
    derOptMem M o F' d rp rl res x = M x := by
  rcases res with _ | e | t
  · simp only [derOptMem]
    rw [memStore32_get_sep (a := o + 4) (ho.sub (c := 4) (l := 4) (by decide)), memStore8_ne (rcd_ne0 ho (by decide))]
  · simp only [derOptMem]
    rw [memStore8_ne (rcd_ne0 ho (by decide)), memStore8_ne (rcd_ne0 (o := o + 1) (ho.sub (c := 1) (l := 1) (by decide)) (by decide))]
  · simp only [derOptMem]
    rw [memStore8_ne (rcd_ne0 ho (by decide)), copyBytes_sep (n := 0x14) (dst := o + 4) (ho.sub (c := 4) (l := 0x14) (by decide)) (Nat.le_refl _),
      derTlvMem_outside _ hf, derAdvance_outside _ hd]

theorem rcd_optOut {M M' : Word → BitVec 8} {G S o F' d b : Word} {L : Bytes} {r : RcRd} {tag : Nat}
    (hL : RcL M G b L) (hr : RcRdAt M d b L r) (hod : Sep o 0x18 (d + 8) 8) (hfd : Sep (F' + 4) 17 (d + 8) 8)
    (hSo : Sep S 0x30 o 0x18) (hSd : Sep S 0x30 (d + 8) 8)
    (h : ∀ x, Sep S 0x30 x 1 →
      M' x = derOptMem M o F' d (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC))
        (derOptRes tag (memBytes M (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat)) x) :
    RcOptOut M' o d b L r (derOptRes tag (rcView L r)) := by
  rw [hr.view hL] at h
  have hC : Sep S 0x30 (d + 0xC) 4 := by have := hSd.subR (c := 4) (l := 4) (by decide); rwa [rcd_c8] at this
  have ho1 : Sep S 0x30 o 1 := hSo.subR (c := 0) (l := 1) (by decide) |> fun h => by rwa [add_ofNat_zero] at h
  rcases hE : derOptRes tag (rcView L r) with _ | e | t
  · rw [hE] at h
    have ho := rcd_out8 (M' := derOptMem M o F' d (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)) none) hod
      (fun x hx => by
        simp only [derOptMem]
        rw [memStore32_get_sep (a := o + 4) (hx.sub (c := 4) (l := 4) (by decide)),
          memStore8_ne (rcd_ne0 hx (by decide))])
    refine ⟨by rw [h o ho1]; simp only [derOptMem]; rw [memStore32_get_sep (x := o) (a := o + 4) (rcd_o4 o),
      memStore8_same], ?_⟩
    exact hr.keep ((rcd_ld h (rcd_s0 hSd (by decide))).trans ho.1) ((rcd_ld h hC).trans ho.2)
  · rw [hE] at h
    refine ⟨by rw [h o ho1]; simp only [derOptMem]; rw [memStore8_same], ?_⟩
    rw [h (o + 1) (hSo.subR (c := 1) (l := 1) (by decide))]
    simp only [derOptMem]
    rw [memStore8_ne (rcd_ne0 (rcd_o1 o) (by decide)), memStore8_same]
  · rw [hE] at h
    have hb0 : ∀ V : Bytes, derOptRes tag V = some (.ok t) → t.header + t.len ≤ V.length := by
      intro V hV
      cases V with
      | nil => cases hV
      | cons a l =>
        simp only [derOptRes] at hV; split at hV
        · exact derTlv_bound (Option.some.inj hV)
        · cases hV
    have hb : t.header + t.len ≤ r.2 := by have := hb0 _ hE; rwa [rcd_view_len hr.2.2] at this
    have ho := rcd_out8 (M' := derOptMem M o F' d (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)) (some (.ok t)))
      (M := derTlvMem M (F' + 4) d (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)) (.ok t)) hod (fun x hx => by
        simp only [derOptMem]
        rw [memStore8_ne (rcd_ne0 hx (by decide)),
          copyBytes_sep (n := 0x14) (dst := o + 4) (hx.sub (c := 4) (l := 0x14) (by decide)) (Nat.le_refl _)])
    have hf := rcd_out8 hfd (fun x hx => derTlvMem_outside (M := M) (d := d) (rp := memLoad32 M (d + 8))
      (rl := memLoad32 M (d + 0xC)) (.ok t) hx)
    refine ⟨by rw [h o ho1]; simp only [derOptMem]; rw [memStore8_same], ?_, hb⟩
    exact rcd_rdAdv hL hr hb (by rw [rcd_ld h (rcd_s0 hSd (by decide)), ho.1, hf.1, rcd_adv8, hr.1])
      (by rw [rcd_ld h hC, ho.2, hf.2, rcd_advC]) rfl

theorem rcd_opt_saved : ∀ q : Fin 32, q.val ∈ trSaved → optKeep q = true := by decide

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

/-- The call of `Der::optional` at `off` with the result at `F + oc` and
the reader at `F + dc`. -/
theorem RcCtx.callOpt (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {off oc dc tag : Nat} {hi lo b : Word} {L : Bytes} {r : RcRd}
    (h1 : fetchRel trustedRootReadChainCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootReadChainCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TRC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = RDO)
    (hev : (TRC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = TRC + BitVec.ofNat 32 (off + 8))
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hoc : 0x60 ≤ oc ∧ oc + 0x18 ≤ 0x14C ∧ oc % 4 = 0) (hdc : 0x60 ≤ dc ∧ dc + 16 ≤ 0x14C ∧ dc % 4 = 0)
    (hod : oc + 0x18 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (ha0 : f a0 = F + BitVec.ofNat 32 oc) (ha1 : f a1 = F + BitVec.ofNat 32 dc) (ha2 : f a2 = BitVec.ofNat 32 tag)
    (htag : tag < 256) (hL : RcL M G b L) (hr : RcRdAt M (F + BitVec.ofNat 32 dc) b L r)
    (k : ∀ m2 : Machine, RcKeep G M m2.mem → RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 24 (F + BitVec.ofNat 32 (dc + 8)) 8 →
      RcMemInv M0 G F fr fp fl g0 m2.mem →
      RcOptOut m2.mem (F + BitVec.ofNat 32 oc) (F + BitVec.ofNat 32 dc) b L r (derOptRes tag (rcView L r)) →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f := by
  have gw := X.gw
  have hw := hL.hw
  have hr2 := hr.2.2
  have eG : F + 0xFFFFFFD0 = G + BitVec.ofNat 32 0x590 := X.fneg (k := 0x30) (by decide) (by decide)
  have eF : F + 0xFFFFFFE0 + 4 = G + BitVec.ofNat 32 0x5A4 := by
    rw [X.fneg (k := 0x20) (by decide) (by decide)]; exact add_ofNat_assoc G 0x5A0 4
  refine X.callK (P := fun m2 => RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 24 (F + BitVec.ofNat 32 (dc + 8)) 8 ∧
      RcOptOut m2.mem (F + BitVec.ofNat 32 oc) (F + BitVec.ofNat 32 dc) b L r
      (derOptRes tag (rcView L r)))
    h1 h2 htgt hI (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hK hP hI' => k m2 hK hP.1 hI' hP.2)
  have C := X.codeAt hI
  rw [← hmem1] at C hL
  have hr1 : RcRdAt m1.mem (F + BitVec.ofNat 32 dc) b L r := by rw [hmem1]; exact hr
  have hsp1 : reg m1 sp = F := by rw [hreg1]; trsimp; exact hR.2.1
  obtain ⟨m2, c2, pc2, hsp2, hk2, hm2⟩ := derOptional_correct m1 (P := RDO) (sp0 := F)
    (out := F + BitVec.ofNat 32 oc) (d := F + BitVec.ofNat 32 dc) (retAddr := TRC + BitVec.ofNat 32 (off + 8))
    (tag := tag)
    ⟨by decide, C.dop,
      by rw [show RDO + 0xFFFFD382 = TLV from by decide]; exact C.tlv,
      by rw [show RDO + 0xA4BA = BMS from by decide]; exact C.dec.stub,
      by rw [show RDO + 0xA4C2 = BMB from by decide]; exact C.dec.body,
      X.fa4, by rw [X.fn]; omega, X.fal hoc.2.2, X.fal hdc.2.2, by rw [X.fG, X.gc (by omega)]; omega,
      by rw [eG]; exact X.glo (by decide) (by decide) (by decide),
      by rw [eG]; exact X.glo (by decide) (by decide) (by decide),
      by rw [eG]; exact X.glo (by decide) (by decide) (by decide),
      by rw [eG]; exact X.glo (by decide) (by decide) (by decide),
      by rw [X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [eG, X.fG]; exact X.gsep (Or.inr (by omega)) (by omega) (by decide),
      by rw [eG, X.f8, X.fG]; exact X.gsep (Or.inr (by omega)) (by omega) (by decide),
      by rw [X.f8, X.fG, X.fG]; exact X.gsep (by omega) (by omega) (by omega),
      by rw [hr1.len hL, hr1.1, eG]; exact (hL.sep.sub (c := r.1) (l := r.2) (by omega)).subR (by decide),
      by rw [hr1.1, hL.w (by omega)]; have := hL.pos; omega,
      by rw [hr1.len hL, hr1.1, hL.w (by omega)]; omega⟩
    hpc1 hsp1 (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp; exact ha2)
    htag (by rw [hreg1]; trsimp) hev
  rw [eG] at hm2
  have hF : RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 24 (F + BitVec.ofNat 32 (dc + 8)) 8 := by
    intro x xa xo xd
    rw [hm2 x (rc_gin (rc_g0 xa) (by decide) (by decide)), rcd_opt_out _
        xo
        (by rw [eF]; exact rc_gin (rc_g0 xa) (by decide) (by decide))
        (by rw [X.f8]; exact xd), hmem1]
  refine ⟨m2, c2, pc2, ⟨X.keepOf ⟨hoc.1, hoc.2.1⟩ ⟨hdc.1, hdc.2.1⟩ hF, hF, ?_⟩, by rw [hsp2, hsp1], fun q hq => hk2 q (rcd_opt_saved q hq)⟩
  · exact rcd_optOut hL hr1 (by rw [X.f8, X.fG, X.fG]; exact X.gsep (by omega) (by omega) (by omega))
      (by rw [eF, X.f8, X.fG]; exact X.gsep (Or.inl (by omega)) (by decide) (by omega))
      (by rw [X.fG]; exact X.gsep (Or.inl (by omega)) (by decide) (by omega))
      (by rw [X.f8, X.fG]; exact X.gsep (Or.inl (by omega)) (by decide) (by omega)) hm2

end


/-- `time::read_time`'s result at `o` for the reader `r` at `d`: the time
and the reader over the bytes it leaves, or tag 1 and `readTimeErr`'s byte. -/
def RcTimeOut (M : Word → BitVec 8) (o d b : Word) (L : Bytes) (r : RcRd) : Option (Nat × Bytes) → Prop
  | none => M o = 1 ∧ M (o + 1) = BitVec.ofNat 8 (readTimeErr (rcView L r))
  | some (t, r1) => t < 2 ^ 64 ∧ M o = 0 ∧ memLoad32 M (o + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
      memLoad32 M (o + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32) ∧ r1.length ≤ r.2 ∧
      RcRdAt M d b L (r.1 + (r.2 - r1.length), r1.length)

theorem rcd_time_saved : ∀ q : Fin 32, q.val ∈ trSaved →
    q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by decide

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

/-- The call of `time::read_time` at `off` with the result at `F + oc` and
the reader at `F + dc`. -/
theorem RcCtx.callTime (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {off oc dc : Nat} {hi lo b : Word} {L : Bytes} {r : RcRd}
    (h1 : fetchRel trustedRootReadChainCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootReadChainCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TRC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = XRT)
    (hev : (TRC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = TRC + BitVec.ofNat 32 (off + 8))
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hoc : 0x60 ≤ oc ∧ oc + 16 ≤ 0x14C ∧ oc % 4 = 0) (hdc : 0x60 ≤ dc ∧ dc + 16 ≤ 0x14C ∧ dc % 4 = 0)
    (hod : oc + 16 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (ha0 : f a0 = F + BitVec.ofNat 32 oc) (ha1 : f a1 = F + BitVec.ofNat 32 dc)
    (hL : RcL M G b L) (hr : RcRdAt M (F + BitVec.ofNat 32 dc) b L r)
    (k : ∀ m2 : Machine, RcKeep G M m2.mem → RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 16 (F + BitVec.ofNat 32 (dc + 8)) 8 →
      RcMemInv M0 G F fr fp fl g0 m2.mem →
      RcTimeOut m2.mem (F + BitVec.ofNat 32 oc) (F + BitVec.ofNat 32 dc) b L r (readTime (rcView L r)) →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f := by
  have gw := X.gw
  have hw := hL.hw
  have hr2 := hr.2.2
  have eR : F + 0xFFFFFFA0 = G + BitVec.ofNat 32 0x560 := X.fneg (k := 0x60) (by decide) (by decide)
  refine X.callK (P := fun m2 => RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 16 (F + BitVec.ofNat 32 (dc + 8)) 8 ∧
      RcTimeOut m2.mem (F + BitVec.ofNat 32 oc) (F + BitVec.ofNat 32 dc) b L r
      (readTime (rcView L r)))
    h1 h2 htgt hI (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hK hP hI' => k m2 hK hP.1 hI' hP.2)
  have C := X.codeAt hI
  rw [← hmem1] at C hL
  have hr1 : RcRdAt m1.mem (F + BitVec.ofNat 32 dc) b L r := by rw [hmem1]; exact hr
  have hV : memBytes m1.mem (b + BitVec.ofNat 32 r.1) r.2 = rcView L r := by
    have := hr1.view hL; rwa [hr1.len hL, hr1.1] at this
  have hsp1 : reg m1 sp = F := by rw [hreg1]; trsimp; exact hR.2.1
  have hfn := X.fn
  obtain ⟨m2, c2, pc2, hsp2, hk2, hsome, hnone, hm2⟩ := x509ReadTime_correct m1 (sp0 := F)
    (out := F + BitVec.ofNat 32 oc) (d := F + BitVec.ofNat 32 dc) (rp := b + BitVec.ofNat 32 r.1) (rl := r.2)
    (retAddr := TRC + BitVec.ofNat 32 (off + 8))
    C.xrt C.tlv C.gnt C.tvf.dt C.tvf.td C.tvf.td4 C.tvf.aad hpc1 (by rw [hreg1]; trsimp; exact ha0)
    (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp) hev hsp1 X.fa4 (by omega) (by omega)
    (by rw [X.fG, X.gc (by omega)]; omega) (X.fal hoc.2.2) (by rw [X.fG, X.gc (by omega)]; omega) (X.fal hdc.2.2)
    hr1.1 hr1.2.1 (by rw [hL.w (by omega)]; omega) (by rw [hL.w (by omega)]; have := hL.pos; omega)
    (by rw [eR, X.fG]; exact X.gsep (Or.inr (by omega)) (by omega) (by decide))
    (by rw [eR, X.f8, X.fG]; exact X.gsep (Or.inr (by omega)) (by omega) (by decide))
    (by rw [X.f8, X.fG, X.fG]; exact X.gsep (by omega) (by omega) (by omega))
    (by rw [eR]; exact (hL.sep.sub (c := r.1) (l := r.2 + 14) (by omega)).subR (by decide))
    (by rw [X.f8, X.fG]; exact (hL.sep.sub (c := r.1) (l := r.2) (by omega)).subR (by omega))
  have hF : RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 16 (F + BitVec.ofNat 32 (dc + 8)) 8 := by
    intro x xa xo xd
    rw [hm2 x (by rw [eR]; exact rc_gin (rc_g0 xa) (by decide) (by decide))
        xo
        (by rw [X.f8]; exact xd), hmem1]
  refine ⟨m2, c2, pc2, ⟨X.keepOf ⟨hoc.1, hoc.2.1⟩ ⟨hdc.1, hdc.2.1⟩ hF, hF, ?_⟩, by rw [hsp2, hsp1], fun q hq => hk2 q (rcd_time_saved q hq)⟩
  · rw [← hV]
    rcases hT : readTime (memBytes m1.mem (b + BitVec.ofNat 32 r.1) r.2) with _ | ⟨t, r1⟩
    · exact ⟨(hnone hT).1, (hnone hT).2.trans (by rw [hV])⟩
    · obtain ⟨h64, h0, h8, hC, j, hj, hd8, hdC, hr1'⟩ := hsome t r1 hT
      have hl : r1.length = r.2 - j := by rw [hr1', memBytes_length]
      refine ⟨h64, h0, h8, hC, by omega, ?_, ?_, ?_⟩
      · rw [hd8, hl, show r.2 - (r.2 - j) = j by omega, add_ofNat_assoc]
      · rw [hdC, hl]
      · show _ + _ ≤ _; omega

end


theorem RcL.view2 {M : Word → BitVec 8} {G b : Word} {L : Bytes} (h : RcL M G b L) {i j : Nat}
    (hr : i + j ≤ L.length) : memBytes M (b + BitVec.ofNat 32 i) j = rcView L (i, j) :=
  h.view (r := (i, j)) hr

/-- What `Der::algorithm` stores at `o`, as `derAlgorithm_correct` states
it. -/
def rcAlgMem (M : Word → BitVec 8) (o : Word) :
    Except (BitVec 8) ((Word × Nat) × Option (Word × DerTlv)) → Prop
  | .error b => memLoad32 M o = 0 ∧ M (o + 4) = b
  | .ok ((op, ol), none) => memLoad32 M o = op ∧ memLoad32 M (o + 4) = BitVec.ofNat 32 ol ∧
      memLoad32 M (o + 8) = 0
  | .ok ((op, ol), some (rp, u)) => memLoad32 M o = op ∧
      memLoad32 M (o + 4) = BitVec.ofNat 32 ol ∧
      memLoad32 M (o + 8) = rp + BitVec.ofNat 32 u.header ∧
      memLoad32 M (o + 0xC) = BitVec.ofNat 32 u.len ∧ memLoad32 M (o + 0x10) = rp ∧
      memLoad32 M (o + 0x14) = BitVec.ofNat 32 (u.header + u.len) ∧
      M (o + 0x18) = BitVec.ofNat 8 u.tag

/-- `Der::algorithm`'s result at `o` for the reader `r` over the bytes `L`
at `b`: the OID's offset and length, and the parameters' offset, element,
and tag, all inside `L`. -/
def RcAlgOut (M : Word → BitVec 8) (o b : Word) (L : Bytes) :
    Except Unit ((Nat × Nat) × Option (Nat × DerTlv)) → Prop
  | .error _ => memLoad32 M o = 0
  | .ok ((oo, ol), par) => memLoad32 M o = b + BitVec.ofNat 32 oo ∧ memLoad32 M (o + 4) = BitVec.ofNat 32 ol ∧
      oo + ol ≤ L.length ∧
      match par with
      | none => memLoad32 M (o + 8) = 0
      | some (q, u) => memLoad32 M (o + 8) = b + BitVec.ofNat 32 (q + u.header) ∧
          memLoad32 M (o + 0xC) = BitVec.ofNat 32 u.len ∧ M (o + 0x18) = BitVec.ofNat 8 u.tag ∧
          q + u.header + u.len ≤ L.length

theorem rcd_algOut {M M' : Word → BitVec 8} {G o b : Word} {L : Bytes} {r : RcRd} (hL : RcL M G b L)
    (hr2 : r.1 + r.2 ≤ L.length) (hA : rcAlgMem M' o (derAlgOf M (b + BitVec.ofNat 32 r.1) r.2)) :
    RcAlgOut M' o b L (rcAlg L r) := by
  unfold rcAlg; unfold derAlgOf at hA; rw [hL.view hr2] at hA
  rcases hE : derElement 0x30 (rcView L r) with e | t
  · rw [hE] at hA; exact hA.1
  · rw [hE] at hA; dsimp only at hA ⊢
    have hb := derElement_bound hE; rw [rcd_view_len hr2] at hb
    simp only [add_ofNat_assoc] at hA
    rw [hL.view2 (by omega)] at hA
    rcases hO : derOid (rcView L (r.1 + t.header, t.len)) with e | o
    · rw [hO] at hA; exact hA.1
    · rw [hO] at hA; dsimp only at hA ⊢
      have hob : o.header + o.len ≤ t.len := by
        have := derElement_bound (derOid_ok_elem hO)
        rwa [rcd_view_len (show r.1 + t.header + t.len ≤ L.length by omega)] at this
      by_cases hz : t.len - (o.header + o.len) = 0
      · rw [ite_eq_left hz] at hA ⊢
        exact ⟨hA.1, hA.2.1, by omega, hA.2.2⟩
      · rw [ite_eq_right hz] at hA ⊢
        rw [hL.view2 (by omega)] at hA
        rcases hU : derTlv (rcView L (r.1 + t.header + (o.header + o.len), t.len - (o.header + o.len))) with e | u
        · rw [hU] at hA; exact hA.1
        · rw [hU] at hA; dsimp only at hA ⊢
          by_cases hu : u.header + u.len = t.len - (o.header + o.len)
          · rw [ite_eq_left hu] at hA ⊢
            exact ⟨hA.1, hA.2.1, by omega, by rw [hA.2.2.1, add_ofNat_assoc], hA.2.2.2.1, hA.2.2.2.2.2.2, by omega⟩
          · rw [ite_eq_right hu] at hA ⊢
            exact hA.1

/-- The reader at `d` after `Der::algorithm`: past the algorithm's
element when `Der::element` reads one. -/
def RcAlgRd (M : Word → BitVec 8) (d b : Word) (L : Bytes) (r : RcRd) : Prop :=
  ∀ a, derElement 0x30 (rcView L r) = .ok a → RcRdAt M d b L (rcAdv r a) ∧ a.header + a.len ≤ r.2

theorem rcd_algRd {M M' : Word → BitVec 8} {G S o d b : Word} {L : Bytes} {r : RcRd} {k l : Nat}
    (hL : RcL M G b L) (hr : RcRdAt M d b L r) (hSd : Sep S k (d + 8) 8) (hod : Sep o l (d + 8) 8)
    (h : ∀ x, Sep S k x 1 → Sep o l x 1 →
      M' x = derAdvance M d (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC))
        (derElement 0x30 (memBytes M (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat)) x) :
    RcAlgRd M' d b L r := by
  intro a ha
  rw [hr.view hL, ha] at h
  have hb := derElement_bound ha; rw [rcd_view_len hr.2.2] at hb
  have hC1 : Sep S k (d + 0xC) 4 := by have := hSd.subR (c := 4) (l := 4) (by decide); rwa [rcd_c8] at this
  have hC2 : Sep o l (d + 0xC) 4 := by have := hod.subR (c := 4) (l := 4) (by decide); rwa [rcd_c8] at this
  have l8 : memLoad32 M' (d + 8) = memLoad32 (derAdvance M d (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)) (.ok a)) (d + 8) :=
    memLoad32_congr fun _ hj => h _ ((rcd_s0 hSd (by decide)).symm.shift hj).symm
      ((rcd_s0 hod (by decide)).symm.shift hj).symm
  have lC : memLoad32 M' (d + 0xC) = memLoad32 (derAdvance M d (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)) (.ok a)) (d + 0xC) :=
    memLoad32_congr fun _ hj => h _ (hC1.symm.shift hj).symm (hC2.symm.shift hj).symm
  exact ⟨rcd_rdAdv hL hr hb (by rw [l8, rcd_adv8, hr.1]) (by rw [lC, rcd_advC]) rfl, hb⟩

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

/-- The call of `Der::algorithm` at `off` with the result at `F + oc` and
the reader at `F + dc`. -/
theorem RcCtx.callAlg (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {off oc dc : Nat} {hi lo b : Word} {L : Bytes} {r : RcRd}
    (h1 : fetchRel trustedRootReadChainCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootReadChainCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TRC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = RDA)
    (hev : (TRC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = TRC + BitVec.ofNat 32 (off + 8))
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hoc : 0x60 ≤ oc ∧ oc + 0x1C ≤ 0x14C ∧ oc % 4 = 0) (hdc : 0x60 ≤ dc ∧ dc + 16 ≤ 0x14C ∧ dc % 4 = 0)
    (hod : oc + 0x1C ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (ha0 : f a0 = F + BitVec.ofNat 32 oc) (ha1 : f a1 = F + BitVec.ofNat 32 dc)
    (hL : RcL M G b L) (hr : RcRdAt M (F + BitVec.ofNat 32 dc) b L r)
    (k : ∀ m2 : Machine, RcKeep G M m2.mem → RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 28 (F + BitVec.ofNat 32 (dc + 8)) 8 →
      RcMemInv M0 G F fr fp fl g0 m2.mem →
      RcAlgOut m2.mem (F + BitVec.ofNat 32 oc) b L (rcAlg L r) → RcAlgRd m2.mem (F + BitVec.ofNat 32 dc) b L r →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f := by
  have gw := X.gw
  have hw := hL.hw
  have hr2 := hr.2.2
  have eA : F + 0xFFFFFF90 = G + BitVec.ofNat 32 0x550 := X.fneg (k := 0x70) (by decide) (by decide)
  refine X.callK (P := fun m2 => RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 28 (F + BitVec.ofNat 32 (dc + 8)) 8 ∧
      RcAlgOut m2.mem (F + BitVec.ofNat 32 oc) b L (rcAlg L r) ∧
      RcAlgRd m2.mem (F + BitVec.ofNat 32 dc) b L r)
    h1 h2 htgt hI (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hK hP hI' => k m2 hK hP.1 hI' hP.2.1 hP.2.2)
  have C := X.codeAt hI
  rw [← hmem1] at C hL
  have hr1 : RcRdAt m1.mem (F + BitVec.ofNat 32 dc) b L r := by rw [hmem1]; exact hr
  have hsp1 : reg m1 sp = F := by rw [hreg1]; trsimp; exact hR.2.1
  have hfn := X.fn
  obtain ⟨m2, c2, pc2, hsp2, hk2, hm2, hA⟩ := derAlgorithm_correct m1 (P := RDA) (sp0 := F)
    (out := F + BitVec.ofNat 32 oc) (d := F + BitVec.ofNat 32 dc) (p := b + BitVec.ofNat 32 r.1) (n := r.2)
    (retAddr := TRC + BitVec.ofNat 32 (off + 8))
    ⟨by decide, C.dal,
      by rw [show RDA + 0xFFFFD080 = RDS from by decide]; exact C.dsq,
      by rw [show RDA + 0xFFFFD2F8 = RDN from by decide]; exact C.nst,
      by rw [show RDA + 0xFFFFD218 = RDE from by decide]; exact C.del,
      by rw [show RDA + 0xFFFFD23E = TLV from by decide]; exact C.tlv,
      by rw [show RDA + 0xDA = ROI from by decide]; exact C.oid,
      by rw [show RDA + 0xA376 = BMS from by decide]; exact C.dec.stub,
      by rw [show RDA + 0xA37E = BMB from by decide]; exact C.dec.body,
      X.fa4, by omega, X.fal hoc.2.2, by rw [X.fG, X.gc (by omega)]; omega, X.fal hdc.2.2,
      hr1.1, hr1.2.1, by rw [hL.w (by omega)]; have := hL.pos; omega, by rw [hL.w (by omega)]; omega,
      by rw [eA]; exact X.glo (by decide) (by decide) (by decide),
      by rw [eA]; exact X.glo (by decide) (by decide) (by decide),
      by rw [eA]; exact X.glo (by decide) (by decide) (by decide),
      by rw [eA]; exact X.glo (by decide) (by decide) (by decide),
      by rw [eA]; exact X.glo (by decide) (by decide) (by decide),
      by rw [eA]; exact X.glo (by decide) (by decide) (by decide),
      by rw [eA]; exact X.glo (by decide) (by decide) (by decide),
      by rw [eA]; exact X.glo (by decide) (by decide) (by decide),
      by rw [X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [eA, X.fG]; exact X.gsep (Or.inr (by omega)) (by omega) (by decide),
      by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [X.f8, X.fG]; exact X.glo (by omega) (by decide) (by decide),
      by rw [eA, X.f8, X.fG]; exact X.gsep (Or.inr (by omega)) (by omega) (by decide),
      by rw [X.f8, X.fG, X.fG]; exact X.gsep (by omega) (by omega) (by omega),
      by rw [eA]; exact (hL.sep.sub (c := r.1) (l := r.2) (by omega)).subR (by decide),
      by rw [X.f8, X.fG]; exact (hL.sep.sub (c := r.1) (l := r.2) (by omega)).subR (by omega)⟩
    hpc1 hsp1 (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp) hev
  rw [eA] at hm2
  have hF : RcFr G M m2.mem (F + BitVec.ofNat 32 oc) 28 (F + BitVec.ofNat 32 (dc + 8)) 8 := by
    intro x xa xo xd
    rw [hm2 x (rc_gin (rc_g0 xa) (by decide) (by decide)) xo,
        derAdvance_outside _ (by rw [X.f8]; exact xd), hmem1]
  refine ⟨m2, c2, pc2, ⟨X.keepOf ⟨hoc.1, hoc.2.1⟩ ⟨hdc.1, hdc.2.1⟩ hF, hF, rcd_algOut hL hr2 hA, ?_⟩, by rw [hsp2, hsp1],
    fun q hq => hk2 q (rcd_time_saved q hq)⟩
  · refine rcd_algRd (S := G + BitVec.ofNat 32 0x550) (k := 0x70) (o := F + BitVec.ofNat 32 oc) (l := 0x1C)
      hL hr1 (by rw [X.f8, X.fG]; exact X.gsep (Or.inl (by omega)) (by decide) (by omega))
      (by rw [X.f8, X.fG, X.fG]; exact X.gsep (by omega) (by omega) (by omega)) (fun x xa xb => ?_)
    rw [hr1.1, hr1.len hL, hr1.2.1]; exact hm2 x xa xb

end

end C3.RV32
