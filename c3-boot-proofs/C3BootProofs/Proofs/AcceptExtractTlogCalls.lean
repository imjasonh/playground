import C3BootProofs.Proofs.AcceptExtractTlog

/-!
# The calls of a transparency log pass

A pass calls `field`, `str`, and `next_element` on slices of the document,
with their results in the frame at `sp + 0x1320` and `sp + 0x890`. The
wrappers here state each call's result as the spec's value of the item
(`AceVal`), and its frame as agreement outside the callees' ranges
(`AcetlV`).

`AcetlS` is the state a pass carries between its calls: memory agrees with
the machine at the start of the pass outside the pass's writes, the cursor
over the items left, and `keys`'s slice at `sp + 0x1FDC`.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

set_option maxRecDepth 100000

/-! ## The document -/

/-- The document's bytes, read from memory. -/
def AcetlDoc (X : AceCtx) (M : Word → BitVec 8) : Prop :=
  ∀ (p : Word) (n : Nat), X.D.toNat ≤ p.toNat → p.toNat + n ≤ X.D.toNat + X.json.length →
    memBytes M p n = slice X.json (p.toNat - X.D.toNat) n

/-- `s`, the bytes at `q` of the document. -/
def AcetlIn (X : AceCtx) (q : Word) (s : Bytes) : Prop :=
  X.D.toNat ≤ q.toNat ∧ q.toNat + s.length ≤ X.D.toNat + X.json.length ∧
    slice X.json (q.toNat - X.D.toNat) s.length = s

theorem acetl_sliceLen (d : Bytes) (a b : Nat) : (slice d a b).length ≤ b := by
  unfold slice; simp only [List.length_take]; omega

theorem acetl_sliceLen' {d : Bytes} {a b : Nat} (h : a + b ≤ d.length) : (slice d a b).length = b := by
  unfold slice; simp only [List.length_take, List.length_drop]; omega

theorem acetl_addN {p : Word} {a : Nat} (h : p.toNat + a < 2 ^ 32) : (p + BitVec.ofNat 32 a).toNat = p.toNat + a := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

section
variable {X : AceCtx} (O : X.Ok)
include O

/-- A value's bounds: in the document, which lies in `doc`. -/
theorem acetl_valB {p : Word} {l : Nat} {j : Json} (hv : AceVal X.D X.json p l j) :
    X.D.toNat ≤ p.toNat ∧ p.toNat + l ≤ X.D.toNat + X.json.length ∧ X.Bf.toNat + 0x4000 ≤ p.toNat ∧
      p.toNat + l ≤ X.Bf.toNat + 0x6800 ∧ X.Bf.toNat + 0x6800 ≤ 0x40000000 := by
  have h1 := hv.1; have h2 := hv.2.1
  have hlo := O.pre.docLo; have hhi := O.pre.docHi; have hb := O.lay.hi
  unfold acBufLen at hb
  refine ⟨h1, by omega, by omega, by omega, by omega⟩

theorem acetl_inB {q : Word} {s : Bytes} (h : AcetlIn X q s) :
    X.Bf.toNat + 0x4000 ≤ q.toNat ∧ q.toNat + s.length ≤ X.Bf.toNat + 0x6800 ∧ X.Bf.toNat + 0x6800 ≤ 0x40000000 := by
  have h1 := h.1; have h2 := h.2.1
  have hlo := O.pre.docLo; have hhi := O.pre.docHi; have hb := O.lay.hi
  unfold acBufLen at hb
  refine ⟨by omega, by omega, by omega⟩

/-- A byte of the document lies outside the stack. -/
theorem acetl_docOut {p : Word} {i : Nat} (h1 : X.D.toNat ≤ p.toNat + i)
    (h2 : p.toNat + i < X.D.toNat + X.json.length) :
    (p + BitVec.ofNat 32 i).toNat < X.B.toNat ∨ X.B.toNat + 0x5A70 ≤ (p + BitVec.ofNat 32 i).toNat := by
  have hlo := O.pre.docLo; have hhi := O.pre.docHi; have hb := O.lay.hi
  unfold acBufLen at hb
  have e := acetl_addN (p := p) (a := i) (by omega)
  exact ace_ofSep (ace_bufOut O.lay (by omega) (by unfold acBufLen; omega))

theorem acetl_docV {M M' : Word → BitVec 8} (hd : AcetlDoc X M) (h : ∀ x, AcetlV X.B x → M' x = M x) :
    AcetlDoc X M' := fun p n h1 h2 =>
  (ace_memBytes_ext fun i hi => h _ (acetl_V_out (acetl_docOut O (by omega) (by omega)))).trans (hd p n h1 h2)

theorem acetl_docU {M M' : Word → BitVec 8} {fp : Word} (hd : AcetlDoc X M) (hfp : X.Bf.toNat + 0x6800 ≤ fp.toNat)
    (h : ∀ x, AcetlU X.B X.Bf fp true x → M' x = M x) : AcetlDoc X M' := by
  refine fun p n h1 h2 => (ace_memBytes_ext fun i hi => h _ ?_).trans (hd p n h1 h2)
  have hlo := O.pre.docLo; have hhi := O.pre.docHi
  have e := acetl_addN (p := p) (a := i) (by have := O.lay.hi; unfold acBufLen at this; omega)
  exact acetl_U_out (acetl_docOut O (by omega) (by omega)) (.inl (by omega))

theorem acetl_inBytes {M : Word → BitVec 8} (hd : AcetlDoc X M) {q : Word} {s : Bytes} (h : AcetlIn X q s) :
    memBytes M q s.length = s := by
  rw [hd q s.length h.1 h.2.1]; exact h.2.2

theorem acetl_valBytes {M : Word → BitVec 8} (hd : AcetlDoc X M) {p : Word} {l : Nat} {j : Json}
    (hv : AceVal X.D X.json p l j) : memBytes M p l = slice X.json (p.toNat - X.D.toNat) l := by
  obtain ⟨b1, b2, -⟩ := acetl_valB O hv
  exact hd p l b1 b2

end

/-! ## The state between calls -/

/-- What a pass carries between calls, with `keys`'s free part at `fp`. -/
structure AcetlS (X : AceCtx) (n0 : Machine) (fp0 : Word) (M : Word → BitVec 8) (fp : Word) (rest : List Json) :
    Prop where
  m : ∀ x, AcetlU X.B X.Bf fp0 true x → M x = n0.mem x
  cur : AceCur X.D X.json M (acSlot X.B 0x1860) rest
  fpv : memLoad32 M (acSlot X.B 0x1FDC) = fp
  flv : memLoad32 M (acSlot X.B 0x1FE0) = BitVec.ofNat 32 (X.Bf.toNat + 0xB840 - fp.toNat)
  lo : fp0.toNat ≤ fp.toNat
  hi : fp.toNat ≤ X.Bf.toNat + 0xB840

theorem acetl_s4 {B : Word} : acSlot B 0x1860 + 4 = acSlot B 0x1864 := by
  unfold acSlot; rw [BitVec.add_assoc]; rfl

theorem acetl_s8 {B : Word} : acSlot B 0x1860 + 8 = acSlot B 0x1868 := by
  unfold acSlot; rw [BitVec.add_assoc]; rfl

section
variable {X : AceCtx} {n0 : Machine} {fp0 fp : Word} {rest : List Json} {M M' : Word → BitVec 8}

theorem acetl_cur3 (O : X.Ok) (h : ∀ x, AcetlV X.B x → M' x = M x) (hc : AceCur X.D X.json M (acSlot X.B 0x1860) rest) :
    AceCur X.D X.json M' (acSlot X.B 0x1860) rest := by
  refine acetl_cur_move hc (acetl_ldV O h (s := 0x1860) (by decide) (by decide)) ?_ ?_
  · rw [acetl_s4]; exact acetl_ldV O h (s := 0x1864) (by decide) (by decide)
  · rw [acetl_s8]; exact acetl_ldV O h (s := 0x1868) (by decide) (by decide)

/-- A call that writes only the callees' ranges keeps the state. -/
theorem AcetlS.call (O : X.Ok) (S : AcetlS X n0 fp0 M fp rest) (h : ∀ x, AcetlV X.B x → M' x = M x) :
    AcetlS X n0 fp0 M' fp rest :=
  ⟨fun x hx => (h x (acetl_UV hx)).trans (S.m x hx), acetl_cur3 O h S.cur,
    (acetl_ldV O h (s := 0x1FDC) (by decide) (by decide)).trans S.fpv,
    (acetl_ldV O h (s := 0x1FE0) (by decide) (by decide)).trans S.flv, S.lo, S.hi⟩

/-- A store to `sp + 0x1C` or `sp + 0x28` keeps the state. -/
theorem AcetlS.store (O : X.Ok) (S : AcetlS X n0 fp0 M fp rest) {s : Nat} (hs : s = 0x1C ∨ s = 0x28) (v : Word) :
    AcetlS X n0 fp0 (memStore32 M (acSlot X.B s) v) fp rest := by
  have F := O.lay.fr
  have hW : (0x3A50 + s, 0x3A50 + s + 4) ∈ acetlW := by rcases hs with rfl | rfl <;> decide
  have hs4 : 0x3A50 + s + 4 ≤ 0x5A70 := by omega
  have hld : ∀ t, 0x3A50 + t + 4 ≤ 0x5A70 → (s + 4 ≤ t ∨ t + 4 ≤ s) →
      memLoad32 (memStore32 M (acSlot X.B s) v) (acSlot X.B t) = memLoad32 M (acSlot X.B t) :=
    fun t ht h => acetl_ldS F h hs4 ht
  refine ⟨fun x hx => (memStore32_get_sep (acetl_sep F hx hW (c := 0x3A50 + s) (n := 4) (Nat.le_refl _) (Nat.le_refl _)).symm).trans
      (S.m x hx), acetl_cur_move S.cur ?_ ?_ ?_, (hld 0x1FDC (by decide) (by omega)).trans S.fpv,
    (hld 0x1FE0 (by decide) (by omega)).trans S.flv, S.lo, S.hi⟩
  · exact hld 0x1860 (by decide) (by omega)
  · rw [acetl_s4]; exact hld _ (by decide) (by omega)
  · rw [acetl_s8]; exact hld _ (by decide) (by omega)

theorem acetl_env (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (hm : ∀ x, AcetlU X.B X.Bf fp0 true x → M x = n0.mem x) :
    AcExtractEnv M :=
  O.env M fun x h1 h2 => by
    have := A.fr.hi; have := A.fr.lo; have h2' := ace_ofSep h2; unfold acBufLen at h2'
    exact (hm x (acetl_U_out (ace_ofSep h1) (by omega))).trans (A.inv.out x h1 h2)

theorem AcetlS.doc (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (S : AcetlS X n0 fp0 M fp rest) : AcetlDoc X M :=
  fun _ _ h1 h2 => acetl_doc O A S.m h1 h2

end

/-! ## The calls -/

/-- `field`'s result at `sp + o`, for the member it found. -/
def AcetlFld (X : AceCtx) (M : Word → BitVec 8) (o : Nat) : Option Json → Prop
  | none => memLoad32 M (acSlot X.B o) = 0 ∧ M (acSlot X.B o + 4) = 0x21
  | some j => ∃ q l, AceVal X.D X.json q l j ∧ memLoad32 M (acSlot X.B o) = q ∧
      memLoad32 M (acSlot X.B o + 4) = BitVec.ofNat 32 l

/-- `str`'s result at `sp + 0x890`, for the string it found. -/
def AcetlStr (X : AceCtx) (M : Word → BitVec 8) : Option Bytes → Prop
  | none => memLoad32 M (acSlot X.B 0x890) = 0 ∧ M (acSlot X.B 0x890 + 4) = 0x21
  | some s => ∃ q, AcetlIn X q s ∧ memLoad32 M (acSlot X.B 0x890) = q ∧
      memLoad32 M (acSlot X.B 0x890 + 4) = BitVec.ofNat 32 s.length

theorem acetl_val {X : AceCtx} (O : X.Ok) {p : Word} {l : Nat} (b1 : X.D.toNat ≤ p.toNat)
    (b2' : p.toNat - X.D.toNat + l ≤ X.json.length) {vp vl : Nat} {j' : Json}
    (hd : JDen false (slice X.json (p.toNat - X.D.toNat) l) vp vl j') :
    AceVal X.D X.json (p + BitVec.ofNat 32 vp) vl j' ∧ (p + BitVec.ofNat 32 vp).toNat = p.toNat + vp := by
  have hlo := O.pre.docLo; have hhi := O.pre.docHi; have hb := O.lay.hi
  unfold acBufLen at hb
  have hsl := acetl_sliceLen' (d := X.json) (a := p.toNat - X.D.toNat) (b := l) (by omega)
  have h1 := hd.1; rw [hsl] at h1
  have e := acetl_addN (p := p) (a := vp) (by omega)
  have hd' := ace_den (by omega) hd
  refine ⟨⟨by omega, ?_⟩, e⟩
  rw [e, show p.toNat + vp - X.D.toNat = p.toNat - X.D.toNat + vp by omega]; exact hd'

section
variable {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- `field` on the value `j` at `p`, for the key at `kq`, with the result
at `sp + o`, inside the callees' range from `a` to `b`. -/
theorem WP.acetlField {X : AceCtx} (O : X.Ok) {hi lo p kq : Word} {l kl : Nat} {j : Json} {key : Bytes}
    {o a b : Nat} (hm : (a, b) ∈ acetlWc) (ho1 : a ≤ 0x3A50 + o) (ho2 : 0x3A50 + o + 8 ≤ b) (ho3 : o % 4 = 0)
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 jsonFieldAddress) (hev : (off + 8) % 2 = 0)
    (E : AcExtractEnv M) (hd : AcetlDoc X M) (hv : AceVal X.D X.json p l j)
    (hk : memBytes M kq kl = key) (hk1 : roWindowAddress ≤ kq.toNat) (hk2 : kq.toNat + kl ≤ roWindowAddress + roWindowSize)
    (hsp : f sp = X.B + 0x3A50) (h0 : f a0 = acSlot X.B o) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 l)
    (ha3 : f a3 = kq) (ha4 : f a4 = BitVec.ofNat 32 kl)
    (k : ∀ m2 : Machine, (∀ x, AcetlV X.B x → m2.mem x = M x) →
      (∀ x, Sep x 1 (acSlot X.B o) 8 → Sep x 1 (X.B + BitVec.ofNat 32 0x394C) 260 → m2.mem x = M x) →
      AcetlFld X m2.mem o (j.field key) →
      WP bootMainClosure0Code AC Q m2.mem (off + 8) (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  have F := O.lay.fr
  have hh := F.hi
  have hb5 := (acetlW_le _ ((by decide : ∀ r ∈ acetlWc, r ∈ acetlW) _ hm)).2
  simp only at hb5
  obtain ⟨b1, b2, b3, b4, b5⟩ := acetl_valB O hv
  have hkl : kl < 2 ^ 32 := by unfold roWindowAddress roWindowSize at hk2; omega
  refine WP.callField (tb := BitVec.ofNat 32 jsonFieldAddress) (out := acSlot X.B o)
    (s := X.B + BitVec.ofNat 32 0x394C) (p := p) (kq := kq) (n := l) (kl := kl)
    h1 h2 htgt (by decide) hev E.field h0 ha1 ha2 ha3 ha4 (by rw [hsp]; bv_omega)
    (ace_al4 F (by decide) (by decide)) (ace_al4 (c := 0x3A50 + o) F (by omega) (by omega))
    (by rw [F.at _ (by decide)]; omega) hkl (by omega) (by omega)
    (tuf_fieldSep (by rw [F.at _ (by decide)]; omega) (O.lay.ro.sub (by decide)))
    (ace_bufSep O (by decide) b1 b2)
    (tuf_sep_ro (O.lay.ro.sub (by decide)) hk1 hk2)
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + o)) 8 _ _ from ace_sepB' F (.inr (by omega)) (by omega) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + o)) 8 _ _ from ace_hs F (by omega) (by decide) (by decide))
    (ace_cs F (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + o)) 8 _ _ from ace_cs F (by omega)) fun m2 hR => ?_
  rw [hd p l b1 b2, hk] at hR
  obtain ⟨M1, hO1, hF⟩ := hR
  have hfr : ∀ x, AcetlV X.B x → m2.mem x = M x := fun x hx =>
    (hF.out x (acetl_sepV F hx (c := 0x3A50 + o) (n := 8) hm ho1 ho2)).trans
      (hO1 x (acetl_sepV F hx (a := 0x3110) (b := 0x3A50) (c := 0x394C) (n := 260) (by decide) (by decide) (by decide)))
  refine k m2 hfr (fun x h1 h2 => (hF.out x h1).trans (hO1 x h2)) ?_
  have hOF := ObjField false _ j key hv.2.2
  rcases hf : j.field key with _ | j' <;> rw [hf] at hOF
  · rw [hOF] at hF
    exact ⟨hF.2.1, hF.2.2⟩
  · obtain ⟨vp, vl, hok, hden⟩ := hOF
    rw [hok] at hF
    exact ⟨_, vl, (acetl_val O hv.1 hv.2.1 hden).1, hF.2.1, hF.2.2⟩

/-- `str` on the value `j` at `p`. -/
theorem WP.acetlStr {X : AceCtx} (O : X.Ok) {hi lo p : Word} {l : Nat} {j : Json}
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 jsonStrAddress) (hev : (off + 8) % 2 = 0)
    (E : AcExtractEnv M) (hd : AcetlDoc X M) (hv : AceVal X.D X.json p l j)
    (h0 : f a0 = acSlot X.B 0x890) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 l)
    (k : ∀ m2 : Machine, (∀ x, AcetlV X.B x → m2.mem x = M x) → AcetlStr X m2.mem j.asStr →
      WP bootMainClosure0Code AC Q m2.mem (off + 8) (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 strClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  have F := O.lay.fr
  obtain ⟨b1, b2, b3, b4, b5⟩ := acetl_valB O hv
  refine WP.callStr (tb := BitVec.ofNat 32 jsonStrAddress) (out := acSlot X.B 0x890) (p := p) (n := l)
    h1 h2 htgt (by decide) hev E.str h0 ha1 ha2 (by omega) (ace_al4 (c := 0x3A50 + 0x890) F (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x890)) 8 _ _ from ace_hs F (by decide) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x890)) 8 _ _ from ace_cs F (by decide)) fun m2 hS => ?_
  rw [hd p l b1 b2] at hS
  have hSR := StrRes false _ j p hv.2.2
  rw [hSR.1] at hS
  have hfr : ∀ x, AcetlV X.B x → m2.mem x = M x := fun x hx =>
    hS.out x (acetl_sepV F hx (a := 0x42E0) (b := 0x43E0) (c := 0x3A50 + 0x890) (n := 8) (by decide) (by decide)
      (by decide))
  refine k m2 hfr ?_
  rcases hs : j.asStr with _ | s <;> rw [hs] at hS
  · exact ⟨hS.2.1, hS.2.2⟩
  · have hstr := hSR.2 s hs
    have hsl := acetl_sliceLen' (d := X.json) (a := p.toNat - X.D.toNat) (b := l) (by omega)
    have hv2 : 2 ≤ (slice X.json (p.toNat - X.D.toNat) l).length ∧
        (slice X.json (p.toNat - X.D.toNat) l).length - 2 = s.length := by
      have h := hSR.1
      rw [hs] at h
      unfold strRes at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · next h1 _ _ =>
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at h
            exact ⟨by omega, h⟩
    have hs1 : s.length + 1 ≤ l := by omega
    have e : (p + 1).toNat = p.toNat + 1 := by
      rw [BitVec.toNat_add]; have : (1 : Word).toNat = 1 := rfl
      omega
    refine ⟨p + 1, ⟨by rw [e]; omega, by rw [e]; omega, ?_⟩, hS.2.1, hS.2.2⟩
    rw [e, show p.toNat + 1 - X.D.toNat = p.toNat - X.D.toNat + 1 by omega,
      ← tlm_slice (d := X.json) (tp := p.toNat - X.D.toNat) (tl := l) (by omega)]
    exact hstr

/-- `next_element`'s result at `sp + 0x1320` and the cursor at `sp + 0x1860`,
for the items left. -/
def AcetlElem (X : AceCtx) (M : Word → BitVec 8) : List Json → Prop
  | [] => M (acSlot X.B 0x1320) = 0 ∧ memLoad32 M (acSlot X.B 0x1320 + 4) = 0
  | j :: rest => M (acSlot X.B 0x1320) = 0 ∧ ∃ q l, AceVal X.D X.json q l j ∧
      memLoad32 M (acSlot X.B 0x1320 + 4) = q ∧ memLoad32 M (acSlot X.B 0x1320 + 8) = BitVec.ofNat 32 l ∧
      AceCur X.D X.json M (acSlot X.B 0x1860) rest

set_option maxHeartbeats 1000000 in
/-- `next_element` on the cursor at `sp + 0x1860`. -/
theorem WP.acetlNext {X : AceCtx} (O : X.Ok) {hi lo : Word} {rest : List Json}
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = RJN) (hev : (off + 8) % 2 = 0)
    (E : AcExtractEnv M) (hd : AcetlDoc X M) (hc : AceCur X.D X.json M (acSlot X.B 0x1860) rest)
    (hsp : f sp = X.B + 0x3A50) (h0 : f a0 = acSlot X.B 0x1320) (ha1 : f a1 = acSlot X.B 0x1860)
    (k : ∀ m2 : Machine, (∀ x, AcetlV X.B x → Sep x 1 (acSlot X.B 0x1868) 4 → m2.mem x = M x) →
      AcetlElem X m2.mem rest →
      WP bootMainClosure0Code AC Q m2.mem (off + 8) (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  have F := O.lay.fr
  obtain ⟨p, l, pos, c0, c4, c8, hpos, hp1, hp2, hel⟩ := hc
  have hlo := O.pre.docLo; have hhi := O.pre.docHi; have hb := O.lay.hi
  unfold acBufLen at hb
  have hro := O.lay.ro.sub (c := 0x39BC) (l := 148) (by decide)
  refine WP.callNextElement (tb := RJN) (out := acSlot X.B 0x1320) (c := acSlot X.B 0x1860)
    (s := X.B + BitVec.ofNat 32 0x39BC) (p := p) (n := l) (pos := pos) h1 h2 htgt (by decide) hev E.next E.item
    h0 ha1 (by rw [hsp]; bv_omega) (ace_al4 F (by decide) (by decide))
    (ace_al4 (c := 0x3A50 + 0x1320) F (by decide) (by decide)) (ace_al4 (c := 0x3A50 + 0x1860) F (by decide) (by decide))
    c0 c4 c8 (by omega) hpos (by omega) (by omega)
    ⟨ace_hs F (by decide) (by decide) (by decide), ace_hs F (by decide) (by decide) (by decide),
      ace_hs F (by decide) (by decide) (by decide), ace_hs F (by decide) (by decide) (by decide),
      ace_hs F (by decide) (by decide) (by decide), ace_hs F (by decide) (by decide) (by decide),
      ace_hs F (by decide) (by decide) (by decide), tuf_sep_ro hro (by decide) (by decide),
      tuf_sep_ro hro (by decide) (by decide)⟩
    (ace_hs F (by decide) (by decide) (by decide)) (ace_bufSep O (by decide) (by omega) (by omega))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from ace_sepB' F (.inr (by decide)) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1860)) 12 _ _ from ace_sepB' F (.inr (by decide)) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from ace_sepB' F (.inl (by decide)) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from ace_hs F (by decide) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1860)) 12 _ _ from ace_hs F (by decide) (by decide) (by decide))
    (ace_cs F (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from ace_cs F (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1860)) 12 _ _ from ace_cs F (by decide)) fun m2 hR => ?_
  rw [hd p l hp1 (by omega)] at hR
  obtain ⟨M1, hO1, hER⟩ := hR
  have e8 : acSlot X.B 0x1860 + 8 = acSlot X.B 0x1868 := acetl_s8
  have hfr : ∀ x, AcetlV X.B x → Sep x 1 (acSlot X.B 0x1868) 4 → m2.mem x = M x := fun x hx h8 =>
    (hER.out (x := x) (acetl_sepV F hx (a := 0x4D70) (b := 0x4D88) (c := 0x3A50 + 0x1320) (n := 12) (by decide) (by decide)
      (by decide)) (by rw [e8]; exact h8)).trans
      (hO1 x (acetl_sepV F hx (a := 0x3110) (b := 0x3A50) (c := 0x39BC) (n := 148) (by decide) (by decide) (by decide)))
  refine k m2 hfr ?_
  have hO1c : ∀ t, 0x1860 ≤ t → t + 4 ≤ 0x1868 → memLoad32 M1 (acSlot X.B t) = memLoad32 M (acSlot X.B t) :=
    fun t ht1 ht2 => ace_load_eq fun i hi => hO1 _ (by
      rw [ace_slot]; exact ace_sepB' F (.inr (by omega)) (by omega) (by decide))
  rcases rest with _ | ⟨j, rest'⟩
  · have hn : nextElement (slice X.json (p.toNat - X.D.toNat) l) pos = some none := hel
    rw [hn] at hER
    simp only [elemRes, Option.map_none, Option.map_some] at hER
    exact ⟨hER.2.1, hER.2.2⟩
  · obtain ⟨l', a, hn, hden, hel'⟩ := hel
    change nextElement (slice X.json (p.toNat - X.D.toNat) l) pos = some (some (pos, l', a)) at hn
    rw [hn] at hER
    simp only [elemRes, Option.map_none, Option.map_some] at hER
    obtain ⟨hE0, e0, e4, e8', ea⟩ := hER
    have hbd := rc_nextBd hn
    have hsl := acetl_sliceLen (d := X.json) (a := p.toNat - X.D.toNat) (b := l)
    have hk : ∀ t, 0x1860 ≤ t → t + 4 ≤ 0x1868 →
        memLoad32 m2.mem (acSlot X.B t) = memLoad32 M (acSlot X.B t) := fun t ht1 ht2 =>
      (ace_load_eq fun i hi => hE0 _
        (by rw [ace_slot]; exact ace_sepB' F (.inr (by omega)) (by omega) (by decide))
        (by rw [e8, ace_slot]; exact ace_sepB' F (.inl (by omega)) (by omega) (by decide))).trans (hO1c t ht1 ht2)
    refine ⟨e0, _, l', (acetl_val O hp1 hp2 hden).1, e4, e8', ⟨p, l, a, ?_, ?_, ea, by omega, hp1, hp2, hel'⟩⟩
    · rw [hk 0x1860 (by decide) (by decide)]; exact c0
    · rw [acetl_s4, hk 0x1864 (by decide) (by decide), ← acetl_s4]
      exact c4

end

end C3.RV32.Ac
