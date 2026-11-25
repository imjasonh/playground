import C3BootProofs.Proofs.AcceptTargetsHex
import C3BootProofs.Proofs.TufReadDoc

/-!
# `tuf::read_doc` from the `targets.json` stage

A call to `tuf::read_doc` from the closure, with the result in the frame,
the index at `sp + 0x244`, and the document buffer at `Bf + 0x4000`.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.Json

set_option maxRecDepth 200000

/-- The registers `tuf::read_doc` may change. -/
abbrev actRdClob : List (Fin 32) := [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

theorem act_rd_keep : ∀ q : Fin 32, q ∉ actRdClob → romKeep q = true := by decide

section
variable {romBase : Word} {romCode : List Nat} {B Bf g t : Word} {v : Nat → Word} {M0 : Word → BitVec 8}
  {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- A call to `tuf::read_doc(res, start, plen, idx, iw, buf)` from the
closure, with `res` at `B + c`. -/
theorem act_rd {flash : Nat → BitVec 8} {R : Nat} (hROM : RomRead flash R romBase romCode)
    (hR4 : R % 4 = 0) (hR : R ≤ 0x3A50 - 0x180)
    (X : ActX romBase romCode B Bf M0) (hI : ActI B Bf g t v M0 M f) {hi lo start plen iw : Word} {c : Nat}
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 tufReadDocAddress) (hev : (off + 8) % 2 = 0)
    (h0 : f a0 = B + BitVec.ofNat 32 c) (ha1 : f a1 = start) (ha2 : f a2 = plen) (ha3 : f a3 = acSlot B 0x244)
    (ha4 : f a4 = iw) (ha5 : f a5 = Bf + 0x4000) (hc : 0x3A50 ≤ c ∧ c + 8 ≤ 0x5A70 ∧ c % 4 = 0)
    (k : ∀ m2 : Machine,
      TrdOut flash m2.mem (B + BitVec.ofNat 32 c) (Bf + 0x4000) start plen
        (tufIndexDocSpec M (acSlot B 0x244) iw.toNat) →
      (∀ x, Sep x 1 B 0x3A50 → Sep x 1 (Bf + 0x4000) 0x2800 → Sep x 1 (B + BitVec.ofNat 32 c) 8 →
        m2.mem x = M x) →
      WP bootMainClosure0Code AC Q m2.mem (off + 8)
        (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 actRdClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  have E := X.E hI
  have hF := X.F
  have hRa : (0x3A50 - 0x180 - R) + (0x180 + R) = 0x3A50 := by omega
  obtain ⟨G, hG⟩ : ∃ G, B + BitVec.ofNat 32 (0x3A50 - 0x180 - R) = G := ⟨_, rfl⟩
  have hGl : G.toNat = B.toNat + (0x3A50 - 0x180 - R) := by rw [← hG]; exact X.lo (by omega)
  have sG : ∀ {b : Word} {k : Nat}, 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 → Sep G (0x180 + R) b k :=
    fun hb hbk => by rw [← hG]; exact X.sc (by omega) hb hbk
  have sG' : ∀ {b : Word} {k : Nat}, 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 → Sep G (0x150 + R) b k :=
    fun hb hbk => sep_front (sG hb hbk) (by omega)
  have hP : BitVec.ofNat 32 tufReadDocAddress + 0x16DA4 + 0xFFFFFEA8 = (img% flashReadAddress) := by decide
  have hsBf : Sep (Bf + 0x4000) 0x2800 G (0x180 + R) := by
    rw [← hG]; exact (X.sbf (a := 0x3A50 - 0x180 - R) (n := 0x180 + R) (c := 0x4000) (k := 0x2800)
      (by omega) (by decide)).symm
  have sGR : Sep G (0x180 + R) romBase romCode.length := by
    rw [← hG]; exact X.sRom.sub (c := 0x3A50 - 0x180 - R) (l := 0x180 + R) (by omega)
  have sGX : Sep G (0x180 + R) (acSlot B 0x244) 0x10C := by
    rw [← hG]; exact X.ss (a := 0x3A50 - 0x180 - R) (n := 0x180 + R) (b := 0x3A50 + 0x244) (k := 0x10C)
      (by omega) (by decide) (Or.inl (by omega))
  have sGS : Sep G (0x180 + R) (B + BitVec.ofNat 32 c) 8 := by
    rw [← hG]; exact X.ss (a := 0x3A50 - 0x180 - R) (n := 0x180 + R) (b := c) (k := 8)
      (by omega) (by omega) (Or.inl (by omega))
  have hbf : (Bf + 0x4000).toNat = Bf.toNat + 0x4000 := X.bfLo (c := 0x4000) (by decide)
  refine WP.callGen (cl := actRdClob) (tb := BitVec.ofNat 32 tufReadDocAddress)
    (P := fun m2 => TrdOut flash m2.mem (B + BitVec.ofNat 32 c) (Bf + 0x4000) start plen
        (tufIndexDocSpec M (acSlot B 0x244) iw.toNat) ∧
      ∀ x, Sep G (0x180 + R) x 1 → Sep (Bf + 0x4000) 0x2800 x 1 → Sep (B + BitVec.ofNat 32 c) 8 x 1 →
        m2.mem x = M x) h1 h2
    (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_) (fun m2 hP hcd => ?_)
    (fun m2 hP => k m2 hP.1 fun x h1 h2 h3 => hP.2 x
      (by rw [← hG]; exact (h1.subR (c := 0x3A50 - 0x180 - R) (l := 0x180 + R) (by omega)).symm) h2.symm h3.symm)
  · have env : FRdEnv m1.mem (BitVec.ofNat 32 tufReadDocAddress + 0x16DA4 + 0xFFFFFEA8) G (Bf + 0x4000) 0x2800 R
        romBase romCode := by
      rw [hmem1, hP]
      exact ⟨rfl, E.fr, E.frM, E.frW, by rw [hGl]; have := hF.al; omega, hR4,
        by rw [hGl]; have := hF.hi; omega, by rw [hbf]; have := X.bhi; simp; omega,
        sG' (by decide) (by decide), sG' (by decide) (by decide), sG' (by decide) (by decide),
        X.bfc (by decide) (by decide) (by decide), X.bfc (by decide) (by decide) (by decide),
        sep_front hsBf.symm (by omega) |>.symm, E.rom,
        sep_front sGR (by omega), X.sBR.sub (c := 0x4000) (l := 0x2800) (by decide)⟩
    obtain ⟨m2, c2, pc2, hk2, hout, hfr⟩ := tufReadDoc_correct hROM m1 (base := BitVec.ofNat 32 tufReadDocAddress)
      (G := G) (res := B + BitVec.ofNat 32 c) (start := start) (plen := plen) (idx := acSlot B 0x244) (iw := iw)
      (buf := Bf + 0x4000) (retAddr := AC + BitVec.ofNat 32 (off + 8))
      (by rw [hmem1]; exact E.rd) (by rw [hmem1]; exact E.rdI) (by rw [hmem1]; exact E.rdF) env (by decide) hpc1
      (by rw [hreg1]; simp +decide only [upd_app, ↓reduceIte]; exact h0)
      (by rw [hreg1]; simp +decide only [upd_app, ↓reduceIte]; exact ha1)
      (by rw [hreg1]; simp +decide only [upd_app, ↓reduceIte]; exact ha2)
      (by rw [hreg1]; simp +decide only [upd_app, ↓reduceIte]; exact ha3)
      (by rw [hreg1]; simp +decide only [upd_app, ↓reduceIte]; exact ha4)
      (by rw [hreg1]; simp +decide only [upd_app, ↓reduceIte]; exact ha5)
      (by rw [hreg1]; simp +decide only [upd_app, ↓reduceIte])
      (even_clear _ (even_at _ hb _ hev))
      (by
        rw [hreg1]; simp +decide only [upd_app, ↓reduceIte]
        rw [hI.rsp, ← hG, add_ofNat_assoc, hRa]; rfl)
      (by rw [hGl]; have := hF.hi; omega)
      (X.al (by omega) hc.2.2) (X.al (by decide) (by decide))
      (sG (by decide) (by decide)) (sG (by decide) (by decide)) (sG (by decide) (by decide))
      (sG (by decide) (by decide)) (sG (by decide) (by decide)) (sG (by decide) (by decide))
      sGR sGX hsBf.symm sGS
      (X.bfc (by decide) (by decide) (by decide)) (X.sc (by omega) (by decide) (by decide))
      (X.sbf (by omega) (by decide))
    refine ⟨m2, c2, pc2, ⟨?_, ?_⟩, fun x hx => hk2 x (act_rd_keep x hx)⟩
    · rw [hmem1] at hout; exact hout
    · intro x h1 h2 h3; rw [hfr x h1 h2 h3, hmem1]
  · refine hcd.hi (fun x hx => ?_) (by decide) (by decide)
    refine hP.2 x (sG (k := 1) hx (by have := x.isLt; omega)) ?_ ?_
    · exact X.bfc (c := 0x4000) (n := 0x2800) (k := 1) (by decide) hx (by have := x.isLt; omega)
    · exact X.sc (a := c) (n := 8) (k := 1) (by omega) hx (by have := x.isLt; omega)

end

theorem act_tid_err {M : Word → BitVec 8} {idx : Word} {i e : Nat} (h : tufIndexDocSpec M idx i = .error e) :
    e < 0x27 := by
  unfold tufIndexDocSpec at h
  split at h
  · cases h; decide
  split at h
  · cases h; decide
  unfold tidTail at h
  split at h
  · cases h; decide
  split at h
  · cases h; decide
  · cases h

/-- What `tuf::read_doc` leaves at `res` for a document `d` that `Index::doc`
locates, in the form `act_hex` reads it. -/
theorem act_trd_res {flash : Nat → BitVec 8} {M : Word → BitVec 8} {res buf start plen : Word}
    {r : Except Nat (Nat × Nat)} {d : Bytes} (hO : TrdOut flash M res buf start plen r)
    (hd : ∀ o l, r = .ok (o, l) → flashBytes flash (start.toNat + o) l = d) (he : ∀ e, r = .error e → e < 0x27) :
    (memLoad32 M res = 0 ∧ (M (res + 4)).toNat < 0x27) ∨
      (memLoad32 M res = buf ∧ memLoad32 M (res + 4) = BitVec.ofNat 32 d.length ∧ d.length ≤ 0x2800 ∧
        memBytes M buf d.length = d) := by
  have e8 : ∀ e, e < 0x27 → (BitVec.ofNat 8 e).toNat < 0x27 := fun e h => by
    rw [BitVec.toNat_ofNat]; omega
  rcases r with e | ⟨o, l⟩
  · exact Or.inl ⟨hO.1, by rw [hO.2]; exact e8 e (he e rfl)⟩
  have hdl := hd o l rfl
  simp only [TrdOut] at hO
  split at hO
  · exact Or.inl ⟨hO.1, by rw [hO.2]; decide⟩
  rcases hO with h | ⟨h1, h2, _, _, hb⟩
  · exact Or.inl ⟨h.1, by rw [h.2]; decide⟩
  have hl : d.length = l := by rw [← hdl]; simp [flashBytes]
  refine Or.inr ⟨h1, by rw [hl]; exact h2, by omega, ?_⟩
  rw [hl, ← hdl]
  unfold memBytes flashBytes
  refine List.map_congr_left fun j hj => ?_
  rw [hb j (List.mem_range.mp hj)]

end C3.RV32.Ac
