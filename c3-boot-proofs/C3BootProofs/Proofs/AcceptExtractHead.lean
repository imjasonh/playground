import C3BootProofs.Proofs.AcceptExtractHeadLib
import C3BootProofs.Proofs.TufParseMetadataHead
import C3BootProofs.Models.TufLinkMeta
import C3BootProofs.Proofs.AcceptExtractTail

/-!
# The extract stage's head, from 0xC12 to 0xD8C

The head takes the earlier expiry, parses the document, checks its
`mediaType`, zeroes the Fulcio array at `sp + 0x1ED0`, and opens a cursor
over `certificateAuthorities` at `sp + 0x1310`. Each segment below is
proved from its end back to its start, and `ace_head` proves
`AceHeadStage`.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

set_option maxRecDepth 100000

local notation "MCS" => (BitVec.ofNat 32 memcpyStubAddress : Word)

/-- At 0xD8C: the state that `AceHeadStage` gives. -/
def aceHP (X : AceCtx) (n : Machine) : Prop :=
  ∃ fp jr cas, AceAt X n 0xD8C fp ∧ AceCaInv X n fp jr cas []

theorem ace_AC : 0x40000000 ≤ AC.toNat ∧ AC.toNat + bootMainClosure0Code.length ≤ 2 ^ 32 := by decide

section
variable {B : Word} (F : Fr B 0x5A70)
include F

theorem ace_cs {c n : Nat} (h : c + n ≤ 0x5A70) : Sep (B + BitVec.ofNat 32 c) n AC bootMainClosure0Code.length :=
  F.sepHi h ace_AC.1 ace_AC.2

theorem ace_hs {c n : Nat} (h : c + n ≤ 0x5A70) {b : Word} {l : Nat} (hb : 0x40000000 ≤ b.toNat)
    (hl : b.toNat + l ≤ 2 ^ 32) : Sep (B + BitVec.ofNat 32 c) n b l :=
  F.sepHi h hb hl

theorem ace_al4 {c : Nat} (hc : c % 4 = 0) (h : c ≤ 0x5A70) : (B + BitVec.ofNat 32 c).toNat % 4 = 0 := by
  rw [F.at c h]; have := F.al; omega

theorem ace_ld2 {M M' : Word → BitVec 8} {c1 n1 c2 n2 k : Nat}
    (h : ∀ x, Sep x 1 (B + BitVec.ofNat 32 c1) n1 → Sep x 1 (B + BitVec.ofNat 32 c2) n2 → M' x = M x)
    (h1 : 0x3A50 + k + 4 ≤ c1 ∨ c1 + n1 ≤ 0x3A50 + k) (h2 : 0x3A50 + k + 4 ≤ c2 ∨ c2 + n2 ≤ 0x3A50 + k)
    (hk : 0x3A50 + k + 4 ≤ 0x5A70) (hc1 : c1 + n1 ≤ 0x5A70) (hc2 : c2 + n2 ≤ 0x5A70) :
    memLoad32 M' (acSlot B k) = memLoad32 M (acSlot B k) :=
  ace_load_eq fun j hj => by
    rw [ace_slot]
    refine h _ (ace_sepB' F ?_ (by omega) hc1) (ace_sepB' F ?_ (by omega) hc2)
    · rcases h1 with h1 | h1
      · exact .inl (by omega)
      · exact .inr (by omega)
    · rcases h2 with h2 | h2
      · exact .inl (by omega)
      · exact .inr (by omega)

end

set_option maxHeartbeats 4000000 in
/-- From 0xD38, after `elements` on `certificateAuthorities`: the cursor's
copy at `sp + 0x1310`, or the exit with `elements`' error. -/
theorem ace_d38 {X : AceCtx} (O : X.Ok) {M Mx : Word → BitVec 8} {f : Fin 32 → Word}
    (H : AceHM X M) (R : AceHR X f) {jr jc : Json} {p0 w30 vq : Word} {vl : Nat} (hroot : AceRootJ X.json jr)
    (h26 : f 26 = p0) (h30 : memLoad32 M (acSlot X.B 0x30) = w30) (hobj : AceVal X.D X.json p0 w30.toNat jr)
    (hcas : jr.field (ascii!"certificateAuthorities") = some jc) (hv : AceVal X.D X.json vq vl jc)
    (hz : ∀ i, i < 8 → memLoad32 M (acSlot X.B (0x1ED0 + 0x20 * i)) = 0)
    (hc : CurRes Mx M (acSlot X.B 0x1320) 0x21 (curOpen 91 vq (slice X.json (vq.toNat - X.D.toNat) vl))) :
    WP bootMainClosure0Code AC (aceHQ X (aceHP X)) M 0xD38 f := by
  have F := O.lay.fr
  have hh := F.hi
  have e1 : X.B + 0x3A50 + 4880 + 16 = acSlot X.B 0x1320 := by simp only [acSlot]; bv_omega
  have e2 : X.B + 0x3A50 + 4880 + 20 = acSlot X.B 0x1320 + 4 := by simp only [acSlot]; bv_omega
  refine WP.lui ac_at_d38 ?_; wn
  refine WP.aluImm ac_at_d3a ?_; wn
  refine WP.alu ac_at_d3e ?_; wn
  simp only [ev_add, show (4096 : Word) + 784 = 0x1310 by rfl, BitVec.add_comm (0x1310 : Word), R.rsp]
  refine WP.lw ac_at_d40 (by rsimp; rw [e1]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.lbu ac_at_d42 ?_; wn
  rw [e1, e2]
  rcases hco : curOpen 91 vq (slice X.json (vq.toNat - X.D.toNat) vl) with _ | ⟨q, l, k⟩ <;> rw [hco] at hc
  · obtain ⟨-, t0, t4⟩ := hc
    refine WP.branch ac_at_d46 (fun _ => ?_) (fun eb => ?_) <;> wn
    · refine ace_f1A6A O H.mem (by hr) ?_
      rsimp; rw [t4, ace_zeAnd]; decide
    · rsimp at eb; (try rw [t0] at eb); exact absurd eb (by decide)
  obtain ⟨hq, hl, hk, hn⟩ := pm_co_some hco
  obtain ⟨hD, hvl, hJV⟩ := hv
  obtain ⟨-, harr, -⟩ := CurOpen false _ jc vq hJV
  rw [hco] at harr
  obtain ⟨js, hjs⟩ : ∃ js, jc.asArr = some js := by
    cases h : jc.asArr with
    | none => rw [h] at harr; simp at harr
    | some js => exact ⟨js, rfl⟩
  have hJ := tlm_asArr hjs
  subst hJ
  have hE := Elements false _ js hJV
  have hlen : (slice X.json (vq.toNat - X.D.toNat) vl).length = vl := by
    simp only [slice, List.length_take, List.length_drop]; omega
  rw [hlen] at hl
  obtain ⟨-, t0, t4, t8⟩ := hc
  rw [hq] at t0; rw [hl] at t4; rw [hk] at t8
  have hD0 := O.pre.docLo
  refine WP.branch ac_at_d46 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; (try rw [t0] at eb)
    have e0 : vq = 0 := by simpa [branchTaken] using eb
    rw [e0] at hD; simp at hD; omega
  refine WP.lui ac_at_d4a ?_; wn
  refine WP.aluImm ac_at_d4c ?_; wn
  refine WP.alu ac_at_d50 ?_; wn
  refine WP.lui ac_at_d54 ?_; wn
  refine WP.aluImm ac_at_d56 ?_; wn
  refine WP.alu ac_at_d5a ?_; wn
  refine WP.aluImm ac_at_d5c ?_; wn
  refine WP.aluImm ac_at_d5e ?_; wn
  have E := ace_env O H.mem
  have EM : McEnv M (MCS + 8) (acSlot X.B 0x1310 + BitVec.ofNat 32 (0 + 5)) (acSlot X.B 0x1310 + BitVec.ofNat 32 (0x10 + 5))
      (X.B + BitVec.ofNat 32 0x3A40) 7 := by
    refine ⟨by rw [show MCS + 8 = BitVec.ofNat 32 memcpyBodyAddress by decide]; exact E.body, ?_, ?_, ?_, ?_, ?_,
      ace_al4 F (by decide) (by decide), by rw [F.at _ (by decide)]; omega, ?_, ?_⟩
    · rw [ace_slot]; exact ace_hs F (by decide) (by decide) (by decide)
    · exact ace_hs F (by decide) (by decide) (by decide)
    · rw [ace_slot]; exact ace_sepB' F (.inr (by decide)) (by decide) (by decide)
    · rw [ace_slot]; exact ace_sepB' F (.inr (by decide)) (by decide) (by decide)
    · rw [ace_slot, ace_slot]; exact ace_sepB' F (.inl (by decide)) (by decide) (by decide)
    · rw [ace_slot, F.at _ (by decide)]; omega
    · rw [ace_slot, F.at _ (by decide)]; omega
  refine WP.callMemcpy (tb := MCS) (N := 7) ac_at_d60 ac_at_d64 (by decide) (by decide) (by decide) E.stub EM
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp <;> rfl)
    (by rsimp; rw [R.rsp]; bv_omega)
    (ace_cs F (by decide)) (by rw [ace_slot]; exact ace_cs F (by decide)) fun m3 hO3 => ?_
  generalize m3.mem = M3 at hO3
  refine WP.aluImm ac_at_d68 ?_; wn
  refine WP.lui ac_at_d6a ?_; wn
  refine WP.aluImm ac_at_d6c ?_; wn
  refine WP.alu ac_at_d70 ?_; wn
  simp only [ev_add, R.rsp]
  have e3 : (4096 : Word) + 784 + (X.B + 0x3A50) + 0 = acSlot X.B 0x1310 + BitVec.ofNat 32 0 := by
    simp only [acSlot]; bv_omega
  refine WP.sw ac_at_d72 (by rsimp; rw [e3, ace_slot]; exact ace_al4 F (by decide) (by decide))
    (by rsimp; rw [e3, ace_slot]; exact ace_cs F (by decide)) ?_; wn
  refine WP.lui ac_at_d74 ?_; wn
  refine WP.aluImm ac_at_d76 ?_; wn
  refine WP.alu ac_at_d7a ?_; wn
  have e4 : (4096 : Word) + 784 + (X.B + 0x3A50) + 4 = acSlot X.B 0x1310 + BitVec.ofNat 32 (0 + 4) := by
    simp only [acSlot]; bv_omega
  refine WP.sb ac_at_d7e (by rsimp; rw [e4, ace_slot]; exact ace_cs F (by decide)) ?_; wn
  refine WP.lui ac_at_d82 ?_; wn
  refine WP.aluImm ac_at_d84 ?_; wn
  refine WP.alu ac_at_d88 ?_; wn
  refine WP.here fun n hpc hn hrg => ?_
  rw [e3, e4, ri_ze, t0] at hn
  have t4' : memLoad32 M (acSlot X.B 0x1310 + BitVec.ofNat 32 (0x10 + 4)) = BitVec.ofNat 32 vl := by
    rw [← t4, show acSlot X.B 0x1310 + BitVec.ofNat 32 (0x10 + 4) = acSlot X.B 0x1320 + 4 by
      simp only [acSlot]; bv_omega]
  have t8' : memLoad32 M (acSlot X.B 0x1310 + BitVec.ofNat 32 (0x10 + 8)) =
      BitVec.ofNat 32 (skipWs (slice X.json (vq.toNat - X.D.toNat) vl) 1) := by
    rw [← t8, show acSlot X.B 0x1310 + BitVec.ofNat 32 (0x10 + 8) = acSlot X.B 0x1320 + 8 by
      simp only [acSlot]; bv_omega]
  have e5 : acSlot X.B 0x1320 + 4 = acSlot X.B 0x1310 + BitVec.ofNat 32 (0x10 + 4) := by
    simp only [acSlot]; bv_omega
  rw [e5] at hn
  obtain ⟨⟨c0, c4, c8⟩, hfa⟩ := pm_ccopy (F := acSlot X.B 0x1310) (d := 0) (a := 0x10) (by decide)
    (by rw [ace_slot]; exact ace_sepB' F (.inr (by decide)) (by decide) (by decide)) t4' t8' hO3 hn.symm
  rw [ace_slot] at hfa
  have hM5 : ∀ x, AceL X.B x → n.mem x = M x := fun x hx =>
    hfa x (hx.s1310 F (by decide) (by decide)) (hx.frame F (by decide) (by decide))
  have H5 := H.mono F hM5
  have rg : ∀ q : Fin 32, reg n q = _ := hrg
  have hbf := O.lay.hi
  have hfp : (X.Bf + 0x6800).toNat = X.Bf.toNat + 0x6800 := by
    rw [BitVec.toNat_add]; unfold acBufLen at hbf
    have : (0x6800 : Word).toNat = 0x6800 := rfl
    omega
  refine ⟨ace_inv O H5.mem rfl (by rw [hrg]; rsimp; exact R.rsp) (by rw [hrg]; rsimp; exact R.rgp)
    (by rw [hrg]; rsimp; exact R.rtp), .inr ⟨hpc, X.Bf + 0x6800, jr, js, ⟨ace_code O H5.mem, ⟨hpc, rfl, fun _ => rfl⟩,
      ace_inv O H5.mem rfl (by rw [hrg]; rsimp; exact R.rsp) (by rw [hrg]; rsimp; exact R.rgp)
        (by rw [hrg]; rsimp; exact R.rtp), ⟨H5.fp, ?_, by omega, by omega⟩, ⟨ace_kept O H5.mem, ?_⟩, H5.exp⟩,
      ⟨hroot, ?_, ⟨[], by rw [hcas]; rfl, rfl⟩, ?_, ?_, ?_, by rw [hrg]; rsimp, by rw [hrg]; rsimp; exact R.r19,
        ?_, by rw [hrg]; rsimp⟩⟩⟩
  · rw [H5.fl, hfp, show X.Bf.toNat + 0xB840 - (X.Bf.toNat + 0x6800) = 0x5040 by omega]; rfl
  · intro q hq
    have : q = 21 ∨ q = 25 ∨ q = 27 := by revert hq; revert q; decide
    rcases this with rfl | rfl | rfl <;> rw [hrg] <;> rsimp
    · exact R.r21
    · exact R.r25
    · exact R.r27
  · unfold AceObj
    rw [hrg]; rsimp
    rw [h26, ace_ld2 F hfa (.inl (by decide)) (.inr (by decide)) (by decide) (by decide) (by decide), h30]
    exact hobj
  · have hsk := skipWs_le (slice X.json (vq.toNat - X.D.toNat) vl) 1
    have hjl := O.pre.docHi
    rw [hlen] at hsk
    rw [add_ofNat_zero] at c0 c4 c8
    exact ⟨vq, vl, _, c0, c4, c8, by omega, hD, hvl, hE⟩
  · refine ⟨Nat.zero_le _, fun i h => absurd h (Nat.not_lt_zero _), fun i _ hi => ?_⟩
    rw [add_ofNat_assoc, show 0x3A50 + 0x1ED0 + 0x20 * i = 0x3A50 + (0x1ED0 + 0x20 * i) by omega]
    show memLoad32 n.mem (acSlot X.B (0x1ED0 + 0x20 * i)) = 0
    rw [ace_ld2 F hfa (.inr (by omega)) (.inr (by omega)) (by omega) (by decide) (by decide)]
    exact hz i hi
  · rw [hrg]; rsimp; simp only [ev_add, R.rsp, acSlot]; bv_omega
  · rw [hrg]; rsimp; simp only [ev_add, R.rsp, acSlot]; bv_omega

/-- A span of the document is apart from the stack frame. -/
theorem ace_bufSep {X : AceCtx} (O : X.Ok) {c k : Nat} (hc : c + k ≤ 0x5A70) {p : Word} {n : Nat}
    (h1 : X.D.toNat ≤ p.toNat) (h2 : p.toNat + n ≤ X.D.toNat + X.json.length) :
    Sep (X.B + BitVec.ofNat 32 c) k p n := by
  have hlo := O.pre.docLo; have hhi := O.pre.docHi; have hb := O.lay.hi
  have e : p = X.Bf + BitVec.ofNat 32 (p.toNat - X.Bf.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := p.isLt; omega
  rw [e]; exact (O.lay.sep.sub hc).subR (by unfold acBufLen at *; omega)

/-- A span of the document in memory that agrees with the head's. -/
theorem ace_docBytes {X : AceCtx} (O : X.Ok) {M : Word → BitVec 8} (H : AceHM X M) {p : Word} {n : Nat}
    (h1 : X.D.toNat ≤ p.toNat) (h2 : p.toNat + n ≤ X.D.toNat + X.json.length) :
    memBytes M p n = slice X.json (p.toNat - X.D.toNat) n := by
  have hhi := O.pre.docHi; have hb := O.lay.hi
  have e : p = X.D + BitVec.ofNat 32 (p.toNat - X.D.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := p.isLt; omega
  have h := tuf_memBytes_drop_take (M := M) (p := X.D) (n := X.json.length) (h := p.toNat - X.D.toNat) (l := n)
    (by omega)
  rw [ace_doc O H.mem, ← e] at h
  exact h.symm

theorem ace_den {d : Bytes} {tp tl a b : Nat} {j : Json} (ht : tp + tl ≤ d.length)
    (h : JDen false (slice d tp tl) a b j) : JDen false d (tp + a) b j := by
  obtain ⟨h1, h2⟩ := h
  have hl : (slice d tp tl).length ≤ tl := by unfold slice; simp only [List.length_take]; omega
  refine ⟨by omega, ?_⟩
  rw [← tlm_slice (d := d) (tp := tp) (tl := tl) (by omega)]; exact h2

set_option maxHeartbeats 4000000 in
/-- From 0xD04: `field` for `certificateAuthorities`, then `elements` on it. -/
theorem ace_d04 {X : AceCtx} (O : X.Ok) {M : Word → BitVec 8} {f : Fin 32 → Word}
    (H : AceHM X M) (R : AceHR X f) {jr : Json} {p0 w30 : Word} (hroot : AceRootJ X.json jr)
    (h26 : f 26 = p0) (h30 : memLoad32 M (acSlot X.B 0x30) = w30) (hobj : AceVal X.D X.json p0 w30.toNat jr)
    (hz : ∀ i, i < 8 → memLoad32 M (acSlot X.B (0x1ED0 + 0x20 * i)) = 0) :
    WP bootMainClosure0Code AC (aceHQ X (aceHP X)) M 0xD04 f := by
  have F := O.lay.fr
  have hh := F.hi
  have E := ace_env O H.mem
  have hobj' := hobj
  obtain ⟨hD, hn, hJV⟩ := hobj'
  have hjl := O.pre.docHi
  have hD0 := O.pre.docLo
  have hbh := O.lay.hi
  unfold acBufLen at hbh
  have e30 : X.B + 0x3A50 + 0x30 = acSlot X.B 0x30 := by simp only [acSlot]; bv_omega
  refine WP.lui ac_at_d04 ?_; wn
  refine WP.aluImm ac_at_d08 ?_; wn
  refine WP.aluImm ac_at_d0c ?_; wn
  refine WP.aluImm ac_at_d0e ?_; wn
  refine WP.alu ac_at_d10 ?_; wn
  refine WP.lw ac_at_d12 (by rsimp; rw [R.rsp, e30]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.callField (tb := BitVec.ofNat 32 jsonFieldAddress) (out := acSlot X.B 0x350)
    (s := X.B + BitVec.ofNat 32 0x394C) (p := p0) (kq := (img% acCasKeyAddress)) (n := w30.toNat) (kl := 0x16)
    ac_at_d14 ac_at_d18 (by decide) (by decide) (by decide) E.field
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; simp only [ev_add]; exact (BitVec.zero_add _).trans h26)
    (by rsimp; rw [R.rsp, e30, h30]; simp)
    (by rsimp <;> rfl)
    (by rsimp <;> rfl)
    (by rsimp; rw [R.rsp]; bv_omega)
    (ace_al4 F (by decide) (by decide)) (ace_al4 (c := 0x3A50 + 0x350) F (by decide) (by decide))
    (by rw [F.at _ (by decide)]; omega) (by decide) (by omega) (by omega)
    (tuf_fieldSep (by rw [F.at _ (by decide)]; omega) (O.lay.ro.sub (by decide)))
    (ace_bufSep O (by decide) hD (by omega))
    (tuf_sep_ro (O.lay.ro.sub (by decide)) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x350)) 8 _ _ from ace_sepB' F (.inr (by decide)) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x350)) 8 _ _ from ace_hs F (by decide) (by decide) (by decide))
    (ace_cs F (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x350)) 8 _ _ from ace_cs F (by decide)) fun m2 hR => ?_
  rw [ace_docBytes O H hD (by omega), E.kCas] at hR
  generalize m2.mem = M2 at hR
  have hOF := ObjField false _ jr (ascii!"certificateAuthorities") hJV
  obtain ⟨M1, hO1, hF⟩ := hR
  have hM2 : ∀ x, AceL X.B x → M2 x = M x := fun x hx =>
    (hF.out x (hx.s350 F (by decide) (by decide))).trans (hO1 x (hx.frame F (by decide) (by decide)))
  have H2 := H.mono F hM2
  have e350 : X.B + 0x3A50 + 0x350 = acSlot X.B 0x350 := by simp only [acSlot]; bv_omega
  have e354 : X.B + 0x3A50 + 0x354 = acSlot X.B 0x350 + 4 := by simp only [acSlot]; bv_omega
  have e354a : X.B + 0x3A50 + 0x354 = X.B + BitVec.ofNat 32 0x3DA4 := by bv_omega
  rcases hf : jr.field (ascii!"certificateAuthorities") with _ | jc <;> rw [hf] at hOF
  · rw [hOF] at hF
    obtain ⟨-, t0, t4⟩ := hF
    refine WP.lw ac_at_d1c (by rsimp; rw [R.rsp, e350]; exact ace_al4 (c := 0x3A50 + 0x350) F (by decide) (by decide)) ?_
    wn
    refine WP.branch ac_at_d20 (fun _ => ?_) (fun eb => ?_) <;> wn
    · refine ace_f1A66 O H2.mem (by hr) ?_
      rw [e354, t4]; decide
    · rsimp at eb; rw [R.rsp, e350, t0] at eb; exact absurd eb (by decide)
  obtain ⟨vp, vl, hok, hden⟩ := hOF
  rw [hok] at hF
  have hden' := ace_den hn hden
  have hvb := hden'.1
  have hsl : (slice X.json (p0.toNat - X.D.toNat) w30.toNat).length = w30.toNat := by
    simp only [slice, List.length_take, List.length_drop]; omega
  have hvl : vp + vl ≤ w30.toNat := hsl ▸ hden.1
  have hq : (p0 + BitVec.ofNat 32 vp).toNat = p0.toNat + vp := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨hF0, t0, t4⟩ := hF
  refine WP.lw ac_at_d1c (by rsimp; rw [R.rsp, e350]; exact ace_al4 (c := 0x3A50 + 0x350) F (by decide) (by decide)) ?_
  wn
  refine WP.branch ac_at_d20 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [R.rsp, e350, t0] at eb
    have e0 : p0 + BitVec.ofNat 32 vp = 0 := by simpa [branchTaken] using eb
    rw [e0] at hq; simp at hq; omega
  refine WP.lw ac_at_d24 (by rsimp; rw [R.rsp, e354a]; exact ace_al4 F (by decide) (by decide)) ?_
  wn
  refine WP.lui ac_at_d28 ?_; wn
  refine WP.aluImm ac_at_d2a ?_; wn
  refine WP.alu ac_at_d2e ?_; wn
  have hq1 : X.D.toNat ≤ (p0 + BitVec.ofNat 32 vp).toNat := by omega
  have hq2 : (p0 + BitVec.ofNat 32 vp).toNat + vl ≤ X.D.toNat + X.json.length := by omega
  have E2 := ace_env O H2.mem
  refine WP.callElements (tb := RJE) (out := acSlot X.B 0x1320) (s := X.B + BitVec.ofNat 32 0x3A40)
    (p := p0 + BitVec.ofNat 32 vp) (n := vl) ac_at_d30 ac_at_d34 (by decide) (by decide) (by decide) E2.elems
    (by rw [show RJE + 0xFFFFFAB2 = RSW by decide]; exact E2.skipWs)
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; rw [R.rsp, e350, t0])
    (by rsimp; rw [R.rsp, e354, t4])
    (by rsimp; rw [R.rsp]; bv_omega)
    (by omega) (ace_al4 F (by decide) (by decide)) (ace_al4 (c := 0x3A50 + 0x1320) F (by decide) (by decide))
    (ace_hs F (by decide) (by decide) (by decide)) (ace_hs F (by decide) (by decide) (by decide))
    (ace_bufSep O (by decide) hq1 hq2)
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from ace_sepB' F (.inr (by decide)) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from ace_hs F (by decide) (by decide) (by decide))
    (ace_cs F (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from ace_cs F (by decide)) fun m3 hC => ?_
  rw [ace_docBytes O H2 hq1 hq2] at hC
  generalize m3.mem = M3 at hC
  obtain ⟨M1', hO', hc⟩ := hC
  have hM3 : ∀ x, AceL X.B x → M3 x = M2 x := fun x hx =>
    (hc.out x (hx.s1310 F (by decide) (by decide))).trans (hO' x (hx.frame F (by decide) (by decide)))
  have H3 := H2.mono F hM3
  have hf2 : ∀ x, Sep x 1 (X.B + BitVec.ofNat 32 (0x3A50 + 0x350)) 8 → Sep x 1 (X.B + BitVec.ofNat 32 0x394C) 260 →
      M2 x = M x := fun x h1 h2 => (hF0 x h1).trans (hO1 x h2)
  have hf3 : ∀ x, Sep x 1 (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 → Sep x 1 (X.B + BitVec.ofNat 32 0x3A40) 16 →
      M3 x = M2 x := fun x h1 h2 => (hc.out x h1).trans (hO' x h2)
  refine ace_d38 O H3 (by hr) hroot (by rsimp; exact h26) ?_ hobj hf
    ⟨hq1, by rw [hq, show p0.toNat + vp - X.D.toNat = p0.toNat - X.D.toNat + vp by omega]; exact hden'⟩ ?_ hc
  · rw [ace_ld2 F hf3 (.inl (by decide)) (.inr (by decide)) (by decide) (by decide) (by decide),
      ace_ld2 F hf2 (.inl (by decide)) (.inr (by decide)) (by decide) (by decide) (by decide), h30]
  · intro i hi
    rw [ace_ld2 F hf3 (.inr (by omega)) (.inr (by omega)) (by omega) (by decide) (by decide),
      ace_ld2 F hf2 (.inr (by omega)) (.inr (by omega)) (by omega) (by decide) (by decide)]
    exact hz i hi

set_option maxHeartbeats 4000000 in
/-- The loop at 0xCF8 that zeroes the Fulcio array, with `m` entries left. -/
theorem ace_zl {X : AceCtx} (O : X.Ok) {jr : Json} {p0 w30 : Word} (hroot : AceRootJ X.json jr)
    (hobj : AceVal X.D X.json p0 w30.toNat jr) :
    ∀ m, m ≤ 8 → 0 < m → ∀ (M : Word → BitVec 8) (f : Fin 32 → Word), AceHM X M → AceHR X f → f 26 = p0 →
      memLoad32 M (acSlot X.B 0x30) = w30 → f 10 = acSlot X.B (0x1ED0 + 0x20 * (8 - m)) →
      f 11 = BitVec.ofNat 32 m → (∀ i, i < 8 - m → memLoad32 M (acSlot X.B (0x1ED0 + 0x20 * i)) = 0) →
      WP bootMainClosure0Code AC (aceHQ X (aceHP X)) M 0xCF8 f := by
  have F := O.lay.fr
  have hh := F.hi
  intro m
  induction m with
  | zero => intro _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ m ih =>
    intro hm _ M f H R h26 h30 h10 h11 hz
    have ea : acSlot X.B (0x1ED0 + 0x20 * (8 - (m + 1))) + 0 = X.B + BitVec.ofNat 32 (0x5920 + 0x20 * (7 - m)) := by
      unfold acSlot; rw [show (0 : Word) = BitVec.ofNat 32 0 from rfl, add_ofNat_assoc]; congr 2; omega
    refine WP.sw ac_at_cf8 (by rw [h10, ea]; exact ace_al4 F (by omega) (by omega))
      (by rw [h10, ea]; exact ace_cs F (by omega)) ?_
    wn
    rw [h10, ea]
    have hx0 : f x0 = 0 := R.rz
    rw [hx0]
    have ha : f a0 = acSlot X.B (0x1ED0 + 0x20 * (8 - (m + 1))) := h10
    have hb : f a1 = BitVec.ofNat 32 (m + 1) := h11
    have hS : ∀ x, AceL X.B x → memStore32 M (X.B + BitVec.ofNat 32 (0x5920 + 0x20 * (7 - m))) 0 x = M x :=
      fun x hx => memStore32_get_sep (hx.s1ED0 F (by omega) (by omega)).symm
    have H' := H.mono F hS
    have h30' : memLoad32 (memStore32 M (X.B + BitVec.ofNat 32 (0x5920 + 0x20 * (7 - m))) 0) (acSlot X.B 0x30) = w30 := by
      rw [memLoad32_store32_sep (ace_sepB' F (.inr (by omega)) (by omega) (by decide)), h30]
    have hz' : ∀ i, i < 8 - m → memLoad32 (memStore32 M (X.B + BitVec.ofNat 32 (0x5920 + 0x20 * (7 - m))) 0)
        (acSlot X.B (0x1ED0 + 0x20 * i)) = 0 := by
      intro i hi
      rcases Nat.lt_or_ge i (8 - (m + 1)) with hl | hl
      · rw [show acSlot X.B (0x1ED0 + 0x20 * i) = X.B + BitVec.ofNat 32 (0x3A50 + (0x1ED0 + 0x20 * i)) from rfl,
          memLoad32_store32_sep (ace_sepB' F (.inr (by omega)) (by omega) (by omega))]
        exact hz i hl
      · rw [show acSlot X.B (0x1ED0 + 0x20 * i) = X.B + BitVec.ofNat 32 (0x5920 + 0x20 * (7 - m)) by
          unfold acSlot; congr 2; omega, memLoad32_store32_same]
    refine WP.aluImm ac_at_cfc ?_; wn
    refine WP.aluImm ac_at_d00 ?_; wn
    have r11 : aluEval .add (f a1) 4294967295 = BitVec.ofNat 32 m := by
      rw [hb, ev_add]; apply BitVec.eq_of_toNat_eq
      have : (4294967295 : Word).toNat = 4294967295 := rfl
      rw [BitVec.toNat_add, this, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    refine WP.branch ac_at_d02 (fun eb => ?_) (fun eb => ?_) <;> wn
    · rcases Nat.eq_zero_or_pos m with h0 | h0
      · exfalso; rsimp at eb; rw [r11, h0] at eb; simp [branchTaken] at eb
      refine ih (by omega) h0 _ _ H' (by hr) (by rsimp; exact h26) h30' ?_ (by rsimp; exact r11) hz'
      rsimp; rw [ha, ev_add, show (32 : Word) = BitVec.ofNat 32 32 from rfl]; unfold acSlot
      rw [add_ofNat_assoc, show 0x3A50 + (0x1ED0 + 0x20 * (8 - (m + 1))) + 32 = 0x3A50 + (0x1ED0 + 0x20 * (8 - m)) by
        omega]
    · rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        exact ace_d04 O H' (by hr) hroot (by rsimp; exact h26) h30' hobj hz'
      · exfalso; rsimp at eb; rw [r11] at eb
        have : BitVec.ofNat 32 m ≠ 0 := by
          intro e; have h := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat] at h
          have : (0 : Word).toNat = 0 := rfl
          omega
        simp [branchTaken] at eb
        exact this eb

set_option maxHeartbeats 4000000 in
/-- From 0xCEC, after the `mediaType` check. -/
theorem ace_cec {X : AceCtx} (O : X.Ok) {M : Word → BitVec 8} {f : Fin 32 → Word}
    (H : AceHM X M) (R : AceHR X f) {jr : Json} {p0 w30 : Word} (hroot : AceRootJ X.json jr)
    (h26 : f 26 = p0) (h30 : memLoad32 M (acSlot X.B 0x30) = w30) (hobj : AceVal X.D X.json p0 w30.toNat jr) :
    WP bootMainClosure0Code AC (aceHQ X (aceHP X)) M 0xCEC f := by
  refine WP.lui ac_at_cec ?_; wn
  refine WP.aluImm ac_at_cee ?_; wn
  refine WP.alu ac_at_cf2 ?_; wn
  refine WP.aluImm ac_at_cf4 ?_; wn
  refine WP.branch ac_at_cf6 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb
  refine ace_zl O hroot hobj 8 (by decide) (by decide) M _ H (by hr) (by rsimp; exact h26) h30 ?_ (by rsimp <;> rfl)
    (fun i hi => absurd hi (Nat.not_lt_zero _))
  rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega

set_option maxHeartbeats 4000000 in
/-- From 0xC6E, after `parse`: the `mediaType` field, `str`, and the
comparison with the expected media type. -/
theorem ace_c6e {X : AceCtx} (O : X.Ok) {M Mx : Word → BitVec 8} {f : Fin 32 → Word}
    (H : AceHM X M) (R : AceHR X f) (h22 : f 22 = acSlot X.B 0x1310)
    (hP : FieldRes Mx M (acSlot X.B 0x1320) (fieldRes X.D (parseModel false X.json))) :
    WP bootMainClosure0Code AC (aceHQ X (aceHP X)) M 0xC6E f := by
  have F := O.lay.fr
  have hh := F.hi
  have hjl := O.pre.docHi
  have hD0 := O.pre.docLo
  have hbh := O.lay.hi
  unfold acBufLen at hbh
  have e1320 : acSlot X.B 0x1310 + 0x10 = acSlot X.B 0x1320 := by simp only [acSlot]; bv_omega
  have e1324 : acSlot X.B 0x1310 + 0x14 = acSlot X.B 0x1320 + 4 := by simp only [acSlot]; bv_omega
  have e1324a : acSlot X.B 0x1320 + 4 = X.B + BitVec.ofNat 32 0x4D74 := by simp only [acSlot]; bv_omega
  refine WP.lw ac_at_c6e (by rw [h22, e1320]; exact ace_al4 (c := 0x3A50 + 0x1320) F (by decide) (by decide)) ?_; wn
  rcases hpm : parseModel false X.json with e | ⟨a, l⟩ <;> rw [hpm] at hP
  · change FieldRes Mx M _ (.error e) at hP
    obtain ⟨-, t0, t4⟩ := hP
    have he := ace_parseModel false X.json e hpm
    refine WP.branch ac_at_c72 (fun _ => ?_) (fun eb => ?_) <;> wn
    · refine WP.lbu ac_at_ce4 ?_; wn
      refine WP.jal ac_at_ce8 (by decide) ?_; wn
      refine ace_f1A6A O H.mem (by hr) ?_
      rsimp; rw [h22, e1324, t4, ace_zeAnd, BitVec.toNat_ofNat]; omega
    · rsimp at eb; rw [h22, e1320, t0] at eb; exact absurd eb (by decide)
  change FieldRes Mx M _ (.ok (X.D + BitVec.ofNat 32 a, l)) at hP
  obtain ⟨-, t0, t4⟩ := hP
  obtain ⟨jr, hpj, hden⟩ := ParseModelOk false X.json a l hpm
  have hal := hden.1
  have hq : (X.D + BitVec.ofNat 32 a).toNat = X.D.toNat + a := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine WP.branch ac_at_c72 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [h22, e1320, t0] at eb
    have e0 : X.D + BitVec.ofNat 32 a = 0 := by simpa [branchTaken] using eb
    rw [e0] at hq; simp at hq; omega
  have E := ace_env O H.mem
  have e30 : X.B + 0x3A50 + 0x30 = acSlot X.B 0x30 := by simp only [acSlot]; bv_omega
  have ex8 : (4096 : Word) + 784 + (X.B + 0x3A50) = acSlot X.B 0x1310 := by simp only [acSlot]; bv_omega
  refine WP.lui ac_at_c76 ?_; wn
  refine WP.aluImm ac_at_c78 ?_; wn
  refine WP.alu ac_at_c7c ?_; wn
  simp only [ev_add, R.rsp]
  rw [show X.B + 0x3A50 + (4096 + 784) = acSlot X.B 0x1310 by simp only [acSlot]; bv_omega, h22, e1320, t0]
  refine WP.lw ac_at_c80 (by rsimp; rw [e1324, e1324a]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_c82 ?_; wn
  refine WP.aluImm ac_at_c86 ?_; wn
  refine WP.lui ac_at_c8a ?_; wn
  refine WP.aluImm ac_at_c8c ?_; wn
  refine WP.alu ac_at_c90 ?_; wn
  refine WP.aluImm ac_at_c92 ?_; wn
  refine WP.alu ac_at_c94 ?_; wn
  refine WP.sw ac_at_c96 (by rsimp; rw [R.rsp, e30]; exact ace_al4 F (by decide) (by decide))
    (by rsimp; rw [R.rsp, e30]; exact ace_cs F (by decide)) ?_; wn
  rw [R.rsp, e30, e1324, t4]
  have hS1 : ∀ x, AceL X.B x → memStore32 M (acSlot X.B 0x30) (BitVec.ofNat 32 l) x = M x :=
    fun x hx => memStore32_get_sep (hx.s30 F (by decide) (by decide)).symm
  have H1 := H.mono F hS1
  have E1 := ace_env O H1.mem
  have hl32 : (BitVec.ofNat 32 l).toNat = l := by rw [BitVec.toNat_ofNat]; omega
  have hpD : (X.D + BitVec.ofNat 32 a).toNat - X.D.toNat = a := by omega
  refine WP.callField (tb := BitVec.ofNat 32 jsonFieldAddress) (out := acSlot X.B 0x1320)
    (s := X.B + BitVec.ofNat 32 0x394C) (p := X.D + BitVec.ofNat 32 a) (kq := (img% acMediaTypeKeyAddress)) (n := l) (kl := 9)
    ac_at_c98 ac_at_c9c (by decide) (by decide) (by decide) E1.field
    (by rsimp; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; simp only [ev_add]; exact BitVec.zero_add _)
    (by rsimp)
    (by rsimp <;> rfl)
    (by rsimp <;> rfl)
    (by rsimp; rw [R.rsp]; bv_omega)
    (ace_al4 F (by decide) (by decide)) (ace_al4 (c := 0x3A50 + 0x1320) F (by decide) (by decide))
    (by rw [F.at _ (by decide)]; omega) (by decide) (by omega) (by omega)
    (tuf_fieldSep (by rw [F.at _ (by decide)]; omega) (O.lay.ro.sub (by decide)))
    (ace_bufSep O (by decide) (by omega) (by omega))
    (tuf_sep_ro (O.lay.ro.sub (by decide)) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 8 _ _ from ace_sepB' F (.inr (by decide)) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 8 _ _ from ace_hs F (by decide) (by decide) (by decide))
    (ace_cs F (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 8 _ _ from ace_cs F (by decide)) fun m2 hR => ?_
  rw [ace_docBytes O H1 (by omega) (by omega), E1.kMedia, hpD] at hR
  generalize m2.mem = M2 at hR
  have hOF := ObjField false _ jr (ascii!"mediaType") hden.2
  obtain ⟨M1, hO1, hF⟩ := hR
  have hM2 : ∀ x, AceL X.B x → M2 x = memStore32 M (acSlot X.B 0x30) (BitVec.ofNat 32 l) x := fun x hx =>
    (hF.out x (hx.s1310 F (by decide) (by decide))).trans (hO1 x (hx.frame F (by decide) (by decide)))
  have H2 := H1.mono F hM2
  refine WP.lui ac_at_ca0 ?_; wn
  refine WP.aluImm ac_at_ca2 ?_; wn
  refine WP.alu ac_at_ca6 ?_; wn
  refine WP.lw ac_at_ca8 (by rsimp; rw [e1320]; exact ace_al4 (c := 0x3A50 + 0x1320) F (by decide) (by decide)) ?_; wn
  rcases hf : jr.field (ascii!"mediaType") with _ | jm <;> rw [hf] at hOF
  · rw [hOF] at hF
    obtain ⟨-, t0', t4'⟩ := hF
    refine WP.branch ac_at_caa (fun _ => ?_) (fun eb => ?_) <;> wn
    · refine WP.lbu ac_at_140a ?_; wn
      refine WP.jal ac_at_140e (by decide) ?_; wn
      refine ace_f1A6A O H2.mem (by hr) ?_
      rsimp
      rw [show aluEval .add (aluEval .add 4096 784) (f sp) + 20 = acSlot X.B 0x1320 + 4 by
        simp only [ev_add, R.rsp, acSlot]; bv_omega, t4']
      decide
    · rsimp at eb; rw [e1320, t0'] at eb; exact absurd eb (by decide)
  obtain ⟨vp, vl, hok, hden2⟩ := hOF
  rw [hok] at hF
  change FieldRes M1 M2 _ (.ok (X.D + BitVec.ofNat 32 a + BitVec.ofNat 32 vp, vl)) at hF
  obtain ⟨hF0, t0', t4'⟩ := hF
  have hden2' := ace_den hal hden2
  have hvb := hden2'.1
  have hsl : (slice X.json a l).length = l := by simp only [slice, List.length_take, List.length_drop]; omega
  have hvl : vp + vl ≤ l := hsl ▸ hden2.1
  have hq2 : (X.D + BitVec.ofNat 32 a + BitVec.ofNat 32 vp).toNat = X.D.toNat + a + vp := by
    rw [BitVec.toNat_add, hq, BitVec.toNat_ofNat]; omega
  have ea0 : aluEval .add (aluEval .add 4096 784) (f sp) = acSlot X.B 0x1310 := by
    simp only [ev_add, R.rsp, acSlot]; bv_omega
  refine WP.branch ac_at_caa (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [e1320, t0'] at eb
    have e0 : X.D + BitVec.ofNat 32 a + BitVec.ofNat 32 vp = 0 := by simpa [branchTaken] using eb
    rw [e0] at hq2; simp at hq2; omega
  refine WP.lw ac_at_cae (by rsimp; rw [ea0, e1324, e1324a]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.aluImm ac_at_cb0 ?_; wn
  rw [ea0, e1324, t4']
  have E2 := ace_env O H2.mem
  refine WP.callStr (tb := BitVec.ofNat 32 jsonStrAddress) (out := acSlot X.B 0x350)
    (p := X.D + BitVec.ofNat 32 a + BitVec.ofNat 32 vp) (n := vl) ac_at_cb2 ac_at_cb6 (by decide) (by decide)
    (by decide) E2.str (by rsimp; simp only [ev_add, R.rsp, acSlot]; bv_omega) (by rsimp; rw [e1320, t0'])
    (by rsimp) (by omega) (ace_al4 (c := 0x3A50 + 0x350) F (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x350)) 8 _ _ from ace_hs F (by decide) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x350)) 8 _ _ from ace_cs F (by decide)) fun m3 hS => ?_
  have hpD2 : (X.D + BitVec.ofNat 32 a + BitVec.ofNat 32 vp).toNat - X.D.toNat = a + vp := by omega
  rw [ace_docBytes O H2 (by omega) (by omega), hpD2, ← tlm_slice (d := X.json) (tp := a) (tl := l) hvl] at hS
  have hSR := StrRes false _ jm (X.D + BitVec.ofNat 32 a + BitVec.ofNat 32 vp) hden2.2
  rw [hSR.1] at hS
  generalize m3.mem = M3 at hS
  have e350 : X.B + 0x3A50 + 0x350 = acSlot X.B 0x350 := by simp only [acSlot]; bv_omega
  have e354 : X.B + 0x3A50 + 0x354 = acSlot X.B 0x350 + 4 := by simp only [acSlot]; bv_omega
  have e354a : X.B + 0x3A50 + 0x354 = X.B + BitVec.ofNat 32 0x3DA4 := by bv_omega
  rcases hs : jm.asStr with _ | str <;> rw [hs] at hS
  · change SliceRes M2 M3 _ 0x21 none at hS
    obtain ⟨hS0, u0, u4⟩ := hS
    have H3 := H2.mono F fun x hx => hS0 x (hx.s350 F (by decide) (by decide))
    refine WP.lw ac_at_cba (by rsimp; rw [R.rsp, e350]; exact ace_al4 (c := 0x3A50 + 0x350) F (by decide) (by decide)) ?_
    wn
    refine WP.branch ac_at_cbe (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact ace_f1A66 O H3.mem (by hr) (by rw [e354, u4]; decide)
    · rsimp at eb; rw [R.rsp, e350, u0] at eb; exact absurd eb (by decide)
  change SliceRes M2 M3 _ 0x21 (some (X.D + BitVec.ofNat 32 a + BitVec.ofNat 32 vp + 1, str.length)) at hS
  obtain ⟨hS0, u0, u4⟩ := hS
  have H3 := H2.mono F fun x hx => hS0 x (hx.s350 F (by decide) (by decide))
  have hstr := hSR.2 str hs
  have hsl2 : str.length ≤ vl - 1 := by
    have h := congrArg List.length hstr
    simp only [slice, List.length_take, List.length_drop] at h
    omega
  have hq3 : (X.D + BitVec.ofNat 32 a + BitVec.ofNat 32 vp + 1).toNat = X.D.toNat + a + vp + 1 := by
    rw [BitVec.toNat_add, hq2]; have : (1 : Word).toNat = 1 := rfl
    omega
  refine WP.lw ac_at_cba (by rsimp; rw [R.rsp, e350]; exact ace_al4 (c := 0x3A50 + 0x350) F (by decide) (by decide)) ?_
  wn
  refine WP.branch ac_at_cbe (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [R.rsp, e350, u0] at eb
    have e0 : X.D + BitVec.ofNat 32 a + BitVec.ofNat 32 vp + 1 = 0 := by simpa [branchTaken] using eb
    have h0 : (0 : Word).toNat = 0 := rfl
    rw [e0, h0] at hq3; omega
  refine WP.lw ac_at_cc2 (by rsimp; rw [R.rsp, e354a]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_cc6 ?_; wn
  refine WP.aluImm ac_at_cca ?_; wn
  refine WP.aluImm ac_at_cce ?_; wn
  have E3 := ace_env O H3.mem
  have hv2 : 2 ≤ vl := by
    have h := hSR.1
    rw [hs] at h
    rcases Nat.lt_or_ge (slice (slice X.json a l) vp vl).length 2 with h2 | h2
    · exfalso; unfold strRes at h
      split at h
      · cases h
      · rename_i hc; exact hc h2
    · simp only [slice, List.length_take] at h2; omega
  have hb1 : X.D.toNat ≤ (X.D + BitVec.ofNat 32 a + BitVec.ofNat 32 vp + 1).toNat := by omega
  have hb2 : (X.D + BitVec.ofNat 32 a + BitVec.ofNat 32 vp + 1).toNat + str.length ≤ X.D.toNat + X.json.length := by
    omega
  have esp : X.B + 0x3A50 + 0xFFFFFFEC = X.B + BitVec.ofNat 32 0x3A3C := by bv_omega
  refine WP.callSliceNe (tb := RSN) (p := X.D + BitVec.ofNat 32 a + BitVec.ofNat 32 vp + 1)
    (q := (img% acMediaTypeAddress)) (pl := str.length) (ql := 0x39) ac_at_cd2 ac_at_cd6 (by decide) (by decide) (by decide)
    E3.sliceNe (by rw [show RSN + 0xFFFFF372 = RSE by decide]; exact E3.sliceEq)
    (by rw [show RSN + 0xFFFFDF1C = RES by decide]; exact E3.equal)
    (by rw [show RSN + 0xB2DA = RMC by decide]; exact E3.memcmp)
    (by rsimp; rw [R.rsp, e350, u0]) (by rsimp; rw [R.rsp, e354, u4]) (by rsimp <;> rfl) (by rsimp <;> rfl)
    (by omega) (by decide)
    (by rsimp; rw [R.rsp, show X.B + 0x3A50 = X.B + BitVec.ofNat 32 0x3A50 from rfl]; exact ace_al4 F (by decide) (by decide))
    (by rsimp; rw [R.rsp, esp]; exact ace_hs F (by decide) (by decide) (by decide))
    (by rsimp; rw [R.rsp, esp]; exact ace_hs F (by decide) (by decide) (by decide))
    (by rsimp; rw [R.rsp, esp]; exact ace_hs F (by decide) (by decide) (by decide))
    (by rsimp; rw [R.rsp, esp]; exact ace_hs F (by decide) (by decide) (by decide))
    (by rsimp; rw [R.rsp, esp]; exact ace_bufSep O (by decide) hb1 hb2)
    (by rsimp; rw [R.rsp, esp]; exact tuf_sep_ro (O.lay.ro.sub (by decide)) (by decide) (by decide))
    (by rsimp; rw [R.rsp, esp]; exact ace_cs F (by decide)) fun m4 hr4 hO4 => ?_
  rsimp at hO4; rw [R.rsp, esp] at hO4
  have hb3 : (X.D + BitVec.ofNat 32 a + BitVec.ofNat 32 vp + 1).toNat - X.D.toNat = a + vp + 1 := by omega
  rw [ace_docBytes O H3 hb1 hb2, hb3, E3.vMedia,
    show a + vp + 1 = a + (vp + 1) by omega, ← tlm_slice (d := X.json) (tp := a) (tl := l) (by omega),
    ← tlm_slice (d := slice X.json a l) (tp := vp) (tl := vl) (by omega), hstr] at hr4
  generalize m4.mem = M4 at hO4
  have H4 := H3.mono F fun x hx => hO4 x (hx.frame F (by decide) (by decide))
  have hf3 : ∀ x, Sep x 1 (X.B + BitVec.ofNat 32 0x3A3C) 0x14 → Sep x 1 (X.B + BitVec.ofNat 32 0x3A3C) 0x14 →
      M4 x = M3 x := fun x h _ => hO4 x h
  have hf2 : ∀ x, Sep x 1 (X.B + BitVec.ofNat 32 (0x3A50 + 0x350)) 8 → Sep x 1 (X.B + BitVec.ofNat 32 (0x3A50 + 0x350)) 8 →
      M3 x = M2 x := fun x h _ => hS0 x h
  have hf1 : ∀ x, Sep x 1 (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 8 → Sep x 1 (X.B + BitVec.ofNat 32 0x394C) 260 →
      M2 x = memStore32 M (acSlot X.B 0x30) (BitVec.ofNat 32 l) x := fun x h1 h2 => (hF0 x h1).trans (hO1 x h2)
  have h30 : memLoad32 M4 (acSlot X.B 0x30) = BitVec.ofNat 32 l := by
    rw [ace_ld2 F hf3 (.inr (by decide)) (.inr (by decide)) (by decide) (by decide) (by decide),
      ace_ld2 F hf2 (.inl (by decide)) (.inl (by decide)) (by decide) (by decide) (by decide),
      ace_ld2 F hf1 (.inl (by decide)) (.inr (by decide)) (by decide) (by decide) (by decide),
      memLoad32_store32_same]
  rcases decEq str aceMediaType with hne | heq
  · refine WP.branch ac_at_cda (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; rsimp at eb; rw [hr4] at eb; simp only [hne, ↓reduceIte] at eb; exact absurd eb (by decide)
    refine WP.aluImm ac_at_cdc ?_; wn
    refine WP.jal ac_at_ce0 (by decide) ?_; wn
    exact ace_f1A6A O H4.mem (by hr) (by rsimp <;> decide)
  · refine WP.branch ac_at_cda (fun _ => ?_) (fun eb => ?_) <;> wn
    · refine ace_cec (p0 := X.D + BitVec.ofNat 32 a) (w30 := BitVec.ofNat 32 l) O H4 (by hr) ⟨hpj, ?_⟩ (by rsimp) h30 ⟨by omega, by rw [hl32, hpD]; exact hden⟩
      rw [hf]; exact hs.trans (by rw [heq])
    · exfalso; rsimp at eb; rw [hr4] at eb; simp only [heq, ↓reduceIte] at eb; exact absurd eb (by decide)



set_option maxHeartbeats 4000000 in
/-- After the stores at 0xC50 and 0xC54: the memory the head keeps from 0xC58. -/
theorem ace_hm0 {X : AceCtx} (O : X.Ok) {M : Word → BitVec 8}
    (hM : ∀ x, Sep x 1 (X.B + BitVec.ofNat 32 0x3A70) 8 → M x = X.K.mem x)
    (hexp : aceU64 M (acSlot X.B 0x20) = min (aceU64 X.K.mem (acSlot X.B 0x20)) (aceU64 X.K.mem (acSlot X.B 0x28))) :
    AceHM X (memStore32 (memStore32 M (acSlot X.B 0x1FDC) (memLoad32 M (acSlot X.B 0x30))) (acSlot X.B 0x1FE0) 0x5040) := by
  have F := O.lay.fr
  have hh := F.hi
  have hS : ∀ x, x.toNat < X.B.toNat + 0x5A2C ∨ X.B.toNat + 0x5A34 ≤ x.toNat →
      memStore32 (memStore32 M (acSlot X.B 0x1FDC) (memLoad32 M (acSlot X.B 0x30))) (acSlot X.B 0x1FE0) 0x5040 x = M x := by
    intro x h
    have h1 : Sep x 1 (acSlot X.B 0x1FE0) 4 := ace_sepX F (by decide) (by rcases h with h | h; exact .inl (by omega); exact .inr (by omega))
    have h2 : Sep x 1 (acSlot X.B 0x1FDC) 4 := ace_sepX F (by decide) (by rcases h with h | h; exact .inl (by omega); exact .inr (by omega))
    rw [memStore32_get_sep h1.symm, memStore32_get_sep h2.symm]
  have hs1 : Sep (acSlot X.B 0x1FE0) 4 (acSlot X.B 0x1FDC) 4 :=
    (sep_of_le (by rw [ace_slotN F (by decide), ace_slotN F (by decide)]; omega)
      (by rw [ace_slotN F (by decide)]; omega)).symm
  refine ⟨fun x hx => (hS x hx.2.2).trans (hM x (hx.s20 F (by decide) (by decide))), ?_, ?_, ?_⟩
  · rw [← hexp]
    unfold aceU64
    rw [show acSlot X.B 0x20 + 4 = acSlot X.B 0x24 by unfold acSlot; rw [BitVec.add_assoc]; rfl]
    rw [ace_load_eq fun j hj => hS _ (.inl (by rw [ace_slotAdd F (by omega)]; omega)),
      ace_load_eq fun j hj => hS _ (.inl (by rw [ace_slotAdd F (by omega)]; omega))]
  · rw [memLoad32_store32_sep hs1, memLoad32_store32_same, ← O.pre.keys]
    exact ace_load_eq fun j hj => hM _ (ace_sepX F (by decide) (.inr (by rw [ace_slotAdd F (by omega)]; omega)))
  · exact memLoad32_store32_same _ _ _

set_option maxHeartbeats 4000000 in
/-- From 0xC32, with the earlier expiry stored: the length check, `keys`'s
slice, and `parse`. -/
theorem ace_c32 {X : AceCtx} (O : X.Ok) {M : Word → BitVec 8} {f : Fin 32 → Word}
    (hM : ∀ x, Sep x 1 (X.B + BitVec.ofNat 32 0x3A70) 8 → M x = X.K.mem x)
    (hexp : aceU64 M (acSlot X.B 0x20) = min (aceU64 X.K.mem (acSlot X.B 0x20)) (aceU64 X.K.mem (acSlot X.B 0x28)))
    (R : AceHR X f) (h18 : f 18 = X.D) (h22 : f 22 = acSlot X.B 0x1310)
    (h24 : f 24 = BitVec.ofNat 32 X.json.length) :
    WP bootMainClosure0Code AC (aceHQ X (aceHP X)) M 0xC32 f := by
  have F := O.lay.fr
  have hjl := O.pre.docHi
  have hD0 := O.pre.docLo
  have hbh := O.lay.hi
  have hh := F.hi
  unfold acBufLen at hbh
  have hU : ∀ x, AceU X.B x → M x = X.K.mem x := fun x hx => hM x (hx.s20 F (by decide) (by decide))
  refine WP.aluImm ac_at_c32 ?_; wn
  refine WP.aluImm ac_at_c34 ?_; wn
  refine WP.branch ac_at_c36 (fun eb => ?_) (fun eb => ?_) <;> wn
  · have hl : X.json.length ≤ 0x2800 := by
      rsimp at eb; rw [R.rz, h24] at eb
      have e : aluEval AluOp.sll (aluEval AluOp.add 0 5) 11 = (0x2800 : Word) := by decide
      rw [e] at eb
      simp only [branchTaken, BitVec.ult, Bool.not_eq_true', decide_eq_false_iff_not, BitVec.toNat_ofNat] at eb
      omega
    refine WP.lui ac_at_c40 ?_; wn
    refine WP.aluImm ac_at_c42 ?_; wn
    refine WP.lui ac_at_c46 ?_; wn
    refine WP.aluImm ac_at_c48 ?_; wn
    refine WP.alu ac_at_c4c ?_; wn
    have e30 : X.B + 0x3A50 + 0x30 = acSlot X.B 0x30 := by simp only [acSlot]; bv_omega
    have eA : (8192 : Word) + 4294966704 + (X.B + 0x3A50) + 556 = acSlot X.B 0x1FDC := by
      simp only [acSlot]; bv_omega
    have eB : (8192 : Word) + 4294966704 + (X.B + 0x3A50) + 560 = acSlot X.B 0x1FE0 := by
      simp only [acSlot]; bv_omega
    refine WP.lw ac_at_c4e (by rsimp; rw [R.rsp, e30]; exact ace_al4 F (by decide) (by decide)) ?_; wn
    refine WP.sw ac_at_c50 (by rsimp; simp only [ev_add, R.rsp]; rw [eA]; exact ace_al4 F (by decide) (by decide))
      (by rsimp; simp only [ev_add, R.rsp]; rw [eA]; exact ace_cs F (by decide)) ?_; wn
    refine WP.sw ac_at_c54 (by rsimp; simp only [ev_add, R.rsp]; rw [eB]; exact ace_al4 F (by decide) (by decide))
      (by rsimp; simp only [ev_add, R.rsp]; rw [eB]; exact ace_cs F (by decide)) ?_; wn
    simp only [ev_add, R.rsp]
    rw [eA, eB, e30, show (20480 : Word) + 64 = 0x5040 from rfl]
    have H := ace_hm0 O hM hexp
    generalize memStore32 _ _ _ = M' at H ⊢
    refine WP.lui ac_at_c58 ?_; wn
    refine WP.aluImm ac_at_c5a ?_; wn
    refine WP.alu ac_at_c5e ?_; wn
    refine WP.alu ac_at_c60 ?_; wn
    refine WP.alu ac_at_c62 ?_; wn
    refine WP.aluImm ac_at_c64 ?_; wn
    have E := ace_env O H.mem
    refine WP.callParse (tb := BitVec.ofNat 32 jsonParseAddress) (out := acSlot X.B 0x1320)
      (s := X.B + BitVec.ofNat 32 0x38BC) (p := X.D) (n := X.json.length) (c := false)
      ac_at_c66 ac_at_c6a (by decide) (by decide) (by decide) E.parse
      (by rsimp; simp only [ev_add, R.rsp, acSlot]; bv_omega)
      (by rsimp; simp only [ev_add]; rw [h18]; exact BitVec.zero_add _)
      (by rsimp; simp only [ev_add]; rw [h24]; exact BitVec.zero_add _)
      (by rsimp <;> rfl)
      (by rsimp; rw [R.rsp]; bv_omega)
      (ace_al4 F (by decide) (by decide)) (ace_al4 (c := 0x3A50 + 0x1320) F (by decide) (by decide))
      (by rw [F.at _ (by decide)]; omega) (by omega) (by omega) (by omega)
      (tpm_parseSep (by rw [F.at _ (by decide)]; omega) (O.lay.ro.sub (by decide)))
      (ace_bufSep O (by decide) (Nat.le_refl _) (by omega))
      (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 8 _ _ from ace_sepB' F (.inr (by decide)) (by decide) (by decide))
      (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 8 _ _ from ace_hs F (by decide) (by decide) (by decide))
      (ace_cs F (by decide))
      (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 8 _ _ from ace_cs F (by decide)) fun m2 hR => ?_
    rw [ace_doc O H.mem] at hR
    generalize m2.mem = M2 at hR
    obtain ⟨M1, hO1, hF⟩ := hR
    have hM2 : ∀ x, AceL X.B x → M2 x = M' x := fun x hx =>
      (hF.out x (hx.s1310 F (by decide) (by decide))).trans (hO1 x (hx.frame F (by decide) (by decide)))
    exact ace_c6e O (H.mono F hM2) (by hr) (by rsimp; exact h22) hF
  · refine WP.aluImm ac_at_c3a ?_; wn
    refine WP.jal ac_at_c3c (by decide) ?_; wn
    exact ace_f1A6A O hU (by hr) (by rsimp)

set_option maxHeartbeats 4000000 in
/-- From 0xC24, with the words to compare in `a0` and `a1`: the earlier
expiry. -/
theorem ace_c24 {X : AceCtx} (O : X.Ok) {f : Fin 32 → Word} {x y : Word}
    (hxy : x.toNat < y.toNat ↔ aceU64 X.K.mem (acSlot X.B 0x20) < aceU64 X.K.mem (acSlot X.B 0x28))
    (R : AceHR X f) (h18 : f 18 = X.D) (h22 : f 22 = acSlot X.B 0x1310)
    (h24 : f 24 = BitVec.ofNat 32 X.json.length) (ha0 : f 10 = x) (ha1 : f 11 = y) :
    WP bootMainClosure0Code AC (aceHQ X (aceHP X)) X.K.mem 0xC24 f := by
  have F := O.lay.fr
  have hh := F.hi
  refine WP.alu ac_at_c24 ?_; wn
  refine WP.branch ac_at_c28 (fun eb => ?_) (fun eb => ?_) <;> wn
  · rsimp at eb
    rw [ha0, ha1] at eb
    rcases Nat.lt_or_ge x.toNat y.toNat with h | h
    · refine ace_c32 O (fun _ _ => rfl) (Nat.min_eq_left (Nat.le_of_lt (hxy.mp h))).symm (by hr)
        (by rsimp; exact h18) (by rsimp; exact h22) (by rsimp; exact h24)
    · rw [show aluEval .sltu x y = 0 by unfold aluEval BitVec.ult; rw [decide_eq_false (Nat.not_lt.mpr h)]; rfl] at eb
      exact absurd eb (by decide)
  · rsimp at eb
    rw [ha0, ha1] at eb
    rcases Nat.lt_or_ge x.toNat y.toNat with h | h
    · rw [show aluEval .sltu x y = 1 by unfold aluEval BitVec.ult; rw [decide_eq_true h]; rfl] at eb
      exact absurd eb (by decide)
    have hle : aceU64 X.K.mem (acSlot X.B 0x28) ≤ aceU64 X.K.mem (acSlot X.B 0x20) :=
      Nat.not_lt.mp fun h' => Nat.not_lt.mpr h (hxy.mpr h')
    have e20 : X.B + 0x3A50 + 0x20 = acSlot X.B 0x20 := by simp only [acSlot]; bv_omega
    have e24 : X.B + 0x3A50 + 0x24 = acSlot X.B 0x24 := by simp only [acSlot]; bv_omega
    have e28 : X.B + 0x3A50 + 0x28 = acSlot X.B 0x28 := by simp only [acSlot]; bv_omega
    have e2C : X.B + 0x3A50 + 0x2C = acSlot X.B 0x2C := by simp only [acSlot]; bv_omega
    refine WP.lw ac_at_c2a (by rsimp; rw [R.rsp, e2C]; exact ace_al4 F (by decide) (by decide)) ?_; wn
    refine WP.sw ac_at_c2c (by rsimp; rw [R.rsp, e24]; exact ace_al4 F (by decide) (by decide))
      (by rsimp; rw [R.rsp, e24]; exact ace_cs F (by decide)) ?_; wn
    refine WP.lw ac_at_c2e (by rsimp; rw [R.rsp, e28]; exact ace_al4 F (by decide) (by decide)) ?_; wn
    refine WP.sw ac_at_c30 (by rsimp; rw [R.rsp, e20]; exact ace_al4 F (by decide) (by decide))
      (by rsimp; rw [R.rsp, e20]; exact ace_cs F (by decide)) ?_; wn
    rw [R.rsp, e20, e24, e28, e2C]
    have s2024 : Sep (acSlot X.B 0x20) 4 (acSlot X.B 0x24) 4 :=
      show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x20)) 4 (X.B + BitVec.ofNat 32 (0x3A50 + 0x24)) 4 from
        ace_sepB' F (.inl (by decide)) (by decide) (by decide)
    have s2428 : Sep (acSlot X.B 0x24) 4 (acSlot X.B 0x28) 4 :=
      show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x24)) 4 (X.B + BitVec.ofNat 32 (0x3A50 + 0x28)) 4 from
        ace_sepB' F (.inl (by decide)) (by decide) (by decide)
    refine ace_c32 O (fun z hz => ?_) ?_ (by hr) (by rsimp; exact h18) (by rsimp; exact h22) (by rsimp; exact h24)
    · have h' := ace_ofSep hz
      rw [F.at _ (by decide)] at h'
      rw [memStore32_get_sep (ace_sepX F (c := 0x3A50 + 0x20) (n := 4) (by decide)
          (by rcases h' with h' | h'; exact .inl (by omega); exact .inr (by omega))).symm,
        memStore32_get_sep (ace_sepX F (c := 0x3A50 + 0x24) (n := 4) (by decide)
          (by rcases h' with h' | h'; exact .inl (by omega); exact .inr (by omega))).symm]
    · rw [Nat.min_eq_right hle]
      unfold aceU64
      rw [show acSlot X.B 0x20 + 4 = acSlot X.B 0x24 by unfold acSlot; rw [BitVec.add_assoc]; rfl,
        show acSlot X.B 0x28 + 4 = acSlot X.B 0x2C by unfold acSlot; rw [BitVec.add_assoc]; rfl,
        memLoad32_store32_same, memLoad32_store32_sep s2024, memLoad32_store32_same,
        memLoad32_store32_sep s2428]

set_option maxHeartbeats 4000000 in
/-- From 0xC12 to 0xD8C. -/
theorem ace_c12 {X : AceCtx} (O : X.Ok) :
    WP bootMainClosure0Code AC (aceHQ X (aceHP X)) X.K.mem 0xC12 (reg X.K) := by
  have F := O.lay.fr
  have R : AceHR X (reg X.K) := ⟨rfl, O.inv.sp, O.inv.gp, O.inv.tp, O.pre.r19, rfl, rfl, rfl⟩
  have e20 : X.B + 0x3A50 + 0x20 = acSlot X.B 0x20 := by simp only [acSlot]; bv_omega
  have e24 : X.B + 0x3A50 + 0x24 = acSlot X.B 0x24 := by simp only [acSlot]; bv_omega
  have e28 : X.B + 0x3A50 + 0x28 = acSlot X.B 0x28 := by simp only [acSlot]; bv_omega
  have e2C : X.B + 0x3A50 + 0x2C = acSlot X.B 0x2C := by simp only [acSlot]; bv_omega
  have u20 : aceU64 X.K.mem (acSlot X.B 0x20) =
      (memLoad32 X.K.mem (acSlot X.B 0x20)).toNat + 2 ^ 32 * (memLoad32 X.K.mem (acSlot X.B 0x24)).toNat := by
    unfold aceU64; rw [show acSlot X.B 0x20 + 4 = acSlot X.B 0x24 by unfold acSlot; rw [BitVec.add_assoc]; rfl]
  have u28 : aceU64 X.K.mem (acSlot X.B 0x28) =
      (memLoad32 X.K.mem (acSlot X.B 0x28)).toNat + 2 ^ 32 * (memLoad32 X.K.mem (acSlot X.B 0x2C)).toNat := by
    unfold aceU64; rw [show acSlot X.B 0x28 + 4 = acSlot X.B 0x2C by unfold acSlot; rw [BitVec.add_assoc]; rfl]
  have b20 := (memLoad32 X.K.mem (acSlot X.B 0x20)).isLt
  have b28 := (memLoad32 X.K.mem (acSlot X.B 0x28)).isLt
  refine WP.lw ac_at_c12 (by rw [R.rsp, e24]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.lw ac_at_c14 (by rsimp; rw [R.rsp, e2C]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.branch ac_at_c16 (fun eb => ?_) (fun eb => ?_) <;> wn
  · rsimp at eb
    rw [R.rsp, e24, e2C] at eb
    have he := congrArg BitVec.toNat (eq_of_beq eb)
    refine WP.lw ac_at_c20 (by rsimp; rw [R.rsp, e20]; exact ace_al4 F (by decide) (by decide)) ?_; wn
    refine WP.lw ac_at_c22 (by rsimp; rw [R.rsp, e28]; exact ace_al4 F (by decide) (by decide)) ?_; wn
    refine ace_c24 O ?_ (by hr) (by rsimp; exact O.pre.r18) (by rsimp; exact O.pre.r22)
      (by rsimp; exact O.pre.r24) (by rsimp; rw [R.rsp, e20]) (by rsimp; rw [R.rsp, e28])
    rw [u20, u28, he]
    exact ⟨fun h => by omega, fun h => by omega⟩
  · rsimp at eb
    rw [R.rsp, e24, e2C] at eb
    have hne : (memLoad32 X.K.mem (acSlot X.B 0x24)).toNat ≠ (memLoad32 X.K.mem (acSlot X.B 0x2C)).toNat :=
      fun e => Bool.false_ne_true (eb.symm.trans (decide_eq_true (BitVec.eq_of_toNat_eq e)))
    refine WP.lw ac_at_c1a (by rsimp; rw [R.rsp, e24]; exact ace_al4 F (by decide) (by decide)) ?_; wn
    refine WP.lw ac_at_c1c (by rsimp; rw [R.rsp, e2C]; exact ace_al4 F (by decide) (by decide)) ?_; wn
    refine WP.jal ac_at_c1e (by decide) ?_; wn
    refine ace_c24 O ?_ (by hr) (by rsimp; exact O.pre.r18) (by rsimp; exact O.pre.r22)
      (by rsimp; exact O.pre.r24) (by rsimp; rw [R.rsp, e24]) (by rsimp; rw [R.rsp, e2C])
    rw [u20, u28]
    rcases Nat.lt_or_ge (memLoad32 X.K.mem (acSlot X.B 0x24)).toNat (memLoad32 X.K.mem (acSlot X.B 0x2C)).toNat with h | h
    · exact ⟨fun _ => by omega, fun _ => h⟩
    · have h' := Nat.lt_of_le_of_ne h (Ne.symm hne)
      exact ⟨fun h2 => absurd h2 (Nat.not_lt.mpr h), fun h2 => absurd h2 (by omega)⟩

/-- The head, from 0xC12 to 0xD8C. -/
theorem ace_head : AceHeadStage := fun _ O => ace_stage O (ace_c12 O)

/-- **The extract stage**, from the sub-stages of its loops at 0xD8C, 0xEBA,
0x123A, and 0x1434. -/
theorem ac_extract_loops (hC : AceCaStage) (hT : AceTlogStage) (hS : AceTsaStage) (hD : AceDupStage) :
    AcExtractStage :=
  ac_extract ace_head hC hT hS hD ace_tail

end C3.RV32.Ac
