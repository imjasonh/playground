import C3BootProofs.Proofs.AcceptExtractHeadLib
import C3BootProofs.Proofs.TufParseMetadataHead
import C3BootProofs.Models.TufLinkMeta

/-!
# The extract stage's head, from 0xC12 to 0xD8C

The head takes the earlier expiry, parses the document, checks its
`mediaType`, zeroes the Fulcio array at `sp + 0x1ED0`, and opens a cursor
over `certificateAuthorities` at `sp + 0x1310`. Each segment below is
proved from its end back to its start.
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
    (s := X.B + BitVec.ofNat 32 0x394C) (p := p0) (kq := 0x3FCC47DC) (n := w30.toNat) (kl := 0x16)
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

end C3.RV32.Ac
