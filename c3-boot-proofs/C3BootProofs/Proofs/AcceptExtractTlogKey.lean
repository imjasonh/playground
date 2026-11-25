import C3BootProofs.Proofs.AcceptExtractTlogPass

/-! `AceTlogStage`'s pass over one transparency log: the key, from 0xEF2 to 0x1048. -/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

set_option maxRecDepth 100000

theorem acetl_spki {d : Bytes} (h12 : 12 ≤ d.length) (heq : d.take 12 = ed25519SpkiPrefix) :
    readExpect ed25519SpkiPrefix d = some (d.drop 12) := by
  have hb : (d.take 12 == ed25519SpkiPrefix) = true := by rw [heq]; rfl
  have hd : decide (12 ≤ d.length) = true := decide_eq_true h12
  unfold readExpect
  rw [show ed25519SpkiPrefix.length = 12 from rfl, hb, Bool.true_and, hd]
  rfl

/-- `ed25519_public_key_ok` accepting a key is the spec's check on it. -/
theorem acetl_pkq {M : Word → BitVec 8} (I : EdM.EdImage M) {a : Word} (h : evPk M (memBytes M a 32) = true) :
    ((memBytes M a 32).length == 32 && (Ed25519.decode (memBytes M a 32)).any (fun q => !Ed25519.smallOrder q)) =
      true := by
  obtain ⟨P, hP, -, hs, -⟩ := EdM.pk_point I (EdM.decOK C3.Models.ed25519_spec_p_prime)
    (EdM.iso_ok C3.Models.ed25519_spec_p_prime) a h
  rw [memBytes_length, hP, Option.any_some, hs]
  rfl

section
variable {X : AceCtx} {n0 : Machine} {fp0 : Word} {jr : Json} {fs : List FulcioKey} {j : Json}
  {rest : List Json} {ls : List LogKey} {M : Word → BitVec 8} {f : Fin 32 → Word}

set_option maxHeartbeats 4000000 in
/-- From 0x1002, after `decode` on `rawBytes`: the SPKI prefix, the length, and `ed25519_public_key_ok`. -/
theorem acetl_t1002 (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs (j :: rest) ls)
    (R : AceHR X f) (h26 : f 26 = reg n0 26) {d : Bytes}
    (S : AcetlS X n0 fp0 M (fp0 + BitVec.ofNat 32 d.length) rest)
    (hdl : fp0.toNat + d.length ≤ X.Bf.toNat + 0xB840)
    (h244 : memLoad32 M (acSlot X.B 0x244) = fp0) (h248 : memLoad32 M (acSlot X.B 0x248) = BitVec.ofNat 32 d.length)
    (hdm : memBytes M fp0 d.length = d)
    {key : Json} {kq : Word} {kl : Nat} (hkv : AceVal X.D X.json kq kl key)
    (h28 : memLoad32 M (acSlot X.B 0x28) = kq) (h1C : memLoad32 M (acSlot X.B 0x1C) = BitVec.ofNat 32 kl)
    {jq : Word} {jl : Nat} (hjv : AceVal X.D X.json jq jl j)
    (hent : ∀ pk, readExpect ed25519SpkiPrefix d = some pk →
      (pk.length == 32 && (Ed25519.decode pk).any (fun q => !Ed25519.smallOrder q)) = true →
      ∀ s r, (j.field (ascii!"baseUrl") >>= Json.asStr) = some s → readExpect (ascii!"https://") s = some r →
      (!((r.reverse.dropWhile (· == 0x2F)).reverse).isEmpty &&
        ((r.reverse.dropWhile (· == 0x2F)).reverse).all fun b => 0x20 ≤ b && b ≤ 0x7e) = true →
      ∀ w, (key.field (ascii!"validFor") >>= validFor) = some w →
      logEntry j = some (some ⟨(r.reverse.dropWhile (· == 0x2F)).reverse, pk, w⟩))
    (h22 : f 22 = jq) (h23 : f 23 = BitVec.ofNat 32 jl) :
    WP bootMainClosure0Code AC (acetlQ X 0xEBA (acetlNx X jr fs rest)) M 0x1002 f := by
  have F := O.lay.fr
  have hfp0 := A.fr.lo
  have hbw := O.lay.hi
  unfold acBufLen at hbw
  have hlen : d.length < 2 ^ 32 := by have := fp0.isLt; omega
  have e244 : X.B + 0x3A50 + 0x244 = acSlot X.B 0x244 := by simp only [acSlot]; bv_omega
  have e248 : X.B + 0x3A50 + 0x248 = acSlot X.B 0x248 := by simp only [acSlot]; bv_omega
  refine WP.lw ac_at_1002 (by rw [R.rsp, e244]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.branch ac_at_1006 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [R.rsp, e244, h244] at eb
    have e : fp0 = 0 := by simpa [branchTaken] using eb
    rw [e] at hfp0; have : (0 : Word).toNat = 0 := rfl
    omega
  refine WP.lw ac_at_100a (by rsimp; rw [R.rsp, e248]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.aluImm ac_at_100e ?_; wn
  refine WP.aluImm ac_at_1010 ?_; wn
  refine WP.branch ac_at_1012 (fun eb => ?_) (fun eb => ?_) <;> wn
  · exact acetl_f1A6A O A S.m (by hr) (by rsimp <;> decide)
  rsimp at eb
  rw [R.rsp, e248, h248, show aluEval .add 0 12 = BitVec.ofNat 32 12 from rfl, br_bltu hlen (by decide)] at eb
  have h12 : 12 ≤ d.length := by have := of_decide_eq_false eb; omega
  refine WP.aluImm ac_at_1016 ?_; wn
  refine WP.alu ac_at_1018 ?_; wn
  refine WP.lui ac_at_101a ?_; wn
  refine WP.aluImm ac_at_101e ?_; wn
  have E := acetl_env O A S.m
  refine WP.acetlEsl O (q1 := fp0) (q2 := (img% roWindowAddress + 0x690)) (l := 12)
    ac_at_1022 ac_at_1026 (by decide) (by decide) E (by rsimp; exact R.rsp)
    (by rsimp; rw [R.rsp, e244, h244, ev_add]; exact BitVec.zero_add _) (by rsimp <;> rfl) (by rsimp <;> rfl)
    (by decide) (acetl_bufSep O (by decide) (by omega) (by unfold acBufLen; omega))
    (tuf_sep_ro (O.lay.ro.sub (c := 0x3A4C) (l := 4) (by decide)) (by decide) (by decide)) fun m2 hr0 hfr => ?_
  have hq12 : memBytes M fp0 12 = d.take 12 := by rw [← memBytes_take M fp0 h12, hdm]
  rw [hq12, E.vPrefix] at hr0
  have S2 := S.call O hfr
  refine WP.aluImm ac_at_102a ?_; wn
  refine WP.branch ac_at_102e (fun eb => ?_) (fun eb => ?_) <;> wn
  · exact acetl_f1A6A O A S2.m (by hr) (by rsimp <;> decide)
  rsimp at eb; rw [R.rsp, e248, h248] at eb
  have hz : aluEval .add (BitVec.ofNat 32 d.length) 4294967252 = 0 := by
    have e1 : (aluEval .add (BitVec.ofNat 32 d.length) 4294967252 != 0) = false := eb
    cases h : (aluEval .add (BitVec.ofNat 32 d.length) 4294967252 == 0)
    · rw [bne, h] at e1; exact absurd e1 (by decide)
    · exact beq_iff_eq.mp h
  have h44 : d.length = 44 := by
    have := congrArg BitVec.toNat hz
    rw [ev_add, BitVec.toNat_add, BitVec.toNat_ofNat] at this
    have e : (4294967252 : Word).toNat = 4294967252 := rfl
    have e0 : (0 : Word).toNat = 0 := rfl
    rw [e, e0] at this; omega
  refine WP.alu ac_at_1032 ?_; wn
  refine WP.branch ac_at_1034 (fun eb => ?_) (fun eb => ?_) <;> wn
  · exact acetl_f1A6A O A S2.m (by hr) (by rsimp <;> decide)
  have heq : d.take 12 = ed25519SpkiPrefix := by
    rsimp at eb; rw [hr0] at eb
    split at eb
    · next h => exact h
    · exact absurd eb (by decide)
  refine WP.aluImm ac_at_1038 ?_; wn
  refine WP.alu ac_at_103a ?_; wn
  have E2 := acetl_env O A S2.m
  have es : X.B + 0x3A50 + 0xFFFFF6C0 = X.B + BitVec.ofNat 32 0x3110 := by rw [BitVec.add_assoc]; rfl
  have hsp0 : (X.B + 0x3A50).toNat = X.B.toNat + 0x3A50 := F.at _ (by decide)
  have e12 : (fp0 + 12).toNat = fp0.toNat + 12 := acetl_addN (a := 12) (by omega)
  refine WP.acetlPkOk (pk := fp0 + 12) (sp0 := X.B + 0x3A50) ac_at_103c ac_at_1040 (by decide) (by decide) E2.pk
    (by rsimp; rw [R.rsp, e244, h244, ev_add, ev_add]; exact BitVec.zero_add _) (by rsimp; exact R.rsp) (ace_al4 F (by decide) (by decide))
    (by rw [hsp0]; omega) (by rw [hsp0]; have := F.hi; omega) (by omega)
    (by rw [es]; exact (acetl_bufSep O (by decide) (by omega) (by unfold acBufLen; omega)).symm)
    (by rw [es]; exact (tuf_sep_ro (O.lay.ro.sub (c := 0x3110) (l := 0x940) (by decide)) (by decide) (by decide)).symm)
    (by rw [es]; exact (tuf_sep_ro (O.lay.ro.sub (c := 0x3110) (l := 0x940) (by decide)) (by decide) (by decide)).symm)
    (by rw [es]; exact (tuf_sep_ro (O.lay.ro.sub (c := 0x3110) (l := 0x940) (by decide)) (by decide) (by decide)).symm)
    (by rw [es]; exact (tuf_sep_ro (O.lay.ro.sub (c := 0x3110) (l := 0x940) (by decide)) (by decide) (by decide)).symm)
    (by rw [es]; exact (tuf_sep_ro (O.lay.ro.sub (c := 0x3110) (l := 0x940) (by decide)) (by decide) (by decide)).symm)
    (by rw [es]; exact (tuf_sep_ro (O.lay.ro.sub (c := 0x3110) (l := 0x940) (by decide)) (by decide) (by decide)).symm)
    (by rw [es]; exact ace_cs F (by decide)) fun m3 hr3 hO => ?_
  have hfr3 : ∀ x, AcetlV X.B x → m3.mem x = m2.mem x := fun x hx => by
    refine hO x ?_
    rw [es]
    exact acetl_sepV F hx (a := 0x3110) (b := 0x3A50) (c := 0x3110) (n := 0x940) (by decide) (by decide) (by decide)
  have hfrA : ∀ x, AcetlV X.B x → m3.mem x = M x := fun x hx => (hfr3 x hx).trans (hfr x hx)
  have S3 : AcetlS X n0 fp0 m3.mem (fp0 + 44) rest := by
    have := S2.call O hfr3; rw [h44] at this; exact this
  have hpkd : memBytes M (fp0 + 12) 32 = d.drop 12 := by
    have := memBytes_drop M fp0 (k := 12) (n := d.length) h12
    rw [hdm, h44] at this; exact this.symm
  have hpk2 : memBytes m2.mem (fp0 + 12) 32 = d.drop 12 := (acetl_pkV O hfr (by omega) (by omega)).trans hpkd
  refine WP.branch ac_at_1044 (fun eb => ?_) (fun eb => ?_) <;> wn
  · exact acetl_f1A6A O A S3.m (by hr) (by rsimp <;> decide)
  have hev : evPk m2.mem (memBytes m2.mem (fp0 + 12) 32) = true := by
    rsimp at eb; rw [hr3] at eb
    split at eb
    · next h => exact h
    · exact absurd eb (by decide)
  have hq := acetl_pkq E2.edI hev
  rw [hpk2] at hq
  refine acetl_t1048 O A I (by hr) (by rsimp; exact h26) S3 hkv
    ((acetl_ldV O hfrA (s := 0x28) (by decide) (by decide)).trans h28)
    ((acetl_ldV O hfrA (s := 0x1C) (by decide) (by decide)).trans h1C) hjv
    (fun s r hs hr ho w hw => hent _ (acetl_spki h12 heq) hq s r hs hr ho w hw)
    ((acetl_pkV O hfrA (by omega) (by omega)).trans hpkd) ?_ ?_ (by rsimp; exact h22) (by rsimp; exact h23) ?_
  · rsimp; rw [R.rsp, e248, h248]; exact hz
  · rsimp; rw [hr0]; split
    · rfl
    · next h => exact absurd heq h
  · rsimp; rw [R.rsp, e244, h244, ev_add]

end

end C3.RV32.Ac
