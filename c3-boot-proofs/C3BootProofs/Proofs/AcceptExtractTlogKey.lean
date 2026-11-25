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

/-! ## `decode`'s frame -/

/-- `x` lies outside what the callees write, the slice at `sp + 0x1FDC`, and
`keys`'s free part from `fp`: what a call to `decode` keeps. -/
def AcetlD (X : AceCtx) (fp x : Word) : Prop :=
  AcetlV X.B x ∧ (x.toNat < X.B.toNat + 0x5A2C ∨ X.B.toNat + 0x5A34 ≤ x.toNat) ∧
    (x.toNat < fp.toNat ∨ X.Bf.toNat + 0xB840 ≤ x.toNat)

theorem acetl_UD {X : AceCtx} {fp x : Word} (h : AcetlU X.B X.Bf fp true x) : AcetlD X fp x :=
  ⟨acetl_UV h, (h.2 rfl).2, (h.2 rfl).1⟩

theorem acetl_D_at {X : AceCtx} (O : X.Ok) {fp : Word} (hfp : X.Bf.toNat + 0x6800 ≤ fp.toNat)
    {s l j : Nat} (hs : 0x3A50 + s + l ≤ 0x5A70)
    (hr : acetlWc.all (fun r => decide (0x3A50 + s + l ≤ r.1) || decide (r.2 ≤ 0x3A50 + s)) = true)
    (hd : (decide (0x3A50 + s + l ≤ 0x5A2C) || decide (0x5A34 ≤ 0x3A50 + s)) = true) (hj : j < l) :
    AcetlD X fp (acSlot X.B s + BitVec.ofNat 32 j) := by
  have F := O.lay.fr
  have hx := ace_slotAdd F (k := s) (j := j) (by omega)
  have hbuf : Sep (acSlot X.B s + BitVec.ofNat 32 j) 1 X.Bf acBufLen := by
    rw [ace_slot]; exact O.lay.sep.sub (c := 0x3A50 + s + j) (l := 1) (by omega)
  have hb := ace_ofSep hbuf
  have hbw := O.lay.hi
  unfold acBufLen at hb hbw
  refine ⟨acetl_V_at O hs hr hj, ?_, ?_⟩
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at hd
    rcases hd with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  · rcases hb with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)

theorem acetl_ldD {X : AceCtx} (O : X.Ok) {fp : Word} {M M' : Word → BitVec 8} (hm : ∀ x, AcetlD X fp x → M x = M' x)
    (hfp : X.Bf.toNat + 0x6800 ≤ fp.toNat) {s : Nat} (hs : 0x3A50 + s + 4 ≤ 0x5A70)
    (hr : acetlWc.all (fun r => decide (0x3A50 + s + 4 ≤ r.1) || decide (r.2 ≤ 0x3A50 + s)) = true)
    (hd : (decide (0x3A50 + s + 4 ≤ 0x5A2C) || decide (0x5A34 ≤ 0x3A50 + s)) = true) :
    memLoad32 M (acSlot X.B s) = memLoad32 M' (acSlot X.B s) :=
  ace_load_eq fun _ hj => hm _ (acetl_D_at O hfp hs hr hd hj)

theorem acetl_trdec {x : Option Bytes} {fl : Nat} {d : Bytes} (h : trDecodeRes x fl = some d) :
    x = some d ∧ d.length ≤ fl := by
  cases x with
  | none => cases h
  | some b =>
    unfold trDecodeRes at h
    rw [Option.bind_some] at h
    split at h
    · next hl => cases h; exact ⟨rfl, hl⟩
    · cases h

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

set_option maxHeartbeats 4000000 in
/-- From 0xF9E: `field` for `rawBytes` on the key, `str`, and `decode`. -/
theorem acetl_tF9E (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs (j :: rest) ls)
    (R : AceHR X f) (h26 : f 26 = reg n0 26) (S : AcetlS X n0 fp0 M fp0 rest)
    {key : Json} {kq : Word} {kl : Nat} (hkv : AceVal X.D X.json kq kl key)
    (h28 : memLoad32 M (acSlot X.B 0x28) = kq) (h1C : memLoad32 M (acSlot X.B 0x1C) = BitVec.ofNat 32 kl)
    {jq : Word} {jl : Nat} (hjv : AceVal X.D X.json jq jl j)
    (hent : ∀ pk, (key.field (ascii!"rawBytes") >>= Json.asStr >>= base64Decode >>= readExpect ed25519SpkiPrefix) =
        some pk →
      (pk.length == 32 && (Ed25519.decode pk).any (fun q => !Ed25519.smallOrder q)) = true →
      ∀ s r, (j.field (ascii!"baseUrl") >>= Json.asStr) = some s → readExpect (ascii!"https://") s = some r →
      (!((r.reverse.dropWhile (· == 0x2F)).reverse).isEmpty &&
        ((r.reverse.dropWhile (· == 0x2F)).reverse).all fun b => 0x20 ≤ b && b ≤ 0x7e) = true →
      ∀ w, (key.field (ascii!"validFor") >>= validFor) = some w →
      logEntry j = some (some ⟨(r.reverse.dropWhile (· == 0x2F)).reverse, pk, w⟩))
    (h22 : f 22 = jq) (h23 : f 23 = BitVec.ofNat 32 jl) :
    WP bootMainClosure0Code AC (acetlQ X 0xEBA (acetlNx X jr fs rest)) M 0xF9E f := by
  have F := O.lay.fr
  have hh := F.hi
  have hfp0 := A.fr.lo
  have hbw := O.lay.hi
  unfold acBufLen at hbw
  have hd := S.doc O A
  have E := acetl_env O A S.m
  have e28 : X.B + 0x3A50 + 0x28 = acSlot X.B 0x28 := by simp only [acSlot]; bv_omega
  have e1C : X.B + 0x3A50 + 0x1C = acSlot X.B 0x1C := by simp only [acSlot]; bv_omega
  refine WP.lui ac_at_f9e ?_; wn
  refine WP.aluImm ac_at_fa0 ?_; wn
  refine WP.alu ac_at_fa4 ?_; wn
  refine WP.aluImm ac_at_fa6 ?_; wn
  refine WP.lw ac_at_fa8 (by rsimp; rw [R.rsp, e28]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.lw ac_at_faa (by rsimp; rw [R.rsp, e1C]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_fac ?_; wn
  refine WP.aluImm ac_at_fb0 ?_; wn
  refine WP.acetlField O (o := 0x1320) (a := 0x4D70) (b := 0x4D88) (kq := (img% roWindowAddress + 0x730)) (kl := 8)
    (by decide) (by decide) (by decide) (by decide) ac_at_fb4 ac_at_fb8 (by decide) (by decide) E hd hkv E.kRaw
    (by decide) (by decide) (by rsimp; exact R.rsp)
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; rw [R.rsp, e28, h28])
    (by rsimp; rw [R.rsp, e1C, h1C])
    (by rsimp <;> rfl)
    (by rsimp <;> rfl) fun m2 hfr _ hres => ?_
  have S2 := S.call O hfr
  generalize m2.mem = M2 at hfr hres S2
  have e10 : (4096 : Word) + 784 + (X.B + 0x3A50) + 16 = acSlot X.B 0x1320 := by simp only [acSlot]; bv_omega
  have e14 : (4096 : Word) + 784 + (X.B + 0x3A50) + 20 = acSlot X.B 0x1324 := by simp only [acSlot]; bv_omega
  have e4 : acSlot X.B 0x1320 + 4 = acSlot X.B 0x1324 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  refine WP.lui ac_at_fbc ?_; wn
  refine WP.aluImm ac_at_fbe ?_; wn
  refine WP.alu ac_at_fc2 ?_; wn
  refine WP.lw ac_at_fc4 (by rsimp; simp only [ev_add, R.rsp]; rw [e10]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  rcases hf : key.field (ascii!"rawBytes") with _ | ju <;> rw [hf] at hres
  · obtain ⟨t0, t4⟩ := hres
    refine WP.branch ac_at_fc6 (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact acetl_f1402 O A S2.m (by hr) (by rw [← e4, t4]; decide)
    · exfalso; rsimp at eb; simp only [ev_add, R.rsp] at eb; rw [e10, t0] at eb; exact absurd eb (by decide)
  obtain ⟨uq, ul, huv, t0, t4⟩ := hres
  obtain ⟨b1, b2, b3, b4, b5⟩ := acetl_valB O huv
  refine WP.branch ac_at_fc6 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; simp only [ev_add, R.rsp] at eb; rw [e10, t0] at eb
    have e : uq = 0 := by simpa [branchTaken] using eb
    rw [e] at b3; simp at b3
  refine WP.lui ac_at_fca ?_; wn
  refine WP.aluImm ac_at_fcc ?_; wn
  refine WP.alu ac_at_fd0 ?_; wn
  refine WP.lw ac_at_fd2 (by rsimp; simp only [ev_add, R.rsp]; rw [e14]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.aluImm ac_at_fd4 ?_; wn
  refine WP.aluImm ac_at_fd8 ?_; wn
  have hd2 := S2.doc O A
  have E2 := acetl_env O A S2.m
  refine WP.acetlStr O ac_at_fdc ac_at_fe0 (by decide) (by decide) E2 hd2 huv
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; simp only [ev_add, R.rsp]; rw [e10, t0])
    (by rsimp; simp only [ev_add, R.rsp]; rw [e14, ← e4, t4]) fun m3 hfr3 hstr => ?_
  have S3 := S2.call O hfr3
  have hfr13 : ∀ x, AcetlV X.B x → m3.mem x = M x := fun x hx => (hfr3 x hx).trans (hfr x hx)
  generalize m3.mem = M3 at hfr3 hstr S3 hfr13
  have e0 : acSlot X.B 0x890 + 0 = acSlot X.B 0x890 := BitVec.add_zero _
  have e894 : acSlot X.B 0x890 + 4 = acSlot X.B 0x894 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  rcases hs : ju.asStr with _ | s <;> rw [hs] at hstr
  · obtain ⟨t0, t4⟩ := hstr
    refine WP.lw ac_at_fe4 (by rsimp; rw [R.r19, e0]; exact ace_al4 F (by decide) (by decide)) ?_; wn
    refine WP.branch ac_at_fe8 (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact acetl_f1410 O A S3.m (by hr) (by rw [t4]; decide)
    · exfalso; rsimp at eb; rw [R.r19, e0, t0] at eb; exact absurd eb (by decide)
  obtain ⟨q, hsq, t0, t4⟩ := hstr
  have hb := acetl_inB O hsq
  refine WP.lw ac_at_fe4 (by rsimp; rw [R.r19, e0]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.branch ac_at_fe8 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [R.r19, e0, t0] at eb
    have e : q = 0 := by simpa [branchTaken] using eb
    rw [e] at hb; have : (0 : Word).toNat = 0 := rfl
    omega
  refine WP.lw ac_at_fec (by rsimp; rw [R.r19, e894]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.aluImm ac_at_ff0 ?_; wn
  refine WP.lui ac_at_ff2 ?_; wn
  refine WP.aluImm ac_at_ff4 ?_; wn
  refine WP.alu ac_at_ff8 ?_; wn
  have hd3 := S3.doc O A
  have E3 := acetl_env O A S3.m
  have hsm := acetl_inBytes O hd3 hsq
  have esG : X.B + 0x3A50 + 0xFFFFFF90 = X.B + BitVec.ofNat 32 0x39E0 := by rw [BitVec.add_assoc]; rfl
  have hsp0 : (X.B + 0x3A50).toNat = X.B.toNat + 0x3A50 := F.at _ (by decide)
  have hO244 : (acSlot X.B 0x244).toNat = X.B.toNat + (0x3A50 + 0x244) := F.at _ (by decide)
  have hO1FDC : (acSlot X.B 0x1FDC).toNat = X.B.toNat + (0x3A50 + 0x1FDC) := F.at _ (by decide)
  have hfl0 := S3.hi
  have hAC := ace_AC
  refine WP.acetlDecode (out := acSlot X.B 0x244) (t := q) (fr := acSlot X.B 0x1FDC) (fp := fp0)
    (sp0 := X.B + 0x3A50) (n := s.length) (fl := X.Bf.toNat + 0xB840 - fp0.toNat)
    ac_at_ffa ac_at_ffe (by decide) (by decide) E3.decode
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; rw [R.r19, e0, t0])
    (by rsimp; rw [R.r19, t4])
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; exact R.rsp) (ace_al4 F (by decide) (by decide)) (by rw [hsp0]; omega) (by rw [hsp0]; omega)
    (ace_al4 (c := 0x3A50 + 0x244) F (by decide) (by decide)) (by rw [hO244]; omega)
    (ace_al4 (c := 0x3A50 + 0x1FDC) F (by decide) (by decide)) (by rw [hO1FDC]; omega)
    S3.fpv (by rw [show acSlot X.B 0x1FDC + 4 = acSlot X.B 0x1FE0 by unfold acSlot; rw [BitVec.add_assoc]; rfl]; exact S3.flv)
    (by omega) (by omega)
    (by rw [esG]; exact ace_sepB' (c := 0x3A50 + 0x244) F (.inr (by decide)) (by decide) (by decide))
    (by rw [esG]; exact ace_sepB' (c := 0x3A50 + 0x1FDC) F (.inr (by decide)) (by decide) (by decide))
    (by rw [esG]; exact (acetl_bufSep O (by decide) (by omega) (by unfold acBufLen; omega)).symm)
    (by rw [esG]; exact (acetl_bufSep O (by decide) (by omega) (by unfold acBufLen; omega)).symm)
    (sep_of_le (by omega) (by omega))
    (acetl_bufSep O (c := 0x3A50 + 0x244) (by decide) (by omega) (by unfold acBufLen; omega))
    (acetl_bufSep O (c := 0x3A50 + 0x1FDC) (by decide) (by omega) (by unfold acBufLen; omega))
    (ace_sepB' (c := 0x3A50 + 0x244) F (.inl (by decide)) (by decide) (by decide))
    (by rw [esG]; exact ace_cs F (by decide)) (ace_cs (c := 0x3A50 + 0x244) F (by decide))
    (ace_cs (c := 0x3A50 + 0x1FDC) F (by decide)) (sep_of_le (by omega) (by omega)) fun m4 hR => ?_
  rw [hsm] at hR
  obtain ⟨hO, hR4⟩ := hR
  have hD : ∀ x, AcetlD X fp0 x → m4.mem x = M3 x := fun x hx => by
    refine hR4 x ?_ ?_ ?_ ?_
    · rw [esG]
      exact (acetl_sepV F hx.1 (a := 0x3110) (b := 0x3A50) (c := 0x39E0) (n := 0x70) (by decide) (by decide)
        (by decide)).symm
    · exact (acetl_sepV F hx.1 (a := 0x3C94) (b := 0x3C9C) (c := 0x3A50 + 0x244) (n := 8) (by decide) (by decide)
        (by decide)).symm
    · exact (ace_sepX (c := 0x3A50 + 0x1FDC) F (by decide) hx.2.1).symm
    · rcases hx.2.2 with h | h
      · exact (sep_of_le (by omega) (by omega)).symm
      · exact sep_of_le (by omega) (by have := x.isLt; omega)
  have hDM : ∀ x, AcetlD X fp0 x → m4.mem x = M x := fun x hx => (hD x hx).trans (hfr13 x hx.1)
  have hm4 : ∀ x, AcetlU X.B X.Bf fp0 true x → m4.mem x = n0.mem x := fun x hx =>
    (hD x (acetl_UD hx)).trans (S3.m x hx)
  have e248 : acSlot X.B 0x244 + 4 = acSlot X.B 0x248 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  have e244 : X.B + 0x3A50 + 0x244 = acSlot X.B 0x244 := by simp only [acSlot]; bv_omega
  rcases hres : trDecodeRes (base64Decode s) (X.Bf.toNat + 0xB840 - fp0.toNat) with _ | d <;> rw [hres] at hO
  · obtain ⟨o0, -, -, oc⟩ := hO
    refine WP.lw ac_at_1002 (by rsimp; rw [R.rsp, e244]; exact ace_al4 F (by decide) (by decide)) ?_; wn
    refine WP.branch ac_at_1006 (fun _ => ?_) (fun eb => ?_) <;> wn
    · refine acetl_f1428 O A hm4 (by hr) ?_
      rw [← e248]; rcases oc with h | h <;> rw [h] <;> decide
    · exfalso; rsimp at eb; rw [R.rsp, e244, o0] at eb; exact absurd eb (by decide)
  obtain ⟨o0, o4, o8, oc, odm⟩ := hO
  obtain ⟨hbd, hdl⟩ := acetl_trdec hres
  have hl : (fp0 + BitVec.ofNat 32 d.length).toNat = fp0.toNat + d.length := acetl_addN (by omega)
  have e1FE0 : acSlot X.B 0x1FDC + 4 = acSlot X.B 0x1FE0 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  have S4 : AcetlS X n0 fp0 m4.mem (fp0 + BitVec.ofNat 32 d.length) rest := by
    refine ⟨hm4, ?_, o8, ?_, by omega, by omega⟩
    · refine acetl_cur_move S3.cur (acetl_ldD O hD hfp0 (s := 0x1860) (by decide) (by decide) (by decide)) ?_ ?_
      · rw [acetl_s4]; exact acetl_ldD O hD hfp0 (s := 0x1864) (by decide) (by decide) (by decide)
      · rw [acetl_s8]; exact acetl_ldD O hD hfp0 (s := 0x1868) (by decide) (by decide) (by decide)
    · rw [← e1FE0, oc, hl]; congr 1; omega
  have hchain : (key.field (ascii!"rawBytes") >>= Json.asStr >>= base64Decode >>= readExpect ed25519SpkiPrefix) =
      readExpect ed25519SpkiPrefix d := by
    rw [hf]
    show ((ju.asStr >>= base64Decode) >>= readExpect ed25519SpkiPrefix) = _
    rw [hs]
    show (base64Decode s >>= readExpect ed25519SpkiPrefix) = _
    rw [hbd]; rfl
  exact acetl_t1002 O A I (by hr) (by rsimp; exact h26) S4 (by omega) o0 (by rw [← e248, o4]) odm hkv
    ((acetl_ldD O hDM hfp0 (s := 0x28) (by decide) (by decide) (by decide)).trans h28)
    ((acetl_ldD O hDM hfp0 (s := 0x1C) (by decide) (by decide) (by decide)).trans h1C) hjv
    (fun pk hpk => hent pk (hchain.trans hpk)) (by rsimp; exact h22) (by rsimp; exact h23)

end

end C3.RV32.Ac
