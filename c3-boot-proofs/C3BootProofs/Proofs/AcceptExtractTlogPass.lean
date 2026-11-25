import C3BootProofs.Proofs.AcceptExtractTlogEnd

/-! `AceTlogStage`'s pass over one transparency log, from 0xEF2 back to 0xEBA. -/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

set_option maxRecDepth 100000

/-! ## The spec -/

/-- A byte the origin check takes. -/
def acetlPr (b : Nat) : Prop := 0x20 ≤ b ∧ b ≤ 0x7e

theorem acetl_logEntry_some {j key : Json} {pk s r : Bytes} {w : Window}
    (hk : j.field (ascii!"publicKey") = some key)
    (hd : (key.field (ascii!"keyDetails") >>= Json.asStr) = some (ascii!"PKIX_ED25519"))
    (hp : (key.field (ascii!"rawBytes") >>= Json.asStr >>= base64Decode >>= readExpect ed25519SpkiPrefix) = some pk)
    (hq : (pk.length == 32 && (Ed25519.decode pk).any (fun q => !Ed25519.smallOrder q)) = true)
    (hu : (j.field (ascii!"baseUrl") >>= Json.asStr) = some s)
    (hr : readExpect (ascii!"https://") s = some r)
    (ho : (!((r.reverse.dropWhile (· == 0x2F)).reverse).isEmpty &&
      ((r.reverse.dropWhile (· == 0x2F)).reverse).all fun b => 0x20 ≤ b && b ≤ 0x7e) = true)
    (hw : (key.field (ascii!"validFor") >>= validFor) = some w) :
    logEntry j = some (some ⟨(r.reverse.dropWhile (· == 0x2F)).reverse, pk, w⟩) := by
  simp only [Option.bind_eq_bind] at hd hp hu hw
  unfold logEntry
  simp only [hk, Option.bind_eq_bind, Option.bind_some, hd, bne_self_eq_false, Bool.false_eq_true, ite_false, hp,
    require, hq, ite_true, hu, hr, ho, hw]
  rfl

theorem acetl_logEntry_none {j key : Json} {d : Bytes}
    (hk : j.field (ascii!"publicKey") = some key)
    (hd : (key.field (ascii!"keyDetails") >>= Json.asStr) = some d) (hne : d ≠ ascii!"PKIX_ED25519") :
    logEntry j = some none := by
  simp only [Option.bind_eq_bind] at hd
  unfold logEntry
  have : (d != ascii!"PKIX_ED25519") = true := bne_iff_ne.mpr hne
  simp only [hk, Option.bind_eq_bind, Option.bind_some, hd, this, ite_true]
  rfl

theorem acetl_dropWhile_all {p : Nat → Bool} : ∀ {l1 l2 : List Nat}, (∀ x ∈ l1, p x = true) →
    (l1 ++ l2).dropWhile p = l2.dropWhile p
  | [], _, _ => rfl
  | a :: l1, l2, h => by
    rw [List.cons_append, List.dropWhile_cons_of_pos (h a (List.mem_cons_self ..))]
    exact acetl_dropWhile_all fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem acetl_getD_drop {s : Bytes} {k i : Nat} : (s.drop k).getD i 0 = s.getD (k + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem acetl_origin {s : Bytes} {m : Nat} (hm : 0 < m) (hL : 8 + m ≤ s.length)
    (hne : s.getD (8 + (m - 1)) 0 ≠ 0x2F) (hsl : ∀ i, m ≤ i → 8 + i < s.length → s.getD (8 + i) 0 = 0x2F) :
    ((s.drop 8).reverse.dropWhile (· == 0x2F)).reverse = (s.drop 8).take m := by
  have hr : (s.drop 8).length = s.length - 8 := List.length_drop ..
  have hsplit : (s.drop 8).take m = ((s.drop 8).take (m - 1)) ++ [(s.drop 8).getD (m - 1) 0] := by
    conv => lhs; rw [show m = (m - 1) + 1 by omega]
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  conv => lhs; rw [← List.take_append_drop m (s.drop 8), List.reverse_append]
  rw [acetl_dropWhile_all, hsplit, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.dropWhile_cons_of_neg, List.reverse_cons, List.reverse_reverse]
  · rw [acetl_getD_drop]; simpa using hne
  · intro x hx
    rw [List.mem_reverse, List.mem_iff_getElem] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [List.length_drop, List.length_drop] at hk
    have h1 := hsl (m + k) (by omega) (by omega)
    rw [← acetl_getD_drop (k := 8), ← acetl_getD_drop (k := m), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [List.length_drop, List.length_drop]; omega)] at h1
    simp only [Option.getD_some] at h1
    rw [h1]; rfl

theorem acetl_printOk {s : Bytes} {m : Nat} (hm : 0 < m) (hL : 8 + m ≤ s.length)
    (hp : ∀ i < m, acetlPr (s.getD (8 + i) 0)) :
    (!((s.drop 8).take m).isEmpty && ((s.drop 8).take m).all fun b => 0x20 ≤ b && b ≤ 0x7e) = true := by
  have hlen : ((s.drop 8).take m).length = m := by rw [List.length_take, List.length_drop]; omega
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · cases h : (s.drop 8).take m with
    | nil => rw [h] at hlen; simp at hlen; omega
    | cons _ _ => rfl
  · rw [List.all_eq_true]
    intro x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [hlen] at hk
    obtain ⟨h1, h2⟩ := hp k hk
    rw [List.getElem_take, List.getElem_drop]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at h1 h2
    simp only [Option.getD_some] at h1 h2
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨h1, h2⟩

/-! ## The machine -/

/-- A span of `Buffers` is apart from the stack frame. -/
theorem acetl_bufSep {X : AceCtx} (O : X.Ok) {c k : Nat} (hc : c + k ≤ 0x5A70) {p : Word} {n : Nat}
    (h1 : X.Bf.toNat ≤ p.toNat) (h2 : p.toNat + n ≤ X.Bf.toNat + acBufLen) :
    Sep (X.B + BitVec.ofNat 32 c) k p n := by
  have hb := O.lay.hi
  have e : p = X.Bf + BitVec.ofNat 32 (p.toNat - X.Bf.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := p.isLt; omega
  rw [e]; exact (O.lay.sep.sub hc).subR (by omega)

theorem acetl_ofNatMod (t : Nat) : BitVec.ofNat 32 (t % 2 ^ 32) = BitVec.ofNat 32 t := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod]

theorem acetl_mb1 (M : Word → BitVec 8) (a : Word) : memBytes M a 1 = [(M a).toNat] := by
  unfold memBytes
  rw [show List.range 1 = [0] from rfl, List.map_cons, List.map_nil,
    show a + BitVec.ofNat 32 0 = a from BitVec.add_zero a]

theorem acetl_pkV {X : AceCtx} (O : X.Ok) {M M' : Word → BitVec 8} (hfr : ∀ x, AcetlV X.B x → M' x = M x)
    {fp0 : Word} (h1 : X.Bf.toNat ≤ fp0.toNat) (h2 : fp0.toNat + 44 ≤ X.Bf.toNat + 0xB840) :
    memBytes M' (fp0 + 12) 32 = memBytes M (fp0 + 12) 32 := by
  have hb := O.lay.hi; unfold acBufLen at hb
  refine ace_memBytes_ext fun i hi => hfr _ (acetl_V_out (ace_ofSep (ace_bufOut O.lay ?_ ?_))) <;>
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add]
    have : (12 : Word).toNat = 12 := rfl
    (try unfold acBufLen); omega

theorem acetl_e44 {X : AceCtx} {n0 : Machine} {fp0 : Word} {M : Word → BitVec 8} {rest : List Json}
    (S : AcetlS X n0 fp0 M (fp0 + 44) rest) : (fp0 + 44).toNat = fp0.toNat + 44 := by
  have h1 := S.lo; have h2 : (44 : Word).toNat = 44 := rfl
  rw [BitVec.toNat_add, h2] at h1 ⊢; omega

/-- A call to `equal_same_length` from the closure, which saves `ra` on the stack. -/
theorem WP.acetlEsl {X : AceCtx} (O : X.Ok) {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}
    {hi lo q1 q2 : Word} {l : Nat}
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = RES) (hev : (off + 8) % 2 = 0)
    (E : AcExtractEnv M) (hsp : f sp = X.B + 0x3A50) (h0 : f a0 = q1) (ha1 : f a1 = q2)
    (ha2 : f a2 = BitVec.ofNat 32 l) (hl : l < 2 ^ 32)
    (s1 : Sep (X.B + BitVec.ofNat 32 0x3A4C) 4 q1 l) (s2 : Sep (X.B + BitVec.ofNat 32 0x3A4C) 4 q2 l)
    (k : ∀ m2 : Machine, reg m2 a0 = (if memBytes M q1 l = memBytes M q2 l then 1 else 0) →
      (∀ x, AcetlV X.B x → m2.mem x = M x) →
      WP bootMainClosure0Code AC Q m2.mem (off + 8) (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 eslClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  have F := O.lay.fr
  refine WP.callEsl (tb := RES) (r := X.B + BitVec.ofNat 32 0x3A4C) h1 h2 htgt (by decide) hev E.equal
    (by rw [show RES + 0xD3BE = RMC by decide]; exact E.memcmp) h0 ha1 ha2 hl
    (by rw [hsp]; bv_omega) (by rw [hsp]; exact ace_al4 F (by decide) (by decide))
    (ace_hs F (by decide) (by decide) (by decide)) (ace_hs F (by decide) (by decide) (by decide)) s1 s2
    (ace_cs F (by decide)) fun m2 hr hO => k m2 hr fun x hx =>
      hO x (acetl_sepV F hx (a := 0x3110) (b := 0x3A50) (c := 0x3A4C) (n := 4) (by decide) (by decide) (by decide))

section
variable {X : AceCtx} {n0 : Machine} {fp0 : Word} {jr : Json} {fs : List FulcioKey} {j : Json}
  {rest : List Json} {ls : List LogKey} {M : Word → BitVec 8} {f : Fin 32 → Word}

set_option maxHeartbeats 4000000 in
/-- From 0x1116: `field` for `validFor` on the key, `valid_for`, and the push. -/
theorem acetl_t1116 (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs (j :: rest) ls)
    (R : AceHR X f) (h26 : f 26 = reg n0 26) (S : AcetlS X n0 fp0 M (fp0 + 44) rest)
    {key : Json} {kq : Word} {kl : Nat} (hkv : AceVal X.D X.json kq kl key)
    (h28 : memLoad32 M (acSlot X.B 0x28) = kq) (h1C : memLoad32 M (acSlot X.B 0x1C) = BitVec.ofNat 32 kl)
    {origin pk : Bytes} (hent : ∀ w, (key.field (ascii!"validFor") >>= validFor) = some w →
      logEntry j = some (some ⟨origin, pk, w⟩))
    {op : Word} (ho1 : X.D.toNat ≤ op.toNat) (ho2 : op.toNat + origin.length ≤ X.D.toNat + X.json.length)
    (ho3 : slice X.json (op.toNat - X.D.toNat) origin.length = origin)
    (hpk : memBytes M (fp0 + 12) 32 = pk)
    (h20 : f 20 = op) (h22 : f 22 = BitVec.ofNat 32 origin.length) (h24 : f 24 = fp0 + 12) :
    WP bootMainClosure0Code AC (acetlQ X 0xEBA (acetlNx X jr fs rest)) M 0x1116 f := by
  have F := O.lay.fr
  have hh := F.hi
  have hfp0 := A.fr.lo
  have hbw := O.lay.hi
  unfold acBufLen at hbw
  have h44 := S.hi
  have e44 : (fp0 + 44).toNat = fp0.toNat + 44 := by
    have h1 := S.lo; have h2 : (44 : Word).toNat = 44 := rfl
    rw [BitVec.toNat_add, h2] at h1 ⊢; omega
  rw [e44] at h44
  have hd := S.doc O A
  have E := acetl_env O A S.m
  have e28 : X.B + 0x3A50 + 0x28 = acSlot X.B 0x28 := by simp only [acSlot]; bv_omega
  have e1C : X.B + 0x3A50 + 0x1C = acSlot X.B 0x1C := by simp only [acSlot]; bv_omega
  refine WP.aluImm ac_at_1116 ?_; wn
  refine WP.aluImm ac_at_111a ?_; wn
  refine WP.aluImm ac_at_111e ?_; wn
  refine WP.lw ac_at_1120 (by rsimp; rw [R.rsp, e28]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.lw ac_at_1122 (by rsimp; rw [R.rsp, e1C]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_1124 ?_; wn
  refine WP.aluImm ac_at_1128 ?_; wn
  refine WP.acetlField O (o := 0x890) (a := 0x42E0) (b := 0x43E0) (kq := (img% roWindowAddress + 0x700)) (kl := 8) (by decide)
    (by decide) (by decide) (by decide) ac_at_112c ac_at_1130 (by decide) (by decide) E hd hkv E.kValidFor
    (by decide) (by decide) (by rsimp; exact R.rsp)
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; rw [R.rsp, e28, h28])
    (by rsimp; rw [R.rsp, e1C, h1C])
    (by rsimp <;> rfl)
    (by rsimp <;> rfl) fun m2 hfr _ hres => ?_
  have S2 := S.call O hfr
  generalize m2.mem = M2 at hfr hres S2
  have h28' : memLoad32 M2 (acSlot X.B 0x28) = kq := (acetl_ldV O hfr (s := 0x28) (by decide) (by decide)).trans h28
  have hpk2 : memBytes M2 (fp0 + 12) 32 = pk := by
    rw [← hpk]; refine ace_memBytes_ext fun i hi => hfr _ (acetl_V_out (ace_ofSep (ace_bufOut O.lay ?_ ?_))) <;>
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add]
      have : (12 : Word).toNat = 12 := rfl
      (try unfold acBufLen); omega
  have e0 : acSlot X.B 0x890 + 0 = acSlot X.B 0x890 := BitVec.add_zero _
  have e4 : acSlot X.B 0x890 + 4 = acSlot X.B 0x894 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  rcases hf : key.field (ascii!"validFor") with _ | jv <;> rw [hf] at hres
  · obtain ⟨t0, t4⟩ := hres
    refine WP.lw ac_at_1134 (by rsimp; rw [R.r19, e0]; exact ace_al4 F (by decide) (by decide)) ?_; wn
    refine WP.branch ac_at_1138 (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact acetl_f1410 O A S2.m (by hr) (by rw [t4]; decide)
    · exfalso; rsimp at eb; rw [R.r19, e0, t0] at eb; exact absurd eb (by decide)
  obtain ⟨vq, vl, hvv, t0, t4⟩ := hres
  obtain ⟨b1, b2, b3, b4, b5⟩ := acetl_valB O hvv
  refine WP.lw ac_at_1134 (by rsimp; rw [R.r19, e0]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.branch ac_at_1138 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [R.r19, e0, t0] at eb
    have e : vq = 0 := by simpa [branchTaken] using eb
    rw [e] at b3; simp at b3
  refine WP.lw ac_at_113c (by rsimp; rw [R.r19, e4]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_1140 ?_; wn
  refine WP.aluImm ac_at_1142 ?_; wn
  refine WP.alu ac_at_1146 ?_; wn
  have E2 := acetl_env O A S2.m
  have hd2 := S2.doc O A
  have es : X.B + 0x3A50 + 0xFFFFFEBC = X.B + BitVec.ofNat 32 0x390C := by rw [BitVec.add_assoc]; rfl
  refine WP.acetlValidFor (out := acSlot X.B 0x1320) (p := vq) (n := vl) (sp0 := X.B + 0x3A50) (c := false)
    (j := jv) ac_at_1148 ac_at_114c (by decide) (by decide) E2.validFor
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; rw [R.r19, e0, t0])
    (by rsimp; rw [R.r19]; exact t4)
    (by rsimp; exact R.rsp)
    (show (X.B + BitVec.ofNat 32 0x3A50).toNat % 4 = 0 from ace_al4 F (by decide) (by decide))
    (by rw [show X.B + 0x3A50 = X.B + BitVec.ofNat 32 0x3A50 from rfl, F.at _ (by decide)]; omega)
    (by rw [show X.B + 0x3A50 = X.B + BitVec.ofNat 32 0x3A50 from rfl, F.at _ (by decide)]; omega)
    (ace_al4 (c := 0x3A50 + 0x1320) F (by decide) (by decide))
    (by rw [show acSlot X.B 0x1320 = X.B + BitVec.ofNat 32 (0x3A50 + 0x1320) from rfl, F.at _ (by decide)]; omega)
    (by omega) (by omega)
    (by rw [es]; exact ace_sepB' F (.inr (by decide)) (by decide) (by decide))
    (by rw [es]; exact (acetl_bufSep O (c := 0x390C) (k := 0x144) (by decide) (by omega)
      (by unfold acBufLen; omega)).symm)
    (by rw [es]; exact O.lay.ro.sub (c := 0x390C) (l := 0x144) (by decide))
    E2.kStart E2.kEnd (by rw [hd2 vq vl b1 b2]; exact hvv.2.2)
    (by rw [es]; exact ace_cs F (by decide)) (ace_cs F (c := 0x3A50 + 0x1320) (by decide)) fun m3 r hR hv he => ?_
  obtain ⟨hO, hR2⟩ := hR
  have hfr3 : ∀ x, AcetlV X.B x → m3.mem x = M2 x := fun x hx => hR2 x
    (by rw [es]; exact (acetl_sepV F hx (a := 0x3110) (b := 0x3A50) (c := 0x390C) (n := 0x144) (by decide)
      (by decide) (by decide)).symm)
    (acetl_sepV F hx (a := 0x4D70) (b := 0x4D88) (c := 0x3A50 + 0x1320) (n := 0x18) (by decide) (by decide)
      (by decide)).symm
  have S3 := S2.call O hfr3
  have hpk3 : memBytes m3.mem (fp0 + 12) 32 = pk := by
    rw [← hpk2]; refine ace_memBytes_ext fun i hi => hfr3 _ (acetl_V_out (ace_ofSep (ace_bufOut O.lay ?_ ?_))) <;>
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add]
      have : (12 : Word).toNat = 12 := rfl
      (try unfold acBufLen); omega
  generalize m3.mem = M3 at hO hR2 hfr3 S3 hpk3
  have e10 : (4096 : Word) + 784 + (X.B + 0x3A50) + 16 = acSlot X.B 0x1320 := by simp only [acSlot]; bv_omega
  have e1 : acSlot X.B 0x1320 + 1 = acSlot X.B 0x1321 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  refine WP.lui ac_at_1150 ?_; wn
  refine WP.aluImm ac_at_1152 ?_; wn
  refine WP.alu ac_at_1156 ?_; wn
  refine WP.lbu ac_at_1158 ?_; wn
  simp only [ev_add, R.rsp]
  rw [e10]
  rcases r with e | ⟨t, u⟩
  · obtain ⟨o0, o1⟩ := hO
    have hel := he e rfl
    refine WP.branch ac_at_115c (fun _ => ?_) (fun eb => ?_) <;> wn
    · refine acetl_f1416 O A S3.m (by hr) ?_
      rw [← e1, o1, BitVec.toNat_ofNat]; omega
    · exfalso; rsimp at eb; rw [o0] at eb; exact absurd eb (by decide)
  obtain ⟨hnb, hna, o0, o8, oC, o10, o14⟩ := hO
  refine WP.branch ac_at_115c (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [o0] at eb; exact absurd eb (by decide)
  have hvf : validFor jv = some ⟨t, u⟩ := by rw [← hv]; rfl
  have hj : logEntry j = some (some ⟨origin, pk, ⟨t, u⟩⟩) := hent _ (by rw [hf]; exact hvf)
  have e8 : acSlot X.B 0x1320 + 8 = acSlot X.B 0x1328 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  have eC : acSlot X.B 0x1320 + 0xC = acSlot X.B 0x132C := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  have e16 : acSlot X.B 0x1320 + 0x10 = acSlot X.B 0x1330 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  have e14 : acSlot X.B 0x1320 + 0x14 = acSlot X.B 0x1334 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  refine acetl_push O A I (by hr) (by rsimp; exact h26) (Ms := M3) (fun _ _ => rfl) S3.m S3.cur h44 S3.fpv
    (by rw [S3.flv, e44]) hj ho1 ho2 ho3 hpk3 hnb hna
    (by rw [← e8, o8]; exact acetl_ofNatMod t) (by rw [← eC, oC])
    (by rw [← e16, o10]; exact acetl_ofNatMod u) (by rw [← e14, o14])
    (by rsimp; exact h20) (by rsimp; exact h22) (by rsimp; exact h24)

theorem acetl_prAll : ∀ x : Fin 256, branchTaken .bltu (aluEval .add (BitVec.zeroExtend 32 (BitVec.ofFin x : BitVec 8))
    4294967264) (aluEval .add 0 95) = decide (0x20 ≤ x.val ∧ x.val ≤ 0x7e) := by
  decide

theorem acetl_prT {b : BitVec 8}
    (h : branchTaken .bltu (aluEval .add (BitVec.zeroExtend 32 b) 4294967264) (aluEval .add 0 95) = true) :
    acetlPr b.toNat := by
  rw [show b = BitVec.ofFin b.toFin from rfl, acetl_prAll] at h
  have := of_decide_eq_true h
  exact this

theorem acetl_prF {b : BitVec 8}
    (h : branchTaken .bltu (aluEval .add (BitVec.zeroExtend 32 b) 4294967264) (aluEval .add 0 95) = false) :
    ¬ acetlPr b.toNat := by
  rw [show b = BitVec.ofFin b.toFin from rfl, acetl_prAll] at h
  have := of_decide_eq_false h
  exact this

set_option maxHeartbeats 4000000 in
/-- The loop at 0x10FE that checks the origin's bytes are printable. -/
theorem acetl_print (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs (j :: rest) ls)
    (S : AcetlS X n0 fp0 M (fp0 + 44) rest)
    {key : Json} {kq : Word} {kl : Nat} (hkv : AceVal X.D X.json kq kl key)
    (h28 : memLoad32 M (acSlot X.B 0x28) = kq) (h1C : memLoad32 M (acSlot X.B 0x1C) = BitVec.ofNat 32 kl)
    {s : Bytes} {q : Word} (hs : AcetlIn X q s) {m : Nat} (hm : 8 + m ≤ s.length) {pk : Bytes}
    (hent : (∀ i < m, acetlPr (s.getD (8 + i) 0)) → ∀ w, (key.field (ascii!"validFor") >>= validFor) = some w →
      logEntry j = some (some ⟨(s.drop 8).take m, pk, w⟩))
    (hpk : memBytes M (fp0 + 12) 32 = pk) :
    ∀ k i, i + k = m → (∀ i' < i, acetlPr (s.getD (8 + i') 0)) → ∀ f : Fin 32 → Word, AceHR X f →
      f 26 = reg n0 26 → f 8 = 0x21 → f 20 = q + 8 → f 22 = BitVec.ofNat 32 m → f 24 = fp0 + 12 →
      f a0 = q + BitVec.ofNat 32 (8 + i) → f 9 = BitVec.ofNat 32 k →
      WP bootMainClosure0Code AC (acetlQ X 0xEBA (acetlNx X jr fs rest)) M 0x10FE f := by
  have hd := S.doc O A
  have hb := acetl_inB O hs
  have hsm := acetl_inBytes O hd hs
  intro k
  induction k with
  | zero =>
    intro i hi hp f R h26 h8 h20 h22 h24 h10 h9
    refine WP.branch ac_at_10fe (fun _ => ?_) (fun eb => ?_) <;> wn
    · rw [Nat.add_zero] at hi; subst hi
      obtain ⟨b1, b2, b3⟩ := hb
      have e8 : (q + 8).toNat = q.toNat + 8 := acetl_addN (a := 8) (by omega)
      have hq8 : memBytes M (q + 8) i = (s.drop 8).take i := by
        rw [← hsm, memBytes_drop M q (by omega), memBytes_take M _ (by omega)]; rfl
      refine acetl_t1116 O A I R h26 S hkv h28 h1C (hent hp) (op := q + 8) (by have := hs.1; omega)
        (by rw [List.length_take, List.length_drop]; have := hs.2.1; omega) ?_ hpk h20
        (by rw [h22, List.length_take, List.length_drop, Nat.min_eq_left (by omega)]) h24
      rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega), ← hd _ _ (by have := hs.1; omega)
        (by have := hs.2.1; omega), hq8]
    · exfalso; rw [h9, R.rz] at eb; exact absurd eb (by decide)
  | succ k ih =>
    intro i hi hp f R h26 h8 h20 h22 h24 h10 h9
    have hk : k + 1 < 2 ^ 32 := by have := hs.2.1; omega
    refine WP.branch ac_at_10fe (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; rw [h9, R.rz] at eb
      have := congrArg BitVec.toNat (beq_iff_eq.mp eb : BitVec.ofNat 32 (k + 1) = 0)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this; simp at this
    refine WP.lbu ac_at_1100 ?_; wn
    refine WP.aluImm ac_at_1104 ?_; wn
    refine WP.aluImm ac_at_1106 ?_; wn
    refine WP.aluImm ac_at_1108 ?_; wn
    refine WP.aluImm ac_at_110a ?_; wn
    have hbyte : (M (q + BitVec.ofNat 32 (8 + i))).toNat = s.getD (8 + i) 0 := by
      rw [← memBytes_getD (M := M) (p := q) (n := s.length) (by omega), hsm]
    refine WP.branch ac_at_110e (fun eb => ?_) (fun eb => ?_) <;> wn
    · refine ih (i + 1) (by omega) (fun i' hi' => ?_) _ (by hr) (by rsimp; exact h26) (by rsimp; exact h8)
        (by rsimp; exact h20) (by rsimp; exact h22) (by rsimp; exact h24) ?_ ?_
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | h
        · exact hp i' h
        · subst h
          rsimp at eb
          rw [h10, show q + BitVec.ofNat 32 (8 + i') + 0 = q + BitVec.ofNat 32 (8 + i') from BitVec.add_zero _] at eb
          rw [← hbyte]; exact acetl_prT eb
      · rsimp; rw [h10, ev_add, BitVec.add_assoc, show 8 + (i + 1) = 8 + i + 1 from rfl,
          BitVec.ofNat_add (8 + i) 1]; rfl
      · rsimp; rw [h9, ev_add]; apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have : (4294967295 : Word).toNat = 4294967295 := rfl
        rw [this]; omega
    · refine WP.jal ac_at_1112 (by decide) ?_
      refine acetl_f1A6A O A S.m (by hr) ?_
      rsimp; rw [h8]; decide

set_option maxHeartbeats 4000000 in
/-- The loop at 0x10DA that drops the slashes at the end of the URL. -/
theorem acetl_slash (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs (j :: rest) ls)
    {key : Json} {kq : Word} {kl : Nat} (hkv : AceVal X.D X.json kq kl key)
    {s : Bytes} {q : Word} (hs : AcetlIn X q s) {pk : Bytes}
    (hent : (!((s.drop 8).reverse.dropWhile (· == 0x2F)).reverse.isEmpty &&
        ((s.drop 8).reverse.dropWhile (· == 0x2F)).reverse.all fun b => 0x20 ≤ b && b ≤ 0x7e) = true →
      ∀ w, (key.field (ascii!"validFor") >>= validFor) = some w →
      logEntry j = some (some ⟨((s.drop 8).reverse.dropWhile (· == 0x2F)).reverse, pk, w⟩)) :
    ∀ m (M : Word → BitVec 8) (f : Fin 32 → Word), 8 + m ≤ s.length →
      (∀ i, m ≤ i → 8 + i < s.length → s.getD (8 + i) 0 = 0x2F) →
      AcetlS X n0 fp0 M (fp0 + 44) rest → memLoad32 M (acSlot X.B 0x28) = kq →
      memLoad32 M (acSlot X.B 0x1C) = BitVec.ofNat 32 kl → memBytes M (fp0 + 12) 32 = pk →
      AceHR X f → f 26 = reg n0 26 → f 8 = 0x21 → f 20 = q + 8 → f 24 = fp0 + 12 →
      f 18 = BitVec.ofNat 32 m → f 22 = BitVec.ofNat 32 (m + 1) → f 23 = q + BitVec.ofNat 32 (8 + m) →
      WP bootMainClosure0Code AC (acetlQ X 0xEBA (acetlNx X jr fs rest)) M 0x10DA f := by
  have hb := acetl_inB O hs
  have hlen : s.length < 2 ^ 32 := by omega
  have F := O.lay.fr
  intro m
  induction m with
  | zero =>
    intro M f _ _ S _ _ _ R _ h8 _ _ h18 _ _
    refine WP.branch ac_at_10da (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact acetl_f1A6A O A S.m R (by rw [h8]; decide)
    · exfalso; rw [h18, R.rz] at eb; exact absurd eb (by decide)
  | succ m ih =>
    intro M f hm hsl S h28 h1C hpk R h26 h8 h20 h24 h18 h22 h23
    have hk : m + 1 < 2 ^ 32 := by omega
    refine WP.branch ac_at_10da (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; rw [h18, R.rz] at eb
      have := congrArg BitVec.toNat (beq_iff_eq.mp eb : BitVec.ofNat 32 (m + 1) = 0)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this; simp at this
    refine WP.alu ac_at_10de ?_; wn
    refine WP.aluImm ac_at_10e0 ?_; wn
    refine WP.aluImm ac_at_10e2 ?_; wn
    refine WP.aluImm ac_at_10e4 ?_; wn
    refine WP.aluImm ac_at_10e6 ?_; wn
    refine WP.alu ac_at_10e8 ?_; wn
    refine WP.lui ac_at_10ea ?_; wn
    refine WP.aluImm ac_at_10ee ?_; wn
    have hd := S.doc O A
    have hsm := acetl_inBytes O hd hs
    have e7 : aluEval .add (q + BitVec.ofNat 32 (8 + (m + 1))) 4294967295 = q + BitVec.ofNat 32 (8 + m) := by
      have e : BitVec.ofNat 32 (8 + (m + 1)) + 4294967295 = BitVec.ofNat 32 (8 + m) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have : (4294967295 : Word).toNat = 4294967295 := rfl
        rw [this]; omega
      rw [ev_add, BitVec.add_assoc, e]
    have hq : (q + BitVec.ofNat 32 (8 + m)).toNat = q.toNat + (8 + m) := acetl_addN (by omega)
    refine WP.acetlEsl O (q1 := q + BitVec.ofNat 32 (8 + m)) (q2 := (img% roWindowAddress + 0x831)) (l := 1)
      ac_at_10f2 ac_at_10f6 (by decide) (by decide) (acetl_env O A S.m) (by rsimp; exact R.rsp)
      (by rsimp; rw [h23, e7, ev_add]; exact BitVec.zero_add _) (by rsimp <;> rfl) (by rsimp <;> rfl) (by decide)
      (acetl_bufSep O (by decide) (by omega) (by unfold acBufLen; omega))
      (tuf_sep_ro (O.lay.ro.sub (c := 0x3A4C) (l := 4) (by decide)) (by decide) (by decide)) fun m2 hr0 hfr => ?_
    have hbyte : memBytes M (q + BitVec.ofNat 32 (8 + m)) 1 = [s.getD (8 + m) 0] := by
      rw [acetl_mb1, ← memBytes_getD (M := M) (p := q) (n := s.length) (by omega), hsm]
    rw [hbyte, (acetl_env O A S.m).vSlash] at hr0
    refine WP.branch ac_at_10fa (fun eb => ?_) (fun eb => ?_) <;> wn
    · have hsl' : s.getD (8 + m) 0 = 0x2F := by
        rsimp at eb; rw [hr0] at eb
        rcases Nat.decEq (s.getD (8 + m) 0) 0x2F with hne | h
        · split at eb
          · next h' => exact absurd (List.singleton_inj.mp h') hne
          · exact absurd eb (by decide)
        · exact h
      refine ih m2.mem _ (by omega) (fun i h1 h2 => ?_) (S.call O hfr)
        ((acetl_ldV O hfr (s := 0x28) (by decide) (by decide)).trans h28)
        ((acetl_ldV O hfr (s := 0x1C) (by decide) (by decide)).trans h1C)
        ((acetl_pkV O hfr (by have := A.fr.lo; omega) (by have := S.hi; rw [acetl_e44 S] at this; exact this)).trans hpk) (by hr) (by rsimp; exact h26)
        (by rsimp; exact h8) (by rsimp; exact h20) (by rsimp; exact h24) ?_ ?_ ?_
      · rcases Nat.eq_or_lt_of_le h1 with h | h
        · subst h; exact hsl'
        · exact hsl i h h2
      · rsimp; rw [h18, ev_add]; apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have : (4294967295 : Word).toNat = 4294967295 := rfl
        rw [this]; omega
      · rsimp; rw [h22, ev_add]; apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have : (4294967295 : Word).toNat = 4294967295 := rfl
        rw [this]; omega
      · rsimp; rw [h23, e7]
    · have hne : s.getD (8 + (m + 1 - 1)) 0 ≠ 0x2F := by
        rsimp at eb; rw [hr0] at eb
        intro h
        rw [show m + 1 - 1 = m from rfl] at h
        rw [h] at eb
        exact absurd eb (by decide)
      have ho := acetl_origin (m := m + 1) (by omega) hm hne hsl
      refine WP.alu ac_at_10fc ?_; wn
      refine acetl_print O A I (S.call O hfr) hkv ((acetl_ldV O hfr (s := 0x28) (by decide) (by decide)).trans h28)
        ((acetl_ldV O hfr (s := 0x1C) (by decide) (by decide)).trans h1C) hs hm
        (fun hp w hw => ?_)
        ((acetl_pkV O hfr (by have := A.fr.lo; omega) (by have := S.hi; rw [acetl_e44 S] at this; exact this)).trans hpk)
        (m + 1) 0 (Nat.zero_add _) (fun _ h => absurd h (Nat.not_lt_zero _)) _ (by hr) (by rsimp; exact h26)
        (by rsimp; exact h8) (by rsimp; exact h20) ?_ (by rsimp; exact h24) ?_ ?_
      · rw [← ho]; exact hent (by rw [ho]; exact acetl_printOk (by omega) hm hp) w hw
      · rsimp; rw [h22, ev_add]; apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have : (4294967295 : Word).toNat = 4294967295 := rfl
        rw [this]; omega
      · rsimp; rw [h20, ev_add]; exact BitVec.zero_add _
      · rsimp; rw [R.rz, h18, ev_add]; exact BitVec.zero_add _

theorem acetl_https {s : Bytes} (h8 : 8 ≤ s.length) (heq : s.take 8 = ascii!"https://") :
    readExpect (ascii!"https://") s = some (s.drop 8) := by
  have hb : (s.take 8 == ascii!"https://") = true := by rw [heq]; rfl
  have hd : decide (8 ≤ s.length) = true := decide_eq_true h8
  unfold readExpect
  rw [show (ascii!"https://").length = 8 from rfl, hb, Bool.true_and, hd]
  rfl

set_option maxHeartbeats 4000000 in
/-- From 0x1048: `field` for `baseUrl`, `str`, and the `https://` prefix. -/
theorem acetl_t1048 (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs (j :: rest) ls)
    (R : AceHR X f) (h26 : f 26 = reg n0 26) (S : AcetlS X n0 fp0 M (fp0 + 44) rest)
    {key : Json} {kq : Word} {kl : Nat} (hkv : AceVal X.D X.json kq kl key)
    (h28 : memLoad32 M (acSlot X.B 0x28) = kq) (h1C : memLoad32 M (acSlot X.B 0x1C) = BitVec.ofNat 32 kl)
    {jq : Word} {jl : Nat} (hjv : AceVal X.D X.json jq jl j) {pk : Bytes}
    (hent : ∀ s r, (j.field (ascii!"baseUrl") >>= Json.asStr) = some s → readExpect (ascii!"https://") s = some r →
      (!((r.reverse.dropWhile (· == 0x2F)).reverse).isEmpty &&
        ((r.reverse.dropWhile (· == 0x2F)).reverse).all fun b => 0x20 ≤ b && b ≤ 0x7e) = true →
      ∀ w, (key.field (ascii!"validFor") >>= validFor) = some w →
      logEntry j = some (some ⟨(r.reverse.dropWhile (· == 0x2F)).reverse, pk, w⟩))
    (hpk : memBytes M (fp0 + 12) 32 = pk)
    (h18 : f 18 = 0) (h20 : f 20 = 1) (h22 : f 22 = jq) (h23 : f 23 = BitVec.ofNat 32 jl)
    (h24 : f 24 = fp0 + 12) :
    WP bootMainClosure0Code AC (acetlQ X 0xEBA (acetlNx X jr fs rest)) M 0x1048 f := by
  have F := O.lay.fr
  have hd := S.doc O A
  have E := acetl_env O A S.m
  have hfp0 := A.fr.lo
  have h44 := S.hi; rw [acetl_e44 S] at h44
  refine WP.lui ac_at_1048 ?_; wn
  refine WP.aluImm ac_at_104a ?_; wn
  refine WP.alu ac_at_104e ?_; wn
  refine WP.aluImm ac_at_1050 ?_; wn
  refine WP.alu ac_at_1052 ?_; wn
  refine WP.alu ac_at_1054 ?_; wn
  refine WP.lui ac_at_1056 ?_; wn
  refine WP.aluImm ac_at_105a ?_; wn
  refine WP.acetlField O (o := 0x1320) (a := 0x4D70) (b := 0x4D88) (kq := (img% roWindowAddress + 0x82A)) (kl := 7)
    (by decide) (by decide) (by decide) (by decide) ac_at_105e ac_at_1062 (by decide) (by decide) E hd hjv E.kUrl
    (by decide) (by decide) (by rsimp; exact R.rsp)
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; rw [h22, ev_add]; exact BitVec.zero_add _)
    (by rsimp; rw [h23, ev_add]; exact BitVec.zero_add _)
    (by rsimp <;> rfl)
    (by rsimp <;> rfl) fun m2 hfr _ hres => ?_
  have S2 := S.call O hfr
  generalize m2.mem = M2 at hfr hres S2
  have e10 : (4096 : Word) + 784 + (X.B + 0x3A50) + 16 = acSlot X.B 0x1320 := by simp only [acSlot]; bv_omega
  have e14 : (4096 : Word) + 784 + (X.B + 0x3A50) + 20 = acSlot X.B 0x1324 := by simp only [acSlot]; bv_omega
  have e4 : acSlot X.B 0x1320 + 4 = acSlot X.B 0x1324 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  refine WP.lui ac_at_1066 ?_; wn
  refine WP.aluImm ac_at_1068 ?_; wn
  refine WP.alu ac_at_106c ?_; wn
  refine WP.lw ac_at_106e (by rsimp; simp only [ev_add, R.rsp]; rw [e10]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  rcases hf : j.field (ascii!"baseUrl") with _ | ju <;> rw [hf] at hres
  · obtain ⟨t0, t4⟩ := hres
    refine WP.branch ac_at_1070 (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact acetl_f1402 O A S2.m (by hr) (by rw [← e4, t4]; decide)
    · exfalso; rsimp at eb; simp only [ev_add, R.rsp] at eb; rw [e10, t0] at eb; exact absurd eb (by decide)
  obtain ⟨uq, ul, huv, t0, t4⟩ := hres
  obtain ⟨b1, b2, b3, b4, b5⟩ := acetl_valB O huv
  refine WP.branch ac_at_1070 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; simp only [ev_add, R.rsp] at eb; rw [e10, t0] at eb
    have e : uq = 0 := by simpa [branchTaken] using eb
    rw [e] at b3; simp at b3
  refine WP.lui ac_at_1074 ?_; wn
  refine WP.aluImm ac_at_1076 ?_; wn
  refine WP.alu ac_at_107a ?_; wn
  refine WP.lw ac_at_107c (by rsimp; simp only [ev_add, R.rsp]; rw [e14]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.aluImm ac_at_107e ?_; wn
  refine WP.aluImm ac_at_1082 ?_; wn
  have hd2 := S2.doc O A
  have E2 := acetl_env O A S2.m
  refine WP.acetlStr O ac_at_1086 ac_at_108a (by decide) (by decide) E2 hd2 huv
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
    refine WP.lw ac_at_108e (by rsimp; rw [R.r19, e0]; exact ace_al4 F (by decide) (by decide)) ?_; wn
    refine WP.branch ac_at_1092 (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact acetl_f1410 O A S3.m (by hr) (by rw [t4]; decide)
    · exfalso; rsimp at eb; rw [R.r19, e0, t0] at eb; exact absurd eb (by decide)
  obtain ⟨q, hsq, t0, t4⟩ := hstr
  have hb := acetl_inB O hsq
  refine WP.lw ac_at_108e (by rsimp; rw [R.r19, e0]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.branch ac_at_1092 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [R.r19, e0, t0] at eb
    have e : q = 0 := by simpa [branchTaken] using eb
    rw [e] at hb; have : (0 : Word).toNat = 0 := rfl
    omega
  refine WP.lw ac_at_1096 (by rsimp; rw [R.r19, e894]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.aluImm ac_at_109a ?_; wn
  refine WP.aluImm ac_at_109e ?_; wn
  have hlen : s.length < 2 ^ 32 := by omega
  refine WP.branch ac_at_10a0 (fun eb => ?_) (fun eb => ?_) <;> wn
  · exact acetl_f1A6A O A S3.m (by hr) (by rsimp <;> decide)
  rsimp at eb; rw [R.r19, t4, show aluEval .add 0 8 = BitVec.ofNat 32 8 from rfl, br_bltu hlen (by decide)] at eb
  have h8L : 8 ≤ s.length := by have := of_decide_eq_false eb; omega
  refine WP.aluImm ac_at_10a4 ?_; wn
  refine WP.alu ac_at_10a6 ?_; wn
  refine WP.lui ac_at_10a8 ?_; wn
  refine WP.aluImm ac_at_10ac ?_; wn
  have hd3 := S3.doc O A
  have E3 := acetl_env O A S3.m
  have hsm := acetl_inBytes O hd3 hsq
  refine WP.acetlEsl O (q1 := q) (q2 := (img% roWindowAddress + 0x740)) (l := 8)
    ac_at_10b0 ac_at_10b4 (by decide) (by decide) E3 (by rsimp; exact R.rsp)
    (by rsimp; rw [R.r19, e0, t0, ev_add]; exact BitVec.zero_add _) (by rsimp <;> rfl) (by rsimp <;> rfl) (by decide)
    (acetl_bufSep O (by decide) (by omega) (by unfold acBufLen; omega))
    (tuf_sep_ro (O.lay.ro.sub (c := 0x3A4C) (l := 4) (by decide)) (by decide) (by decide)) fun m4 hr0 hfr4 => ?_
  have hq8 : memBytes M3 q 8 = s.take 8 := by rw [← hsm, memBytes_take M3 _ h8L]
  rw [hq8, E3.vHttps] at hr0
  refine WP.branch ac_at_10b8 (fun eb => ?_) (fun eb => ?_) <;> wn
  · exact acetl_f1A6A O A (S3.call O hfr4).m (by hr) (by rsimp <;> decide)
  have heq : s.take 8 = ascii!"https://" := by
    rsimp at eb; rw [hr0] at eb
    split at eb
    · next h => exact h
    · exact absurd eb (by decide)
  refine WP.aluImm ac_at_10bc ?_; wn
  refine WP.alu ac_at_10c0 ?_; wn
  refine WP.aluImm ac_at_10c4 ?_; wn
  refine WP.alu ac_at_10c8 ?_; wn
  refine WP.aluImm ac_at_10cc ?_; wn
  refine WP.alu ac_at_10d0 ?_; wn
  refine WP.aluImm ac_at_10d4 ?_; wn
  refine WP.alu ac_at_10d8 ?_; wn
  have hfrA : ∀ x, AcetlV X.B x → m4.mem x = M x := fun x hx => (hfr4 x hx).trans (hfr13 x hx)
  have hsub : ∀ c : Nat, c ≤ 8 → BitVec.ofNat 32 s.length + BitVec.ofNat 32 (2 ^ 32 - c) =
      BitVec.ofNat 32 (s.length - c) := fun c hc => by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  refine acetl_slash O A I hkv hsq (pk := pk)
    (fun ho w hw => hent s (s.drop 8) (by rw [hf]; exact hs) (acetl_https h8L heq) ho w hw)
    (s.length - 8) m4.mem _ (by omega) (fun i h1 h2 => absurd h2 (by omega)) (S3.call O hfr4)
    ((acetl_ldV O hfrA (s := 0x28) (by decide) (by decide)).trans h28)
    ((acetl_ldV O hfrA (s := 0x1C) (by decide) (by decide)).trans h1C)
    ((acetl_pkV O hfrA (by omega) h44).trans hpk) (by hr) (by rsimp; exact h26) (by rsimp <;> rfl) ?_ ?_ ?_ ?_ ?_
  · rsimp; rw [R.r19, e0, t0, ev_add]
  · rsimp; rw [h18, h20, h24, show aluEval .sub 0 (aluEval .and (aluEval .sltu 0 1) 1) = 0xFFFFFFFF by decide]
    exact jones_and _
  · rsimp; rw [R.r19, t4, ev_add, show (4294967288 : Word) = BitVec.ofNat 32 (2 ^ 32 - 8) from rfl, hsub 8 (by omega)]
  · rsimp; rw [R.r19, t4, ev_add, show (4294967289 : Word) = BitVec.ofNat 32 (2 ^ 32 - 7) from rfl, hsub 7 (by omega),
      show s.length - 7 = s.length - 8 + 1 by omega]
  · rsimp; rw [R.r19, t4, e0, t0, ev_add, Nat.add_sub_cancel' h8L]; exact BitVec.add_comm _ _

end

end C3.RV32.Ac
