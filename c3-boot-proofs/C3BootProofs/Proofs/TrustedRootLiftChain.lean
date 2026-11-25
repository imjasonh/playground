import C3BootProofs.Proofs.TrustedRootLiftCert
import C3BootProofs.Proofs.TrustedRootLift
import C3BootProofs.Proofs.TrustedRootReadChain

/-!
# `read_chain` and `Spec/TrustedRoot.lean`

`trustedRootReadChain_correct` states `read_chain` with the position model
`readChainPos` on the bytes of an entry. When those bytes are one JSON
value `entry` (`JVal`) and `readChainPos` accepts them, the spec's
`readChain entry` accepts the entry too: its window is the model's, and
its first certificate's serial number, issuer, subject, validity, and
P-384 key are the ones the model's certificate names (`readChainPos_spec`).
`trustedRootReadChain_spec` states the machine-level theorem that way, with
the fields read from the decoded certificates in the buffer.

The converse doesn't hold. `read_chain` decodes every certificate into a
buffer of `fl` bytes, and `readChain` has no such limit, so a chain whose
decoded certificates don't fit is one that `readChain` accepts and
`read_chain` rejects. That direction is fail-safe: the device then trusts
no key from that entry.
-/

namespace C3.RV32

open C3 C3.Json

/-- The spec's step for one certificate of the chain. -/
def trchCert (j : Json) : Option CertInfo :=
  j.field (ascii!"rawBytes") >>= Json.asStr >>= base64Decode >>= parseCert

/-- The model's first certificate `f` and the spec's `h` agree. -/
def TrchFirst (fp : Word) (D : Bytes) : Option RcCert → Option CertInfo → Prop
  | none, none => True
  | some c, some i => RcInfo D fp c i
  | _, _ => False

theorem trch_viewApp {D E : Bytes} {a l : Nat} (h : a + l ≤ D.length) :
    rcView (D ++ E) (a, l) = rcView D (a, l) := by
  unfold rcView
  dsimp only
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by rw [List.length_drop]; omega)]

theorem trch_viewShift (D E : Bytes) (a l : Nat) : rcView (D ++ E) (D.length + a, l) = rcView E (a, l) := by
  unfold rcView
  dsimp only
  rw [← List.drop_drop, List.drop_left]

theorem RcInfo.app {D E : Bytes} {fp : Word} {c : RcCert} {i : CertInfo} (h : RcInfo D fp c i) :
    RcInfo (D ++ E) fp c i := by
  obtain ⟨⟨a1, h1, b1, e1⟩, ⟨a2, h2, b2, e2⟩, ⟨a3, h3, b3, e3⟩, hw, hk⟩ := h
  have hl : D.length ≤ (D ++ E).length := by rw [List.length_append]; exact Nat.le_add_right _ _
  refine ⟨⟨a1, h1, Nat.le_trans b1 hl, by rw [e1, trch_viewApp b1]⟩,
    ⟨a2, h2, Nat.le_trans b2 hl, by rw [e2, trch_viewApp b2]⟩,
    ⟨a3, h3, Nat.le_trans b3 hl, by rw [e3, trch_viewApp b3]⟩, hw, ?_⟩
  rcases hk with ⟨a4, h4, b4, e4⟩ | hk
  · exact Or.inl ⟨a4, h4, Nat.le_trans b4 hl, by rw [e4, trch_viewApp b4]⟩
  · exact Or.inr hk

theorem RcInfo.shift {D E : Bytes} {fp : Word} {c : RcCert} {i : CertInfo}
    (h : RcInfo E (fp + BitVec.ofNat 32 D.length) c i) : RcInfo (D ++ E) fp c i := by
  obtain ⟨⟨a1, h1, b1, e1⟩, ⟨a2, h2, b2, e2⟩, ⟨a3, h3, b3, e3⟩, hw, hk⟩ := h
  have hl : (D ++ E).length = D.length + E.length := List.length_append
  refine ⟨⟨D.length + a1, by rw [h1, BitVec.ofNat_add, BitVec.add_assoc], by omega,
      by rw [e1, trch_viewShift]⟩,
    ⟨D.length + a2, by rw [h2, BitVec.ofNat_add, BitVec.add_assoc], by omega, by rw [e2, trch_viewShift]⟩,
    ⟨D.length + a3, by rw [h3, BitVec.ofNat_add, BitVec.add_assoc], by omega, by rw [e3, trch_viewShift]⟩, hw, ?_⟩
  rcases hk with ⟨a4, h4, b4, e4⟩ | hk
  · exact Or.inl ⟨D.length + a4, by rw [h4, BitVec.ofNat_add, BitVec.add_assoc], by omega,
      by rw [e4, trch_viewShift]⟩
  · exact Or.inr hk

theorem trch_strRes {p b : Word} {d : Bytes} {n : Nat} (h : strRes p d = some (b, n)) :
    2 ≤ d.length ∧ n = d.length - 2 := by
  unfold strRes at h
  by_cases h1 : d.length < 2
  · rw [ite_eq_left h1] at h; cases h
  rw [ite_eq_right h1] at h
  by_cases h2 : d.getD 0 0 ≠ 34
  · rw [ite_eq_left h2] at h; cases h
  rw [ite_eq_right h2] at h
  by_cases h3 : d.getD (d.length - 1) 0 ≠ 34
  · rw [ite_eq_left h3] at h; cases h
  rw [ite_eq_right h3] at h
  cases h
  exact ⟨Nat.le_of_not_lt h1, rfl⟩

theorem trch_mem {M : Word → BitVec 8} {q : Word} {l a n : Nat} {c : Bool} {j : Json}
    (h : JDen c (memBytes M q l) a n j) : JVal c (memBytes M (q + BitVec.ofNat 32 a) n) j := by
  have hb := h.1
  rw [memBytes_length] at hb
  have e : slice (memBytes M q l) a n = memBytes M (q + BitVec.ofNat 32 a) n := memBytes_slice hb
  exact e ▸ h.2

theorem trch_decode {d : Option Bytes} {fl : Nat} {bs : Bytes} (h : trDecodeRes d fl = some bs) : d = some bs := by
  unfold trDecodeRes at h
  cases d with
  | none => cases h
  | some bs' =>
    change (if bs'.length ≤ fl then some bs' else none) = some bs at h
    by_cases hl : bs'.length ≤ fl
    · rw [ite_eq_left hl] at h; rw [h]
    · rw [ite_eq_right hl] at h; cases h

/-- One step of the loop is the spec's step for that certificate. -/
theorem trch_step {c : Bool} {M0 : Word → BitVec 8} {fp : Word} {fl : Nat} {q : Word} {l after : Nat}
    {s s1 : RcSt} {j : Json} (hj : JVal c (memBytes M0 q l) j) (h : rcStep M0 fp fl q l after s = .ok s1) :
    ∃ info cert bs, trchCert j = some info ∧
      s1 = ⟨after, s.dec ++ bs, s.first.or (some cert), max s.nb cert.notBefore, min s.na cert.notAfter⟩ ∧
      RcInfo (s.dec ++ bs) fp cert info := by
  unfold rcStep at h
  have hF := ObjField c _ j (ascii!"rawBytes") hj
  cases hf : j.field (ascii!"rawBytes") with
  | none =>
    rw [hf] at hF
    rw [hF] at h
    cases h
  | some jr =>
    rw [hf] at hF
    obtain ⟨vp, vl, hof, hden⟩ := hF
    rw [hof] at h
    dsimp only at h
    have hjr := trch_mem hden
    obtain ⟨hs1, hs2⟩ := StrRes c _ jr (q + BitVec.ofNat 32 vp) hjr
    cases hstr : jr.asStr with
    | none =>
      rw [hstr] at hs1
      rw [hs1] at h
      cases h
    | some str =>
      rw [hstr] at hs1
      obtain ⟨hl2, hn⟩ := trch_strRes hs1
      rw [memBytes_length] at hl2 hn
      have hbody : memBytes M0 (q + BitVec.ofNat 32 vp + 1) str.length = str := by
        have e : slice (memBytes M0 (q + BitVec.ofNat 32 vp) vl) 1 str.length =
            memBytes M0 (q + BitVec.ofNat 32 vp + BitVec.ofNat 32 1) str.length :=
          memBytes_slice (by omega)
        exact e.symm.trans (hs2 str hstr)
      rw [hs1] at h
      dsimp only [Option.map] at h
      rw [hbody] at h
      split at h
      · cases h
      rename_i bs hd
      have hb := trch_decode hd
      split at h
      · cases h
      rename_i cert hp
      cases h
      obtain ⟨info, hpc, hi⟩ := rcParse_spec hp
      refine ⟨info, cert, bs, ?_, rfl, hi.shift⟩
      unfold trchCert
      rw [hf]
      change (jr.asStr >>= base64Decode >>= parseCert) = some info
      rw [hstr]
      change (base64Decode str >>= parseCert) = some info
      rw [hb]
      exact hpc

theorem trch_firstStep {fp : Word} {D bs : Bytes} {f : Option RcCert} {hd : Option CertInfo} {cert : RcCert}
    {info : CertInfo} (hF : TrchFirst fp D f hd) (hi : RcInfo (D ++ bs) fp cert info) :
    TrchFirst fp (D ++ bs) (f.or (some cert)) (hd.or (some info)) := by
  cases f with
  | none =>
    cases hd with
    | none => exact hi
    | some _ => exact hF.elim
  | some c0 =>
    cases hd with
    | none => exact hF.elim
    | some i0 => exact RcInfo.app hF

theorem trch_or (hd : Option CertInfo) (i : CertInfo) (is : List CertInfo) :
    (hd.or (some i)).or is.head? = hd.or (i :: is).head? := by
  cases hd <;> rfl

/-- The loop, from the cursor at `s.pos` over the array items `js`, ends
at the array's end only after a step for each item. -/
theorem trch_loop {c : Bool} {M0 : Word → BitVec 8} {fp : Word} {fl : Nat} {ap : Word} {an : Nat} :
    ∀ (js : List Json) (k : Nat) (s s' : RcSt) (hd : Option CertInfo),
      ElementsFrom c (memBytes M0 ap an) s.pos js → rcLoop M0 fp fl ap an k s = .ok s' →
      nextElement (memBytes M0 ap an) s'.pos = some none → TrchFirst fp s.dec s.first hd →
      ∃ infos, js.mapM trchCert = some infos ∧ js.length ≤ k ∧
        (⟨s'.nb, s'.na⟩ : Window) = infos.foldl (fun w c => w.intersect c.window) ⟨s.nb, s.na⟩ ∧
        TrchFirst fp s'.dec s'.first (hd.or infos.head?)
  | [], k, s, s', hd, hE, hL, _, hF => by
    have hs : s' = s := by
      cases k with
      | zero => cases hL; rfl
      | succ k =>
        unfold rcLoop at hL
        change nextElement (memBytes M0 ap an) s.pos = some none at hE
        rw [hE] at hL
        cases hL; rfl
    subst hs
    refine ⟨[], rfl, Nat.zero_le _, rfl, ?_⟩
    cases hd <;> exact hF
  | j :: js, k, s, s', hd, hE, hL, hN, hF => by
    obtain ⟨l, a, hne, hden, hrest⟩ := hE
    cases k with
    | zero =>
      cases hL
      rw [hne] at hN
      cases hN
    | succ k =>
      unfold rcLoop at hL
      rw [hne] at hL
      dsimp only at hL
      split at hL
      · cases hL
      rename_i s1 hs1
      obtain ⟨info, cert, bs, hc, rfl, hi⟩ := trch_step (trch_mem hden) hs1
      obtain ⟨infos, hm, hk, hw, hF'⟩ :=
        trch_loop js k _ s' (hd.or (some info)) hrest hL hN (trch_firstStep hF hi)
      refine ⟨info :: infos, ?_, Nat.succ_le_succ hk, by rw [List.foldl_cons, hi.window]; exact hw, ?_⟩
      · rw [List.mapM_cons, hc, hm]
        rfl
      · rw [← trch_or]; exact hF'

theorem trch_asArr {j : Json} (h : j.asArr.isSome = true) : ∃ js, j = .arr js := by
  cases j with
  | arr js => exact ⟨js, rfl⟩
  | _ => cases h

theorem trch_mapLen {js : List Json} {infos : List CertInfo} (h : js.mapM trchCert = some infos)
    (hne : infos ≠ []) : js ≠ [] := by
  intro e
  subst e
  cases h
  exact hne rfl

/-- When `readChainPos` accepts an entry's bytes, `readChain` accepts the
entry with the same window, and its first certificate is the one that
the model's certificate names in the decoded bytes `s.dec`. -/
theorem readChainPos_spec {c : Bool} {M0 : Word → BitVec 8} {p : Word} {n : Nat} {fp : Word} {fl : Nat}
    {entry : Json} (hj : JVal c (memBytes M0 p n) entry) {cert : RcCert} {s : RcSt}
    (h : readChainPos M0 p n fp fl = .ok (cert, s)) :
    ∃ info, readChain entry = some (info, ⟨s.nb, s.na⟩) ∧ RcInfo s.dec fp cert info := by
  unfold readChainPos at h
  have hF1 := ObjField c _ entry (ascii!"validFor") hj
  cases hvf : entry.field (ascii!"validFor") with
  | none => rw [hvf] at hF1; rw [hF1] at h; cases h
  | some jv =>
  rw [hvf] at hF1
  obtain ⟨x1, x2, hx, hdx⟩ := hF1
  rw [hx] at h
  dsimp only at h
  split at h
  · cases h
  rename_i nb na hvp
  have hw := validForPos_spec (trch_mem hdx)
  rw [hvp] at hw
  have hF2 := ObjField c _ entry (ascii!"certChain") hj
  cases hcc : entry.field (ascii!"certChain") with
  | none => rw [hcc] at hF2; rw [hF2] at h; cases h
  | some jc =>
  rw [hcc] at hF2
  obtain ⟨y1, y2, hy, hdy⟩ := hF2
  rw [hy] at h
  dsimp only at h
  have hF3 := ObjField c _ jc (ascii!"certificates") (trch_mem hdy)
  cases hcs : jc.field (ascii!"certificates") with
  | none => rw [hcs] at hF3; rw [hF3] at h; cases h
  | some jcs =>
  rw [hcs] at hF3
  obtain ⟨z1, z2, hz, hdz⟩ := hF3
  rw [hz] at h
  dsimp only at h
  have hjcs := trch_mem hdz
  generalize hap : p + BitVec.ofNat 32 y1 + BitVec.ofNat 32 z1 = ap at h hjcs
  obtain ⟨-, harr, hpos⟩ := CurOpen c _ jcs ap hjcs
  unfold rcChain at h
  split at h
  · cases h
  rename_i ap' an' pos hco
  have hx' := hpos _ (Or.inr hco)
  rw [memBytes_length] at hx'
  cases hx'
  rw [hco] at harr
  obtain ⟨js, rfl⟩ := trch_asArr harr.symm
  have hE := Elements c _ js hjcs
  split at h
  · cases h
  rename_i s' hl
  unfold rcFinish at h
  split at h
  · cases h
  · cases h
  rename_i hend
  split at h
  · cases h
  rename_i c1 hc1
  cases h
  obtain ⟨infos, hm, hk, hwin, hF⟩ := trch_loop js 4 _ s none hE hl hend trivial
  rw [hc1] at hF
  cases hh : infos.head? with
  | none => rw [hh] at hF; exact hF.elim
  | some info =>
  rw [hh] at hF
  have hne : infos ≠ [] := fun e => by rw [e] at hh; cases hh
  have hjs := trch_mapLen hm hne
  have hlen : (decide (1 ≤ js.length) && decide (js.length ≤ 4)) = true := by
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    exact ⟨List.length_pos_iff.mpr hjs, hk⟩
  refine ⟨info, ?_, hF⟩
  unfold readChain
  rw [hvf]
  change (validFor jv >>= fun w => _) = _
  rw [← hw]
  dsimp only [Except.toOption, Option.map, bind, Option.bind]
  rw [hcc]
  dsimp only [bind, Option.bind]
  rw [hcs]
  dsimp only [bind, Option.bind, Json.asArr]
  rw [hlen]
  dsimp only [require, bind, Option.bind]
  delta trchCert at hm
  dsimp only [bind, Option.bind] at hm
  rw [hm, ite_eq_left (rfl : true = true)]
  dsimp only
  rw [hh, hwin]
  rfl

theorem trch_viewMem {M : Word → BitVec 8} {fp : Word} {D : Bytes} {a l : Nat}
    (hD : memBytes M fp D.length = D) (h : a + l ≤ D.length) :
    rcView D (a, l) = memBytes M (fp + BitVec.ofNat 32 a) l := by
  have e : slice (memBytes M fp D.length) a l = memBytes M (fp + BitVec.ofNat 32 a) l := memBytes_slice h
  rw [hD] at e
  exact e

theorem trch_outDec {M : Word → BitVec 8} {out fr fp : Word} {fl : Nat} {c : RcCert} {s : RcSt}
    (h : RcOut M out fr fp fl (.ok (c, s))) : memBytes M fp s.dec.length = s.dec :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem trch_outLen {M : Word → BitVec 8} {out fr fp : Word} {fl : Nat} {c : RcCert} {s : RcSt}
    (h : RcOut M out fr fp fl (.ok (c, s))) : s.dec.length ≤ fl :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem trch_addNe {fp : Word} {a : Nat} (h0 : fp.toNat ≠ 0) (hw : fp.toNat + a < 2 ^ 32) :
    fp + BitVec.ofNat 32 a ≠ 0 := by
  intro e
  have h := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, Sv.ofNat_toNat_lt (show a < 2 ^ 32 by omega), Nat.mod_eq_of_lt hw,
    show (0 : Word).toNat = 0 from rfl] at h
  omega

/-- `trustedRootReadChain_correct` for an entry whose bytes are the JSON
value `entry`: when `read_chain` returns `Ok`, `readChain entry` accepts
the entry with the window `read_chain` stored, the serial number, issuer,
and subject of its first certificate are the bytes that the stored `Cert`
points to in the buffer, and its P-384 key is the 97 bytes at the stored
key address, or `none` when that address is 0. The converse doesn't hold:
`read_chain` rejects a chain whose decoded certificates overflow the
buffer, which is fail-safe because the device then trusts no key from
that entry. -/
theorem trustedRootReadChain_spec (m : Machine) {sp0 out p fr fp retAddr : Word} {n fl : Nat} {c : Bool}
    {entry : Json}
    (hc : RcCode m.mem) (hpc : m.pc = TRC) (ha0 : reg m a0 = out) (ha1 : reg m a1 = p)
    (ha2 : reg m a2 = BitVec.ofNat 32 n) (ha3 : reg m a3 = fr) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) (hsa : sp0.toNat % 16 = 0)
    (hsl : 0x740 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000)
    (h384 : P3.Fr (sp0 + 0xFFFFF8C0 + BitVec.ofNat 32 0x1A0) 0x420)
    (sRO : Sep (sp0 + 0xFFFFF8C0) 0x740 TVF_RO 0x1400)
    (hoa : out.toNat % 4 = 0) (how : out.toNat + 0x40 ≤ 0x40000000) (sOG : Sep out 0x40 (sp0 + 0xFFFFF8C0) 0x740)
    (sOR : Sep out 0x40 fr 8) (sOB : Sep out 0x40 fp fl)
    (hfa : fr.toNat % 4 = 0) (hfw : fr.toNat + 8 ≤ 0x40000000) (sRG : Sep fr 8 (sp0 + 0xFFFFF8C0) 0x740)
    (sRR : Sep fr 8 TVF_RO 0x1400) (sRB : Sep fr 8 fp fl)
    (hbw : fp.toNat + fl + 14 ≤ 0x40000000) (hb0 : fp.toNat ≠ 0) (sBG : Sep fp (fl + 14) (sp0 + 0xFFFFF8C0) 0x740)
    (sBR : Sep fp fl TVF_RO 0x1400)
    (hfp : memLoad32 m.mem fr = fp) (hfl : memLoad32 m.mem (fr + 4) = BitVec.ofNat 32 fl)
    (hpw : p.toNat + n + 4 ≤ 0x40000000) (hp0 : p.toNat ≠ 0) (sPG : Sep p (n + 4) (sp0 + 0xFFFFF8C0) 0x740)
    (sPR : Sep p n fr 8) (sPB : Sep p n fp fl) (hj : JVal c (memBytes m.mem p n) entry) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q : Fin 32, q.val ∈ trSaved → reg m' q = reg m q) ∧
      rcMem m.mem (sp0 + 0xFFFFF8C0) out fr fp fl (readChainPos m.mem p n fp fl) m'.mem ∧
      ∀ cert s, readChainPos m.mem p n fp fl = .ok (cert, s) →
        ∃ info, readChain entry = some (info, ⟨s.nb, s.na⟩) ∧
          info.serial = memBytes m'.mem cert.serial cert.serialLen ∧
          info.issuer = memBytes m'.mem cert.issuer cert.issuerLen ∧
          info.subject = memBytes m'.mem cert.subject cert.subjectLen ∧
          info.window = ⟨cert.notBefore, cert.notAfter⟩ ∧
          info.p384Key = if cert.key = 0 then none else some (memBytes m'.mem cert.key 0x61) := by
  obtain ⟨m', hs, hpc', hsp', hk, hR, -⟩ := trustedRootReadChain_correct m hc hpc ha0 ha1 ha2 ha3 hra hret hsp hsa
    hsl hsw h384 sRO hoa how sOG sOR sOB hfa hfw sRG sRR sRB hbw hb0 sBG sBR hfp hfl hpw hp0 sPG sPR sPB
  refine ⟨m', hs, hpc', hsp', hk, hR, fun cert s hr => ?_⟩
  obtain ⟨info, hrc, hi⟩ := readChainPos_spec hj hr
  have hO := hR.1
  rw [hr] at hO
  have hD := trch_outDec hO
  have hL := trch_outLen hO
  obtain ⟨⟨a1, h1, b1, e1⟩, ⟨a2, h2, b2, e2⟩, ⟨a3, h3, b3, e3⟩, hw, hk⟩ := hi
  refine ⟨info, hrc, by rw [e1, trch_viewMem hD b1, h1], by rw [e2, trch_viewMem hD b2, h2],
    by rw [e3, trch_viewMem hD b3, h3], hw, ?_⟩
  rcases hk with ⟨a4, h4, b4, e4⟩ | ⟨h4, e4⟩
  · have hne : ¬cert.key = 0 := by
      rw [h4]
      exact trch_addNe hb0 (by omega)
    rw [e4, ite_eq_right hne, trch_viewMem hD b4, h4]
  · rw [e4, h4, ite_eq_left rfl]

end C3.RV32
