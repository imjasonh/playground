import C3BootProofs.Proofs.TrustedRootReadChainRec

/-!
# The loop of `read_chain`

One pass of the loop from its top at 0xFA: `next_element` on the
`certificates` array, then the element's `rawBytes` string, its base64
decoding into the buffer, and `parse_cert` on the decoded bytes, which
ends in `RcCtx.pRec`. Every error reaches its writer with the error that
`rcLoop` gives.
-/

namespace C3.RV32

open C3.Image C3.Json C3.RV32.Dq C3.RV32.P3

set_option maxRecDepth 20000

/-- The `l` bytes at `q` lie in the entry's `n` bytes at `p`. -/
def RcIn (p : Word) (n : Nat) (q : Word) (l : Nat) : Prop := ∃ o, o + l ≤ n ∧ q = p + BitVec.ofNat 32 o

theorem RcIn.sub {p q : Word} {n l c l' : Nat} (h : RcIn p n q l) (hc : c + l' ≤ l) :
    RcIn p n (q + BitVec.ofNat 32 c) l' := by
  obtain ⟨o, ho, rfl⟩ := h
  exact ⟨o + c, by omega, add_ofNat_assoc p o c⟩

/-- `rcLoop` followed by `rcFinish`. -/
def rcLoopFin (M0 : Word → BitVec 8) (fp : Word) (fl : Nat) (ap : Word) (an k : Nat) (s : RcSt) :
    Except (Option Nat) (RcCert × RcSt) :=
  match rcLoop M0 fp fl ap an k s with
  | .error e => .error e
  | .ok s => rcFinish M0 ap an s

/-- The rest of the loop after one certificate's step. -/
def rcAfter (M0 : Word → BitVec 8) (fp : Word) (fl : Nat) (ap : Word) (an k : Nat)
    (x : Except (Option Nat) RcSt) : Except (Option Nat) (RcCert × RcSt) :=
  match x with
  | .error e => .error e
  | .ok s => rcLoopFin M0 fp fl ap an k s

theorem rc_nextBd {d : Bytes} {pos st len after : Nat} (h : nextElement d pos = some (some (st, len, after))) :
    st + len ≤ d.length ∧ after ≤ d.length := by
  unfold nextElement at h
  split at h
  · cases h
  · cases hr : readItem d pos with
    | none => rw [hr] at h; cases h
    | some x =>
      rw [hr] at h
      cases h
      have hb := readItem_bd hr
      unfold readItem at hr
      cases hv : valueEnd d pos with
      | none => rw [hv] at hr; cases hr
      | some e =>
        rw [hv] at hr
        cases hr
        have := valueEnd_bd hv
        refine ⟨by omega, ?_⟩
        unfold itemTail
        split
        · next hc => have := skipWs_le d (skipWs d e + 1); omega
        · have := skipWs_le d e; omega

theorem rc_strBd {p b : Word} {d : Bytes} {bl : Nat} (h : strRes p d = some (b, bl)) :
    b = p + BitVec.ofNat 32 1 ∧ 1 + bl ≤ d.length := by
  unfold strRes at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; exact ⟨rfl, by omega⟩

/-- `rcStep` after the `rawBytes` string: the decoding and `parse_cert`. -/
def rcDecStep (M0 : Word → BitVec 8) (fp : Word) (fl : Nat) (b : Word) (bl after : Nat) (s : RcSt) :
    Except (Option Nat) RcSt :=
  match trDecodeRes (base64Decode (memBytes M0 b bl)) (fl - s.dec.length) with
  | none => .error (some (bdiErr (memBytes M0 b bl) (fl - s.dec.length)))
  | some bs =>
    match rcParse bs (fp + BitVec.ofNat 32 s.dec.length) with
    | .error e => .error e
    | .ok c => .ok ⟨after, s.dec ++ bs, s.first.or (some c), max s.nb c.notBefore, min s.na c.notAfter⟩

theorem rcStep_eq (M0 : Word → BitVec 8) (fp : Word) (fl : Nat) (q : Word) (l after : Nat) (s : RcSt) :
    rcStep M0 fp fl q l after s =
      match objField (memBytes M0 q l) (ascii!"rawBytes") with
      | .error e => .error (some e)
      | .ok x =>
        match strRes (q + BitVec.ofNat 32 x.1) (memBytes M0 (q + BitVec.ofNat 32 x.1) x.2) with
        | none => .error (some 0x21)
        | some (b, bl) => rcDecStep M0 fp fl b bl after s := rfl

theorem rc_decLe {d : Option Bytes} {fl : Nat} {bs : Bytes} (h : trDecodeRes d fl = some bs) : bs.length ≤ fl := by
  cases d with
  | none => cases h
  | some d =>
    simp only [trDecodeRes, Option.bind_some] at h
    split at h
    · next hl => cases h; exact hl
    · cases h

theorem rc_a4 (B : Word) (c : Nat) : B + BitVec.ofNat 32 c + 4 = B + BitVec.ofNat 32 (c + 4) := add_ofNat_assoc B c 4

theorem rc_a8 (B : Word) (c : Nat) : B + BitVec.ofNat 32 c + 8 = B + BitVec.ofNat 32 (c + 8) := add_ofNat_assoc B c 8

/-- Memory that kept the frame words from `F + 0x24` to `F + 0x60`. -/
def RcFL (F : Word) (M M' : Word → BitVec 8) : Prop :=
  ∀ j, 0x24 ≤ j → j < 0x60 → M' (F + BitVec.ofNat 32 j) = M (F + BitVec.ofNat 32 j)

theorem RcFL.trans {F : Word} {M M1 M2 : Word → BitVec 8} (h1 : RcFL F M M1) (h2 : RcFL F M1 M2) : RcFL F M M2 :=
  fun j a b => (h2 j a b).trans (h1 j a b)

theorem RcFL.ld {F : Word} {M M' : Word → BitVec 8} (h : RcFL F M M') {c : Nat} (hc : 0x24 ≤ c ∧ c + 4 ≤ 0x60) :
    memLoad32 M' (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (by omega) (by omega)

theorem RcFL.first {F : Word} {M M' : Word → BitVec 8} {c : Option RcCert} (h : RcFL F M M')
    (hF : RcFirst M (F + BitVec.ofNat 32 0x30) c) : RcFirst M' (F + BitVec.ofNat 32 0x30) c :=
  hF.copy fun k _ hk => by rw [add_ofNat_assoc]; exact h.ld ⟨by omega, by omega⟩

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

theorem RcCtx.flKB (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {lo : Nat}
    (h : RcKB G lo M M') (hlo : lo ≤ 0x24) : RcFL F M M' :=
  fun j a b => h _ (by
      rw [X.fG]
      have s := sep_offsets G (c := 0) (n := 0x5C0 + lo) (d := 0x5C0 + j) (k := 1) (Or.inl (by omega)) (by omega)
        (by omega)
      rwa [add_ofNat_zero] at s)
    (by rw [X.fG]; exact sep_offsets G (by omega) (by omega) (by omega))

theorem RcCtx.flKeep (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} (h : RcKeep G M M') :
    RcFL F M M' :=
  X.flKB (lo := 0) h.kb (by decide)

theorem RcCtx.inW (X : RcCtx M0 G F out fr fp fl p n g0) {q : Word} {l : Nat} (h : RcIn p n q l) :
    q.toNat ≠ 0 ∧ q.toNat + l + 4 ≤ 0x40000000 := by
  obtain ⟨o, ho, rfl⟩ := h
  have pw := X.pw
  have p0 := X.p0
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  constructor <;> omega

theorem RcCtx.inG (X : RcCtx M0 G F out fr fp fl p n g0) {q : Word} {l : Nat} (h : RcIn p n q l) :
    Sep q l G 0x740 := by
  obtain ⟨o, ho, rfl⟩ := h
  exact X.pg.sub (by omega)

theorem RcCtx.inFr (X : RcCtx M0 G F out fr fp fl p n g0) {q : Word} {l : Nat} (h : RcIn p n q l) :
    Sep q l fr 8 := by
  obtain ⟨o, ho, rfl⟩ := h
  exact X.pfr.sub (by omega)

theorem RcCtx.inFp (X : RcCtx M0 G F out fr fp fl p n g0) {q : Word} {l : Nat} (h : RcIn p n q l) :
    Sep q l fp fl := by
  obtain ⟨o, ho, rfl⟩ := h
  exact X.pb.sub (by omega)

theorem RcCtx.inM (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {q : Word} {l : Nat}
    (hI : RcMemInv M0 G F fr fp fl g0 M) (h : RcIn p n q l) : memBytes M q l = memBytes M0 q l :=
  memBytes_congr fun _ hj => hI.1 _ (sep_pt (X.inG h).symm hj).symm (sep_pt (X.inFr h).symm hj).symm
    (sep_pt (X.inFp h).symm hj).symm

theorem RcCtx.flDec (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {o fl' : Nat}
    (hol : o + fl' ≤ fl)
    (h : ∀ x, Sep (G + BitVec.ofNat 32 0x550) 0x70 x 1 → Sep (F + BitVec.ofNat 32 0xD0) 8 x 1 → Sep fr 8 x 1 →
      Sep (fp + BitVec.ofNat 32 o) fl' x 1 → M' x = M x) : RcFL F M M' :=
  fun j a b => h _ (by rw [X.fG]; exact X.gsep (Or.inl (by omega)) (by omega) (by omega))
    (by rw [X.fG, X.fG]; exact X.gsep (Or.inr (by omega)) (by omega) (by omega))
    (by rw [X.fG]; exact X.frg.subR (by omega))
    (by rw [X.fG]; exact (X.bg.sub (c := o) (l := fl') (by omega)).subR (by omega))

/-- The buffer after `decode` appended `bs` to the decoded certificates. -/
theorem RcCtx.bufDec (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {dec bs : Bytes}
    (hB : RcBuf M fr fp fl dec)
    (hO : TrDecOut M' (F + BitVec.ofNat 32 0xD0) fr (fp + BitVec.ofNat 32 dec.length) (fl - dec.length) (some bs))
    (hl : bs.length ≤ fl - dec.length)
    (h : ∀ x, Sep (G + BitVec.ofNat 32 0x550) 0x70 x 1 → Sep (F + BitVec.ofNat 32 0xD0) 8 x 1 → Sep fr 8 x 1 →
      Sep (fp + BitVec.ofNat 32 dec.length) (fl - dec.length) x 1 → M' x = M x) :
    RcBuf M' fr fp fl (dec ++ bs) := by
  have bw := X.bw
  have h1 := hB.1
  refine ⟨by rw [List.length_append]; omega, ?_, ?_, ?_⟩
  · rw [hO.2.2.1, add_ofNat_assoc, List.length_append]
  · rw [hO.2.2.2.1, List.length_append, Nat.sub_sub]
  · rw [List.length_append, memBytes_split, hO.2.2.2.2]
    congr 1
    refine (memBytes_congr fun j hj => h _ ?_ ?_ ?_ ?_).trans hB.2.2.2
    · exact (sep_pt (X.bg.subR (c := 0x550) (l := 0x70) (by decide)).symm (by omega)).symm
    · exact (sep_pt (by rw [X.fG]; exact (X.bg.subR (c := 0x5C0 + 0xD0) (l := 8) (by decide)).symm) (by omega)).symm
    · exact (sep_pt X.frp (by omega)).symm
    · have := sep_offsets fp (c := dec.length) (n := fl - dec.length) (d := j) (k := 1) (Or.inr (by omega))
        (by omega) (by omega)
      exact this

/-- From 0x13A: the `rawBytes` string's contents, the `bl` bytes at `b`,
in `a1` and at `F + 0x60`. Decodes them into the buffer after the
decoded certificates, then runs `parse_cert` on them through 0x308. -/
theorem RcCtx.pDec (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {r : Except (Option Nat) (RcCert × RcSt)} {ap b : Word} {an k after bl nb na : Nat} {dec : Bytes}
    {first : Option RcCert}
    (hInv : RcLoopInv M0 G F out fr fp fl g0 ap an k ⟨after, dec, first, nb, na⟩ M f) (hk : 1 ≤ k ∧ k ≤ 4)
    (hb : RcIn p n b bl) (ha1 : f a1 = b) (h64 : memLoad32 M (F + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 bl)
    (hr : r = rcAfter M0 fp fl ap an (k - 1) (rcDecStep M0 fp fl b bl after ⟨after, dec, first, nb, na⟩))
    (hIH : ∀ s' M' f', RcLoopInv M0 G F out fr fp fl g0 ap an (k - 1) s' M' f' → k - 1 ≠ 0 →
      r = rcLoopFin M0 fp fl ap an (k - 1) s' →
      WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M' 0xFA f')
    (hFin : ∀ s' M' f' k', RcLoopInv M0 G F out fr fp fl g0 ap an k' s' M' f' → r = rcFinish M0 ap an s' →
      WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M' 0x4D8 f') :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x13A f := by
  obtain ⟨hR, hI, hW, h20, h9, h23, h8, h22, hm24, hm28, hm2C, hpos, hF, hB⟩ := hInv
  dsimp only at hW hm2C hpos hF hB
  obtain ⟨_, hbw⟩ := X.inW hb
  have bw := X.bw
  have b0 := X.b0
  have hdl := hB.1
  refine WP.lw trc_at_13a (by rw [hR.2.1]; exact X.fal (c := 0x64) (by decide)) ?_; wn
  refine WP.aluImm trc_at_13c ?_; wn
  refine WP.alu trc_at_13e ?_; wn
  refine X.callDec (o := dec.length) (fl' := fl - dec.length) (by rc_r hR) hI (by trsimp; rw [hR.2.1]; rfl)
    (by trsimp; exact ha1) (by trsimp; rw [hR.2.1]; exact h64)
    (by trsimp; (try rw [rc_x0 hR.1]); exact hR.2.2.2.1) hB.2.1 hB.2.2.1 (by omega) (by omega) (X.inG hb)
    (X.inFp hb) (X.inM hI hb) (fun m2 hI2 hDE => ?_)
  obtain ⟨hD, hDe⟩ := hDE
  rcases hdr : trDecodeRes (base64Decode (memBytes M0 b bl)) (fl - dec.length) with _ | bs
  · rw [hdr] at hD
    have hD0 : memLoad32 m2.mem (F + 0xD0) = 0 := hD.1.1
    refine WP.lw trc_at_148 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xD0) (by decide)) ?_; wn
    refine WP.branch trc_at_14a (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR.2.1, hD0]; decide)); wn
    exact X.e4c2 (by rw [hr]; simp only [rcDecStep, hdr]; rfl) (by rc_r hR) hI2 (fun _ hb => by
      cases hb; exact hDe hdr)
  · rw [hdr] at hD
    have hl := rc_decLe hdr
    have hFL : RcFL F M m2.mem := X.flDec (o := dec.length) (fl' := fl - dec.length) (by omega) hD.2
    have hB2 := X.bufDec hB hD.1 hl hD.2
    have hBp : (fp + BitVec.ofNat 32 dec.length).toNat = fp.toNat + dec.length := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine X.pOuter (B := fp + BitVec.ofNat 32 dec.length) (L := bs)
      (kc := BitVec.ofNat 32 k) ?_ hI2 (fun _ _ => rfl)
      ⟨hD.1.2.2.2.2, X.bg.sub (by omega), by rw [hBp]; omega, by rw [hBp]; omega⟩ hD.1.1
      (by rw [← rc_a4]; exact hD.1.2.1) (by trsimp; exact h9) (by trsimp; exact h20) (by trsimp; exact h22)
      (by trsimp; exact h23) (fun c hc => ?_) (fun e he => by rw [hr]; simp only [rcDecStep, hdr, he]; rfl)
    · rc_r hR
    · intro M' f' hR' hI' hKB hK' h20' h22' hm18 hm1C hm10 hm14 h9' h8' h23' h18' hcb hca ha1' hm20 hs0
      have hFL' : RcFL F M M' := hFL.trans (X.flKB hKB (Nat.le_refl _))
      exact X.pRec hR' hI' (RcWin.keep (by rc_w hW) hK') h20' h22' hm18 hm1C hm10 hm14 h9' h8' h23' h18' hcb hca
        ha1' hs0 hm20 hk ((hFL'.ld ⟨by decide, by decide⟩).trans hm24) ((hFL'.ld ⟨by decide, by decide⟩).trans hm28)
        ((hFL'.ld ⟨by decide, by decide⟩).trans hm2C) hpos (hFL'.first hF) (X.bufG hB2 (hKB.g (by decide)))
        (fun M'' f'' hinv hk0 => hIH _ M'' f'' hinv hk0 (by rw [hr]; simp only [rcDecStep, hdr, hc]; rfl))
        (fun M'' f'' hinv hk0 => hFin _ M'' f'' _ hinv (by
          rw [hr]; simp only [rcDecStep, hdr, hc, rcAfter, rcLoopFin, hk0, rcLoop]))

/-- The registers that `RcLoopInv` names. -/
abbrev rcLR : List Nat := [8, 9, 19, 20, 21, 22, 23, 24, 27]

/-- `RcLoopInv` with the cursor's position moved to `after`. -/
theorem RcCtx.invPos (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {f f' : Fin 32 → Word}
    {ap : Word} {an k after : Nat} {s : RcSt} (h : RcLoopInv M0 G F out fr fp fl g0 ap an k s M f)
    (hI : RcMemInv M0 G F fr fp fl g0 M')
    (hFL : ∀ j, 0x24 ≤ j → j < 0x60 → (j < 0x2C ∨ 0x30 ≤ j) →
      M' (F + BitVec.ofNat 32 j) = M (F + BitVec.ofNat 32 j))
    (hG : RcG G M M') (h2C : memLoad32 M' (F + BitVec.ofNat 32 0x2C) = BitVec.ofNat 32 after) (ha : after < 2 ^ 32)
    (hR : RcRegs F out fr g0 f') (hK : RcK rcLR f f') :
    RcLoopInv M0 G F out fr fp fl g0 ap an k ⟨after, s.dec, s.first, s.nb, s.na⟩ M' f' := by
  obtain ⟨_, _, hW, h20, h9, h23, h8, h22, hm24, hm28, _, _, hF, hB⟩ := h
  have ld : ∀ c, 0x24 ≤ c → c + 4 ≤ 0x60 → (c + 4 ≤ 0x2C ∨ 0x30 ≤ c) →
      memLoad32 M' (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) :=
    fun c a b d => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hFL _ (by omega) (by omega) (by omega)
  exact ⟨hR, hI, hW.keep (hK.mono (by decide)), (hK 20 (by decide)).trans h20,
    (hK 9 (by decide)).trans h9, (hK 23 (by decide)).trans h23, (hK 8 (by decide)).trans h8,
    (hK 22 (by decide)).trans h22, (ld 0x24 (by decide) (by decide) (by decide)).trans hm24,
    (ld 0x28 (by decide) (by decide) (by decide)).trans hm28, h2C, ha,
    hF.copy fun k _ hk => by rw [add_ofNat_assoc]; exact ld _ (by omega) (by omega) (Or.inr (by omega)),
    X.bufG hB hG⟩

theorem RcCtx.invMem (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {f f' : Fin 32 → Word}
    {ap : Word} {an k : Nat} {s : RcSt} (h : RcLoopInv M0 G F out fr fp fl g0 ap an k s M f)
    (hI : RcMemInv M0 G F fr fp fl g0 M') (hFL : RcFL F M M') (hG : RcG G M M') (hR : RcRegs F out fr g0 f')
    (hK : RcK rcLR f f') : RcLoopInv M0 G F out fr fp fl g0 ap an k s M' f' :=
  X.invPos h hI (fun j a b _ => hFL j a b) hG ((hFL.ld ⟨by decide, by decide⟩).trans h.2.2.2.2.2.2.2.2.2.2.1)
    h.2.2.2.2.2.2.2.2.2.2.2.1 hR hK

theorem RcCtx.invStep (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {f f' : Fin 32 → Word}
    {ap : Word} {an k : Nat} {s : RcSt} (h : RcLoopInv M0 G F out fr fp fl g0 ap an k s M f)
    (hI : RcMemInv M0 G F fr fp fl g0 M') (hKp : RcKeep G M M') (hR : RcRegs F out fr g0 f')
    (hK : RcK rcLR f f') : RcLoopInv M0 G F out fr fp fl g0 ap an k s M' f' :=
  X.invMem h hI (X.flKeep hKp) hKp.g hR hK

theorem RcCtx.invR {M : Word → BitVec 8} {f : Fin 32 → Word} {ap : Word} {an k : Nat} {s : RcSt}
    (h : RcLoopInv M0 G F out fr fp fl g0 ap an k s M f) : RcRegs F out fr g0 f := h.1

/-- From 0x122: `field` left the value of `rawBytes` in the element of
`len` bytes at `q` at `F + 0xE0`. Takes its string, then decodes it at
0x13A. -/
theorem RcCtx.pStr (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {r : Except (Option Nat) (RcCert × RcSt)} {ap q : Word} {an k after len nb na : Nat} {dec : Bytes}
    {first : Option RcCert}
    (hInv : RcLoopInv M0 G F out fr fp fl g0 ap an k ⟨after, dec, first, nb, na⟩ M f) (hk : 1 ≤ k ∧ k ≤ 4)
    (hq : RcIn p n q len)
    (hFR : FieldRes M M (F + BitVec.ofNat 32 0xE0) (fieldRes q (objField (memBytes M0 q len) (ascii!"rawBytes"))))
    (hr : r = rcAfter M0 fp fl ap an (k - 1) (rcStep M0 fp fl q len after ⟨after, dec, first, nb, na⟩))
    (hIH : ∀ s' M' f', RcLoopInv M0 G F out fr fp fl g0 ap an (k - 1) s' M' f' → k - 1 ≠ 0 →
      r = rcLoopFin M0 fp fl ap an (k - 1) s' →
      WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M' 0xFA f')
    (hFin : ∀ s' M' f' k', RcLoopInv M0 G F out fr fp fl g0 ap an k' s' M' f' → r = rcFinish M0 ap an s' →
      WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M' 0x4D8 f') :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x122 f := by
  have hR := hInv.1
  have hI := hInv.2.1
  refine WP.lw trc_at_122 (by rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
  rcases hof : objField (memBytes M0 q len) (ascii!"rawBytes") with e | ⟨a, l1⟩
  · rw [hof] at hFR
    change FieldRes M M _ (.error e) at hFR
    have hE0 : memLoad32 M (F + 0xE0) = 0 := hFR.2.1
    refine WP.branch trc_at_124 (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR.2.1, hE0]; decide)); wn
    refine X.e4fc (by rw [hr, rcStep_eq]; simp only [hof]; rfl) (by rc_r hR) hI (fun b hb => ?_)
    cases hb
    have := hFR.2.2; rw [rc_a4] at this; exact this
  · rw [hof] at hFR
    change FieldRes M M _ (.ok (q + BitVec.ofNat 32 a, l1)) at hFR
    have hv := tvf_field_val hof
    rw [memBytes_length] at hv
    have hqa : RcIn p n (q + BitVec.ofNat 32 a) l1 := hq.sub (by omega)
    obtain ⟨hqa0, hqaw⟩ := X.inW hqa
    have hE0 : memLoad32 M (F + 0xE0) = q + BitVec.ofNat 32 a := hFR.2.1
    have hqa0' : q + BitVec.ofNat 32 a ≠ 0 := fun h => hqa0 (by rw [h]; rfl)
    refine WP.branch trc_at_124 (fun ht => absurd ht (by trsimp; rw [hR.2.1, hE0, rck_beqF hqa0']; decide))
      (fun _ => ?_); wn
    refine WP.lw trc_at_128 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xE4) (by decide)) ?_; wn
    refine WP.aluImm trc_at_12a ?_; wn
    refine X.callStr hI (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; exact hE0)
      (by trsimp; rw [hR.2.1]; have := hFR.2.2; rw [rc_a4] at this; exact this) (by omega) (X.inM hI hqa) (fun m2 hK2 hI2 hSR => ?_)
    refine WP.lw trc_at_134 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0x60) (by decide)) ?_; wn
    rcases hs : strRes (q + BitVec.ofNat 32 a) (memBytes M0 (q + BitVec.ofNat 32 a) l1) with _ | ⟨b, bl⟩
    · rw [hs] at hSR
      have h60 : memLoad32 m2.mem (F + 0x60) = 0 := hSR.2.1
      refine WP.branch trc_at_136 (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR.2.1, h60]; decide)); wn
      refine X.e480 (by rw [hr, rcStep_eq]; simp only [hof, hs]; rfl) (by rc_r hR) hI2 (fun b hb => ?_)
      cases hb
      have := hSR.2.2; rw [rc_a4] at this; exact this
    · rw [hs] at hSR
      obtain ⟨hbq, hbl⟩ := rc_strBd hs
      rw [memBytes_length] at hbl
      have hb : RcIn p n b bl := by rw [hbq]; exact hqa.sub (by omega)
      obtain ⟨hb0, _⟩ := X.inW hb
      have hb0' : b ≠ 0 := fun h => hb0 (by rw [h]; rfl)
      have h60 : memLoad32 m2.mem (F + 0x60) = b := hSR.2.1
      refine WP.branch trc_at_136 (fun ht => absurd ht (by trsimp; rw [hR.2.1, h60, rck_beqF hb0']; decide))
        (fun _ => ?_); wn
      exact X.pDec (X.invStep hInv hI2 hK2 (by rc_r hR) (by rc_k (fun _ _ => rfl))) hk hb (by trsimp; rw [hR.2.1]; exact h60)
        (by have := hSR.2.2; rw [rc_a4] at this; exact this) (by rw [hr, rcStep_eq]; simp only [hof, hs]) hIH hFin

theorem rcLoopFin_step {M0 : Word → BitVec 8} {fp ap : Word} {fl an k st len after : Nat} {s : RcSt}
    (h : nextElement (memBytes M0 ap an) s.pos = some (some (st, len, after))) :
    rcLoopFin M0 fp fl ap an (k + 1) s =
      rcAfter M0 fp fl ap an k (rcStep M0 fp fl (ap + BitVec.ofNat 32 st) len after s) := by
  simp only [rcLoopFin, rcLoop, h, rcAfter]
  cases rcStep M0 fp fl (ap + BitVec.ofNat 32 st) len after s <;> rfl

/-- The loop's top at 0xFA, with `k` certificates left to read from the
array of `an` bytes at `ap`: `next_element`, then the element's
`rawBytes` at 0x122, the error writer at 0x68 when the array is bad, or
0x4D8 when it ends. -/
theorem RcCtx.pFront (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {r : Except (Option Nat) (RcCert × RcSt)} {ap : Word} {an k : Nat} {s : RcSt}
    (hInv : RcLoopInv M0 G F out fr fp fl g0 ap an k s M f) (hk : 1 ≤ k ∧ k ≤ 4) (hA : RcIn p n ap an)
    (hr : r = rcLoopFin M0 fp fl ap an k s)
    (hIH : ∀ s' M' f', RcLoopInv M0 G F out fr fp fl g0 ap an (k - 1) s' M' f' → k - 1 ≠ 0 →
      r = rcLoopFin M0 fp fl ap an (k - 1) s' →
      WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M' 0xFA f')
    (hFin : ∀ s' M' f' k', RcLoopInv M0 G F out fr fp fl g0 ap an k' s' M' f' → r = rcFinish M0 ap an s' →
      WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M' 0x4D8 f') :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0xFA f := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hInv0 := hInv
  obtain ⟨hR, hI, _, _, _, _, h8, _, hm24, hm28, hm2C, hpos, _, _⟩ := hInv
  obtain ⟨hA0, hAw⟩ := X.inW hA
  refine WP.aluImm trc_at_fa ?_; wn
  refine WP.aluImm trc_at_fc ?_; wn
  refine X.callNext (off := 0xFE) trc_at_fe trc_at_102 (by decide) (by decide) (by rc_r hR) hI
    (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl) hm24 hm28 hm2C (by omega) hpos hA0 (by omega)
    (X.inG hA) (X.inM hI hA) (fun m2 hI2 hE => ?_)
  obtain ⟨M1, hK1, hER⟩ := hE
  refine WP.lbu trc_at_106 ?_; wn
  rcases hn : nextElement (memBytes M0 ap an) s.pos with _ | _ | ⟨st, len, after⟩
  · rw [hn] at hER
    change ElemRes M1 m2.mem _ _ none at hER
    have hE0 : m2.mem (F + 0xE0) = 1 := hER.2.1
    refine WP.branch trc_at_10a (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR.2.1, hE0]; decide)); wn
    exact X.e068 (e := some 0x20) (by rw [hr]; simp only [rcLoopFin, rcLoop, hn]) (by rc_r hR) hI2 (fun b hb => by
      cases hb; exact (congrArg m2.mem (add_ofNat_assoc F 0xE0 1)).symm.trans hER.2.2)
  · rw [hn] at hER
    change ElemRes M1 m2.mem _ _ (some none) at hER
    have hE0 : m2.mem (F + 0xE0) = 0 := hER.2.1
    have hE4 : memLoad32 m2.mem (F + 0xE4) = 0 := by have := hER.2.2; rw [rc_a4] at this; exact this
    refine WP.branch trc_at_10a (fun ht => absurd ht (by trsimp; rw [hR.2.1, hE0]; decide)) (fun _ => ?_); wn
    refine WP.lw trc_at_10c (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xE4) (by decide)) ?_; wn
    refine WP.branch trc_at_10e (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR.2.1, hE4]; decide)); wn
    have hFL : RcFL F M m2.mem := (X.flKeep hK1).trans fun j a b => hER.1 _ (by
      rw [X.fG, X.fG]; exact X.gsep (Or.inl (by omega)) (by omega) (by omega))
    have hG : RcG G M m2.mem := hK1.g.trans fun x hx => hER.1 x (by rw [X.fG]; exact sep_in hx.symm (by decide))
    exact hFin s m2.mem _ (k' + 1) (X.invMem hInv0 hI2 hFL hG (by rc_r hR) (by rc_k (fun _ _ => rfl)))
      (by rw [hr]; simp only [rcLoopFin, rcLoop, hn])
  · rw [hn] at hER
    change ElemRes M1 m2.mem _ _ (some (some (ap + BitVec.ofNat 32 st, len, after))) at hER
    obtain ⟨hbd1, hbd2⟩ := rc_nextBd hn
    rw [memBytes_length] at hbd1 hbd2
    have hq : RcIn p n (ap + BitVec.ofNat 32 st) len := hA.sub (by omega)
    obtain ⟨hq0, hqw⟩ := X.inW hq
    have hq0' : ap + BitVec.ofNat 32 st ≠ 0 := fun h => hq0 (by rw [h]; rfl)
    have hE0 : m2.mem (F + 0xE0) = 0 := hER.2.1
    have hE4 : memLoad32 m2.mem (F + 0xE4) = ap + BitVec.ofNat 32 st := by
      have := hER.2.2.1; rw [rc_a4] at this; exact this
    have hE8 : memLoad32 m2.mem (F + 0xE8) = BitVec.ofNat 32 len := by
      have := hER.2.2.2.1; rw [rc_a8] at this; exact this
    have e2C : F + BitVec.ofNat 32 0x24 + 8 = F + BitVec.ofNat 32 0x2C := add_ofNat_assoc F 0x24 8
    have hO := hER.1
    have h2C := hER.2.2.2.2
    rw [e2C] at hO h2C
    refine WP.branch trc_at_10a (fun ht => absurd ht (by trsimp; rw [hR.2.1, hE0]; decide)) (fun _ => ?_); wn
    refine WP.lw trc_at_10c (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xE4) (by decide)) ?_; wn
    refine WP.branch trc_at_10e (fun ht => absurd ht (by trsimp; rw [hR.2.1, hE4, rck_beqF hq0']; decide))
      (fun _ => ?_); wn
    refine WP.lw trc_at_112 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xE8) (by decide)) ?_; wn
    refine WP.aluImm trc_at_114 ?_; wn
    refine WP.aluImm trc_at_116 ?_; wn
    refine WP.alu trc_at_118 ?_; wn
    refine X.callField (off := 0x11A) (c := 0xE0) trc_at_11a trc_at_11e (by decide) (by decide) (by rc_r hR) hI2
      (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; exact hE4)
      (by trsimp; rw [hR.2.1]; exact hE8) (by trsimp; (try rw [rc_x0 hR.1]); exact h8)
      (by trsimp; try rfl) hq0 (by omega) (by decide) (X.inG hq)
      (rc_roSub X.ro ⟨by decide, by decide⟩).symm (X.inM hI2 hq) (X.codeAt hI2).kr (fun m3 hK3 hI3 hFR => ?_)
    have hFLx : ∀ j, 0x24 ≤ j → j < 0x60 → (j < 0x2C ∨ 0x30 ≤ j) →
        m3.mem (F + BitVec.ofNat 32 j) = M (F + BitVec.ofNat 32 j) := fun j a b d =>
      ((X.flKeep hK3) j a b).trans ((hO _ (by rw [X.fG, X.fG]; exact X.gsep (Or.inl (by omega)) (by omega) (by omega))
        (by rw [X.fG, X.fG]; exact X.gsep (by omega) (by omega) (by omega))).trans ((X.flKeep hK1) j a b))
    have hG : RcG G M m3.mem := (hK1.g.trans fun x hx => hO x (by rw [X.fG]; exact sep_in hx.symm (by decide))
      (by rw [X.fG]; exact sep_in hx.symm (by decide))).trans hK3.g
    exact X.pStr (X.invPos hInv0 hI3 hFLx hG ((X.flKeep hK3).ld ⟨by decide, by decide⟩ |>.trans h2C) (by omega)
      (by rc_r hR) (by rc_k (fun _ _ => rfl))) hk hq hFR (by rw [hr, rcLoopFin_step hn]; rfl) hIH hFin

end

end C3.RV32
