import C3BootProofs.Proofs.TrustedRootReadChainFin

/-!
# The start of `read_chain`

The block from 0x3C to 0xF9 finds the entry's `validFor` field and reads
the window from it, finds `certChain.certificates`, opens that array, and
sets up the loop's registers and the array cursor at `F + 0x24`. It ends
at the loop's top, 0xFA, or at one of the error writers.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

/-- `read_chain` from the `certChain` field on, with the window `nb`–`na`. -/
def rcCerts (M0 : Word → BitVec 8) (p : Word) (n : Nat) (fp : Word) (fl nb na : Nat) :
    Except (Option Nat) (RcCert × RcSt) :=
  match objField (memBytes M0 p n) (ascii!"certChain") with
  | .error e => .error (some e)
  | .ok y =>
    match objField (memBytes M0 (p + BitVec.ofNat 32 y.1) y.2) (ascii!"certificates") with
    | .error e => .error (some e)
    | .ok z => rcChain M0 fp fl (p + BitVec.ofNat 32 y.1 + BitVec.ofNat 32 z.1) z.2 nb na

theorem rc_curOpen {q q' : Word} {d : Bytes} {an pos : Nat} (h : curOpen 91 q d = some (q', an, pos)) :
    q' = q ∧ an = d.length ∧ pos ≤ d.length ∧ 1 ≤ d.length := by
  unfold curOpen at h
  by_cases h1 : d.length = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] at h; cases h
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at h
  by_cases h2 : d.getD 0 0 ≠ 91
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)] at h; cases h
  rw [ite_eq_right_of_eq_false _ _ (eq_false h2)] at h
  cases h
  have := skipWs_le d 1
  exact ⟨rfl, rfl, by omega, by omega⟩

/-- Proves a register value that a run of `upd` and `clob` determines. -/
macro "rc_reg" : tactic => `(tactic| first | rfl | (trsimp <;> first | rfl | decide))

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

theorem RcCtx.inG4 (X : RcCtx M0 G F out fr fp fl p n g0) {q : Word} {l : Nat} (h : RcIn p n q l) :
    Sep q (l + 4) G 0x740 := by
  obtain ⟨o, ho, rfl⟩ := h
  exact X.pg.sub (by omega)

theorem RcCtx.inSelf (_X : RcCtx M0 G F out fr fp fl p n g0) : RcIn p n p n :=
  ⟨0, by omega, (add_ofNat_zero p).symm⟩

theorem RcCtx.fsep (X : RcCtx M0 G F out fr fp fl p n g0) {c k d l : Nat} (h : c + k ≤ d ∨ d + l ≤ c)
    (hc : c + k ≤ 0x180) (hd : d + l ≤ 0x180) : Sep (F + BitVec.ofNat 32 c) k (F + BitVec.ofNat 32 d) l := by
  rw [X.fG, X.fG]; exact X.gsep (by omega) (by omega) (by omega)

/-- A byte inside the range of `k` bytes at `F + c` is apart from the
range of `l` bytes at `F + d` when that range is apart from it. -/
theorem RcCtx.fsepIn (X : RcCtx M0 G F out fr fp fl p n g0) {c k d l : Nat} {x : Word}
    (hx : Sep (F + BitVec.ofNat 32 c) k x 1) (hdl : c ≤ d ∧ d + l ≤ c + k) : Sep (F + BitVec.ofNat 32 d) l x 1 := by
  rw [X.fG] at hx ⊢; exact rc_gin hx (by omega) (by omega)

/-- The memory after the cursor stores at 0xD8, 0xDA, and 0xDE, which
follow the copy of the 7 bytes at `F + 0xE5` to `F + 0x29`. -/
theorem RcCtx.hdMem (X : RcCtx M0 G F out fr fp fl p n g0) {M m3 M5 : Word → BitVec 8} {q : Word}
    (hc : ∀ x, Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 →
      m3 x = copyBytes M (F + BitVec.ofNat 32 0x29) (F + BitVec.ofNat 32 0xE5) 7 x)
    (h5 : M5 = memStore32 (memStore8 (memStore32 m3 (F + BitVec.ofNat 32 0x24) q) (F + BitVec.ofNat 32 0x28)
      (M (F + BitVec.ofNat 32 0xE4))) (F + BitVec.ofNat 32 0x30) 0) :
    (∀ x, Sep (F + BitVec.ofNat 32 0x24) 0x10 x 1 → M5 x = m3 x) ∧
      memLoad32 M5 (F + BitVec.ofNat 32 0x24) = q ∧
      memLoad32 M5 (F + BitVec.ofNat 32 0x28) = memLoad32 M (F + BitVec.ofNat 32 0xE4) ∧
      memLoad32 M5 (F + BitVec.ofNat 32 0x2C) = memLoad32 M (F + BitVec.ofNat 32 0xE8) ∧
      memLoad32 M5 (F + BitVec.ofNat 32 0x30) = 0 := by
  subst h5
  have cp : ∀ i, i < 7 → memStore32 (memStore8 (memStore32 m3 (F + BitVec.ofNat 32 0x24) q)
      (F + BitVec.ofNat 32 0x28) (M (F + BitVec.ofNat 32 0xE4))) (F + BitVec.ofNat 32 0x30) 0
      (F + BitVec.ofNat 32 (0x29 + i)) = M (F + BitVec.ofNat 32 (0xE5 + i)) := fun i hi => by
    rw [memStore32_get_sep (X.fsep (Or.inr (by omega)) (by decide) (by omega)),
      memStore8_ne (fun e => X.fsep (c := 0x28) (k := 1) (d := 0x29 + i) (l := 1) (Or.inl (by omega)) (by decide)
        (by omega) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e])),
      memStore32_get_sep (X.fsep (Or.inl (by omega)) (by decide) (by omega)),
      hc _ (by rw [X.fG]; exact X.gsep (Or.inl (by omega)) (by decide) (by omega)),
      ← add_ofNat_assoc F 0x29 i, rc_cpIn hi (by decide), add_ofNat_assoc]
  refine ⟨fun x hx => ?_, ?_, ?_, ?_, memLoad32_store32_same _ _ _⟩
  · rw [memStore32_get_sep (X.fsepIn hx (by decide)),
      memStore8_ne (fun e => X.fsepIn (d := 0x28) (l := 1) hx (by decide) 0 (by decide) 0 (by decide)
        (by rw [add_ofNat_zero, add_ofNat_zero, e])),
      memStore32_get_sep (X.fsepIn hx (by decide))]
  · rw [memLoad32_store32_sep (X.fsep (Or.inr (by decide)) (by decide) (by decide)),
      memLoad32_store8_sep (X.fsep (Or.inr (by decide)) (by decide) (by decide)), memLoad32_store32_same]
  · refine rc_ld2 fun j hj => ?_
    rcases j with _ | i
    · rw [add_ofNat_zero, add_ofNat_zero,
        memStore32_get_sep (X.fsep (c := 0x30) (k := 4) (d := 0x28) (l := 1) (Or.inr (by decide)) (by decide)
          (by decide)), memStore8_same]
    · rw [add_ofNat_assoc, add_ofNat_assoc, show 0x28 + (i + 1) = 0x29 + i by omega,
        show 0xE4 + (i + 1) = 0xE5 + i by omega]
      exact cp i (by omega)
  · refine rc_ld2 fun j hj => ?_
    rw [add_ofNat_assoc, add_ofNat_assoc, show 0x2C + j = 0x29 + (j + 3) by omega,
      show 0xE8 + j = 0xE5 + (j + 3) by omega]
    exact cp (j + 3) (by omega)

/-- From 0xBC, after `elements` on the `certificates` array: the cursor
goes to `F + 0x24`, and the loop starts with four passes of fuel. -/
theorem RcCtx.pElem (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {r : Except (Option Nat) (RcCert × RcSt)} {q : Word} {l nb na : Nat}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) (hB : RcBuf M fr fp fl [])
    (hW : RcWin nb na f) (hA : RcIn p n q l)
    (hC : CurRes M M (F + BitVec.ofNat 32 0xE0) 0x21 (curOpen 91 q (memBytes M0 q l)))
    (hr : r = rcChain M0 fp fl q l nb na) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0xBC f := by
  obtain ⟨hA0, hAw⟩ := X.inW hA
  refine WP.lw trc_at_bc (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
  refine WP.lbu trc_at_be ?_; wn
  rcases hco : curOpen 91 q (memBytes M0 q l) with _ | ⟨q', an, pos⟩
  · rw [hco] at hC
    have hE0 : memLoad32 M (F + 0xE0) = 0 := hC.2.1
    have hE4 : M (F + 0xE4) = 0x21 := by have := hC.2.2; rw [rc_a4] at this; exact this
    refine WP.branch trc_at_c2 (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR.2.1, hE0]; decide)); wn
    exact X.e4c8 (e := some 0x21) (by rw [hr]; simp only [rcChain, hco]) (by rc_r hR) hI (fun b hb => by
      cases hb; trsimp; rw [hR.2.1, hE4]; rfl)
  · obtain ⟨hq', han, hpl, hl1⟩ := rc_curOpen hco
    subst q' an
    rw [hco] at hC
    rw [memBytes_length] at hpl hl1 hC hco
    have hq0 : q ≠ 0 := fun h => hA0 (by rw [h]; rfl)
    have hE0 : memLoad32 M (F + 0xE0) = q := hC.2.1
    have hE4 : memLoad32 M (F + BitVec.ofNat 32 0xE4) = BitVec.ofNat 32 l := by
      have := hC.2.2.1; rw [rc_a4] at this; exact this
    have hE8 : memLoad32 M (F + BitVec.ofNat 32 0xE8) = BitVec.ofNat 32 pos := by
      have := hC.2.2.2; rw [rc_a8] at this; exact this
    refine WP.branch trc_at_c2 (fun ht => absurd ht (by trsimp; rw [hR.2.1, hE0, rck_beqF hq0]; decide))
      (fun _ => ?_); wn
    refine WP.aluImm trc_at_c6 ?_; wn
    refine WP.aluImm trc_at_ca ?_; wn
    refine WP.aluImm trc_at_ce ?_; wn
    refine X.callMc (off := 0xD0) (dd := 0x29) (N := 7) (src := F + BitVec.ofNat 32 0xE5) trc_at_d0 trc_at_d4 (by decide) (by decide) (by rc_r hR) hI
      (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; (try rw [rc_x0 hR.1]); try rfl)
      (by decide) (by have := X.fn; have := X.gw; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      (by rw [X.fG]; exact X.gsep (Or.inr (by decide)) (by decide) (by decide)) (X.fsep (Or.inl (by decide))
        (by decide) (by decide)) (fun m3 hI3 hc => ?_)
    refine WP.sw trc_at_d8 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0x24) (by decide))
      (by trsimp; rw [hR.2.1]; exact X.flo (c := 0x24) (k := 4) (by decide)) ?_; wn
    refine WP.sb trc_at_da (by trsimp; rw [hR.2.1]; exact X.flo (c := 0x28) (k := 1) (by decide)) ?_; wn
    refine WP.sw trc_at_de (by trsimp; rw [hR.2.1]; exact X.fal (c := 0x30) (by decide))
      (by trsimp; rw [hR.2.1]; exact X.flo (c := 0x30) (k := 4) (by decide)) ?_; wn
    refine WP.aluImm trc_at_e0 ?_; wn
    refine WP.aluImm trc_at_e4 ?_; wn
    refine WP.aluImm trc_at_e8 ?_; wn
    refine WP.lui trc_at_ec ?_; wn
    refine WP.aluImm trc_at_f0 ?_; wn
    refine WP.aluImm trc_at_f4 ?_; wn
    refine WP.branch trc_at_f6 (fun ht => absurd ht (by trsimp <;> (try rw [rc_x0 hR.1]) <;> decide)) (fun _ => ?_); wn
    rw [hR.2.1, hE0, rc_ze8]
    obtain ⟨hS, h24, h28, h2C, h30⟩ := X.hdMem (M := M) (q := q) hc rfl
    have hG : RcG G M (memStore32 (memStore8 (memStore32 m3.mem (F + BitVec.ofNat 32 0x24) q)
        (F + BitVec.ofNat 32 0x28) (M (F + BitVec.ofNat 32 0xE4))) (F + BitVec.ofNat 32 0x30) 0) :=
      (X.mcG (by decide) hc).trans ((X.swG (c := 0x24) (by decide)).trans ((X.sbG (c := 0x28) (by decide)).trans
        (X.swG (c := 0x30) (by decide))))
    refine X.pLoop hA 4 (by decide) (by decide) ⟨pos, [], none, nb, na⟩ _ _
      ⟨by rc_r hR, hI3.step X (c := 0x5E4) (l := 16) (by decide) (fun x xa _ _ => hS x (by rw [X.fG]; exact xa)),
        by rc_w hW, by rc_reg, by rc_reg, by rc_reg, by rc_reg, by rc_reg, h24, h28.trans hE4, h2C.trans hE8,
        show pos < 2 ^ 32 by omega, h30, X.bufG hB hG⟩
      (by rw [hr]; simp only [rcChain, hco]; rfl)

/-- From 0x76, with the window read: the `certChain` field, its
`certificates` field, and `elements` on that. -/
theorem RcCtx.pCerts (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {r : Except (Option Nat) (RcCert × RcSt)} {nb na : Nat}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) (hB : RcBuf M fr fp fl [])
    (hW : RcWin nb na f) (h8 : f 8 = p) (h9 : f 9 = BitVec.ofNat 32 n)
    (hr : r = rcCerts M0 p n fp fl nb na) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x76 f := by
  have hP := X.inSelf
  obtain ⟨hP0, hPw⟩ := X.inW hP
  refine WP.lui trc_at_76 ?_; wn
  refine WP.aluImm trc_at_7a ?_; wn
  refine WP.aluImm trc_at_7e ?_; wn
  refine WP.aluImm trc_at_80 ?_; wn
  refine WP.alu trc_at_82 ?_; wn
  refine WP.alu trc_at_84 ?_; wn
  refine X.callField (off := 0x86) (c := 0x60) trc_at_86 trc_at_8a (by decide) (by decide) (by rc_r hR) hI
    (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; (try rw [rc_x0 hR.1]); exact h8)
    (by trsimp; (try rw [rc_x0 hR.1]); exact h9) (by rc_reg) (by rc_reg) hP0 (by omega) (by decide) (X.inG hP)
    (rc_roSub X.ro ⟨by decide, by decide⟩).symm (X.inM hI hP) (X.codeAt hI).kc (fun m2 hK2 hI2 hFR => ?_)
  refine WP.lw trc_at_8e (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0x60) (by decide)) ?_; wn
  rcases hy : objField (memBytes M0 p n) (ascii!"certChain") with e | ⟨yb, yl⟩
  · rw [hy] at hFR
    change FieldRes m2.mem m2.mem _ (.error e) at hFR
    have h60 : memLoad32 m2.mem (F + 0x60) = 0 := hFR.2.1
    refine WP.branch trc_at_90 (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR.2.1, h60]; decide)); wn
    exact X.e480 (e := some e) (by rw [hr]; simp only [rcCerts, hy]) (by rc_r hR) hI2 (fun b hb => by
      cases hb; exact (congrArg m2.mem (add_ofNat_assoc F 0x60 4)).symm.trans hFR.2.2)
  rw [hy] at hFR
  change FieldRes m2.mem m2.mem _ (.ok (p + BitVec.ofNat 32 yb, yl)) at hFR
  obtain ⟨hyb, hyl⟩ := tvf_field_val hy
  rw [memBytes_length] at hyb hyl
  have hq : RcIn p n (p + BitVec.ofNat 32 yb) yl := ⟨yb, by omega, rfl⟩
  obtain ⟨hq0, hqw⟩ := X.inW hq
  have hq0' : p + BitVec.ofNat 32 yb ≠ 0 := fun h => hq0 (by rw [h]; rfl)
  have h60 : memLoad32 m2.mem (F + 0x60) = p + BitVec.ofNat 32 yb := hFR.2.1
  have h64 : memLoad32 m2.mem (F + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 yl := by
    have := hFR.2.2; rw [rc_a4] at this; exact this
  refine WP.branch trc_at_90 (fun ht => absurd ht (by trsimp; rw [hR.2.1, h60, rck_beqF hq0']; decide))
    (fun _ => ?_); wn
  refine WP.lw trc_at_94 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0x64) (by decide)) ?_; wn
  refine WP.lui trc_at_96 ?_; wn
  refine WP.aluImm trc_at_9a ?_; wn
  refine WP.aluImm trc_at_9e ?_; wn
  refine WP.aluImm trc_at_a0 ?_; wn
  refine X.callField (off := 0xA2) (c := 0xD0) trc_at_a2 trc_at_a6 (by decide) (by decide) (by rc_r hR) hI2
    (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; exact h60)
    (by trsimp; rw [hR.2.1]; exact h64) (by rc_reg) (by rc_reg) hq0 (by omega) (by decide) (X.inG hq)
    (rc_roSub X.ro ⟨by decide, by decide⟩).symm (X.inM hI2 hq) (X.codeAt hI2).kl (fun m3 hK3 hI3 hFR3 => ?_)
  refine WP.lw trc_at_aa (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xD0) (by decide)) ?_; wn
  rcases hz : objField (memBytes M0 (p + BitVec.ofNat 32 yb) yl) (ascii!"certificates") with e | ⟨zb, zl⟩
  · rw [hz] at hFR3
    change FieldRes m3.mem m3.mem _ (.error e) at hFR3
    have hD0 : memLoad32 m3.mem (F + 0xD0) = 0 := hFR3.2.1
    refine WP.branch trc_at_ac (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR.2.1, hD0]; decide)); wn
    exact X.e4c2 (e := some e) (by rw [hr]; simp only [rcCerts, hy, hz]) (by rc_r hR) hI3 (fun b hb => by
      cases hb; exact (congrArg m3.mem (add_ofNat_assoc F 0xD0 4)).symm.trans hFR3.2.2)
  rw [hz] at hFR3
  change FieldRes m3.mem m3.mem _ (.ok (p + BitVec.ofNat 32 yb + BitVec.ofNat 32 zb, zl)) at hFR3
  obtain ⟨hzb, hzl⟩ := tvf_field_val hz
  rw [memBytes_length] at hzb hzl
  have hq2 : RcIn p n (p + BitVec.ofNat 32 yb + BitVec.ofNat 32 zb) zl := hq.sub (by omega)
  obtain ⟨hq20, hq2w⟩ := X.inW hq2
  have hq20' : p + BitVec.ofNat 32 yb + BitVec.ofNat 32 zb ≠ 0 := fun h => hq20 (by rw [h]; rfl)
  have hD0 : memLoad32 m3.mem (F + 0xD0) = p + BitVec.ofNat 32 yb + BitVec.ofNat 32 zb := hFR3.2.1
  have hD4 : memLoad32 m3.mem (F + BitVec.ofNat 32 0xD4) = BitVec.ofNat 32 zl := by
    have := hFR3.2.2; rw [rc_a4] at this; exact this
  refine WP.branch trc_at_ac (fun ht => absurd ht (by trsimp; rw [hR.2.1, hD0, rck_beqF hq20']; decide))
    (fun _ => ?_); wn
  refine WP.lw trc_at_b0 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xD4) (by decide)) ?_; wn
  refine WP.aluImm trc_at_b2 ?_; wn
  refine X.callElems (by rc_r hR) hI3 (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; exact hD0)
    (by trsimp; rw [hR.2.1]; exact hD4) (by omega) (X.inG hq2) (X.inM hI3 hq2) (fun m4 hK4 hI4 hC => ?_)
  exact X.pElem (by rc_r hR) hI4 (X.bufG hB ((hK2.g.trans hK3.g).trans hK4.g)) (by rc_w hW) hq2 hC
    (by rw [hr]; simp only [rcCerts, hy, hz])

/-- From 0x3C, after the prologue: the `validFor` field, `valid_for` on it,
and the window into `s3`, `s5`, `s11`, and `s8`. -/
theorem RcCtx.pHead (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {r : Except (Option Nat) (RcCert × RcSt)}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) (hB : RcBuf M fr fp fl [])
    (h8 : f 8 = p) (h9 : f 9 = BitVec.ofNat 32 n) (h11 : f a1 = p) (h12 : f a2 = BitVec.ofNat 32 n)
    (hr : r = readChainPos M0 p n fp fl) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x3C f := by
  have hP := X.inSelf
  obtain ⟨hP0, hPw⟩ := X.inW hP
  refine WP.lui trc_at_3c ?_; wn
  refine WP.aluImm trc_at_40 ?_; wn
  refine WP.aluImm trc_at_44 ?_; wn
  refine WP.aluImm trc_at_46 ?_; wn
  refine X.callField (off := 0x48) (c := 0x60) trc_at_48 trc_at_4c (by decide) (by decide) (by rc_r hR) hI
    (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; exact h11) (by trsimp; exact h12)
    (by rc_reg) (by rc_reg) hP0 (by omega) (by decide) (X.inG hP)
    (rc_roSub X.ro ⟨by decide, by decide⟩).symm (X.inM hI hP) (X.codeAt hI).kv (fun m2 hK2 hI2 hFR => ?_)
  refine WP.lw trc_at_50 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0x60) (by decide)) ?_; wn
  rcases hx : objField (memBytes M0 p n) (ascii!"validFor") with e | ⟨xb, xl⟩
  · rw [hx] at hFR
    change FieldRes m2.mem m2.mem _ (.error e) at hFR
    have h60 : memLoad32 m2.mem (F + 0x60) = 0 := hFR.2.1
    refine WP.branch trc_at_52 (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR.2.1, h60]; decide)); wn
    exact X.e480 (e := some e) (by rw [hr]; simp only [readChainPos, hx]) (by rc_r hR) hI2 (fun b hb => by
      cases hb; exact (congrArg m2.mem (add_ofNat_assoc F 0x60 4)).symm.trans hFR.2.2)
  rw [hx] at hFR
  change FieldRes m2.mem m2.mem _ (.ok (p + BitVec.ofNat 32 xb, xl)) at hFR
  obtain ⟨hxb, hxl⟩ := tvf_field_val hx
  rw [memBytes_length] at hxb hxl
  have hq : RcIn p n (p + BitVec.ofNat 32 xb) xl := ⟨xb, by omega, rfl⟩
  obtain ⟨hq0, hqw⟩ := X.inW hq
  have hq0' : p + BitVec.ofNat 32 xb ≠ 0 := fun h => hq0 (by rw [h]; rfl)
  have h60 : memLoad32 m2.mem (F + 0x60) = p + BitVec.ofNat 32 xb := hFR.2.1
  have h64 : memLoad32 m2.mem (F + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 xl := by
    have := hFR.2.2; rw [rc_a4] at this; exact this
  refine WP.branch trc_at_52 (fun ht => absurd ht (by trsimp; rw [hR.2.1, h60, rck_beqF hq0']; decide))
    (fun _ => ?_); wn
  refine WP.lw trc_at_56 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0x64) (by decide)) ?_; wn
  refine WP.aluImm trc_at_58 ?_; wn
  refine X.callTvf (by rc_r hR) hI2 (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; exact h60)
    (by trsimp; rw [hR.2.1]; exact h64) hqw hq0 (X.inG4 hq) (X.inM hI2 hq) (fun m3 hK3 hI3 hT => ?_)
  refine WP.lbu trc_at_62 ?_; wn
  rcases hv : validForPos (memBytes M0 (p + BitVec.ofNat 32 xb) xl) with e | ⟨nb, na⟩
  · rw [hv] at hT
    have hE0 : m3.mem (F + 0xE0) = 1 := hT.1
    refine WP.branch trc_at_66 (fun ht => absurd ht (by trsimp; rw [hR.2.1, hE0]; decide)) (fun _ => ?_); wn
    exact X.e068 (e := some e) (by rw [hr]; simp only [readChainPos, hx, hv]) (by rc_r hR) hI3 (fun b hb => by
      cases hb; exact (congrArg m3.mem (add_ofNat_assoc F 0xE0 1)).symm.trans hT.2)
  rw [hv] at hT
  obtain ⟨hnb, hna, hE0, t0, t1, t2, t3⟩ := hT
  have hE0' : m3.mem (F + 0xE0) = 0 := hE0
  have e8 : memLoad32 m3.mem (F + 0xE8) = BitVec.ofNat 32 (nb % 2 ^ 32) := by
    rw [show (F + BitVec.ofNat 32 0xE0 + 8 : Word) = F + 0xE8 from add_ofNat_assoc F 0xE0 8] at t0; exact t0
  have eC : memLoad32 m3.mem (F + 0xEC) = BitVec.ofNat 32 (nb / 2 ^ 32) := by
    rw [show (F + BitVec.ofNat 32 0xE0 + 0xC : Word) = F + 0xEC from add_ofNat_assoc F 0xE0 0xC] at t1; exact t1
  have e10 : memLoad32 m3.mem (F + 0xF0) = BitVec.ofNat 32 (na % 2 ^ 32) := by
    rw [show (F + BitVec.ofNat 32 0xE0 + 0x10 : Word) = F + 0xF0 from add_ofNat_assoc F 0xE0 0x10] at t2; exact t2
  have e14 : memLoad32 m3.mem (F + 0xF4) = BitVec.ofNat 32 (na / 2 ^ 32) := by
    rw [show (F + BitVec.ofNat 32 0xE0 + 0x14 : Word) = F + 0xF4 from add_ofNat_assoc F 0xE0 0x14] at t3; exact t3
  refine WP.branch trc_at_66 (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR.2.1, hE0']; decide)); wn
  refine WP.lw trc_at_6e (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xE8) (by decide)) ?_; wn
  refine WP.lw trc_at_70 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xEC) (by decide)) ?_; wn
  refine WP.lw trc_at_72 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xF0) (by decide)) ?_; wn
  refine WP.lw trc_at_74 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xF4) (by decide)) ?_; wn
  exact X.pCerts (by rc_r hR) hI3 (X.bufG hB (hK2.g.trans hK3.g))
    ⟨by trsimp; rw [hR.2.1]; exact e8, by trsimp; rw [hR.2.1]; exact eC, by trsimp; rw [hR.2.1]; exact e10,
      by trsimp; rw [hR.2.1]; exact e14, hnb, hna⟩
    (by trsimp; exact h8) (by trsimp; exact h9) (by rw [hr]; simp only [readChainPos, rcCerts, hx, hv]; rfl)

end

end C3.RV32
