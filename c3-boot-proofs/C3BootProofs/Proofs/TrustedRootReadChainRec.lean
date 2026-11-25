import C3BootProofs.Proofs.TrustedRootReadChainParseTop

/-!
# The end of one certificate in `read_chain`

The block from 0x308 to 0x3CD runs after `parse_cert` returns a
certificate. It intersects the window with the certificate's validity,
stores the certificate as a `Cert` at `F + 0xE0`, keeps the first
certificate at `F + 0x30`, and counts down the certificates left. It ends
at the loop's top, 0xFA, or after the loop, at 0x4D8.

`RcLoopInv` is the state at both: the window in `s3`, `s5`, `s11`, and
`s8`, the array cursor at `F + 0x24`, the first certificate at
`F + 0x30`, and the decoded certificates in the buffer.
-/

namespace C3.RV32

open C3.Image C3.Json C3.RV32.Dq C3.RV32.P3

set_option maxRecDepth 20000

/-- The window `nb`–`na` in `s3` and `s5`, and `s11` and `s8`. -/
def RcWin (nb na : Nat) (f : Fin 32 → Word) : Prop :=
  f 19 = BitVec.ofNat 32 (nb % 2 ^ 32) ∧ f 21 = BitVec.ofNat 32 (nb / 2 ^ 32) ∧
    f 27 = BitVec.ofNat 32 (na % 2 ^ 32) ∧ f 24 = BitVec.ofNat 32 (na / 2 ^ 32) ∧ nb < 2 ^ 64 ∧ na < 2 ^ 64

theorem RcWin.keep {nb na : Nat} {f f' : Fin 32 → Word} (h : RcWin nb na f) (hK : RcK [19, 21, 24, 27] f f') :
    RcWin nb na f' :=
  ⟨(hK 19 (by decide)).trans h.1, (hK 21 (by decide)).trans h.2.1, (hK 27 (by decide)).trans h.2.2.1,
    (hK 24 (by decide)).trans h.2.2.2.1, h.2.2.2.2⟩

/-- The `Cert` `c` in the 0x2C bytes at `R`. -/
def RcRec (M : Word → BitVec 8) (R : Word) (c : RcCert) : Prop :=
  memLoad32 M (R + BitVec.ofNat 32 0) = c.serial ∧
    memLoad32 M (R + BitVec.ofNat 32 4) = BitVec.ofNat 32 c.serialLen ∧
    memLoad32 M (R + BitVec.ofNat 32 8) = c.issuer ∧
    memLoad32 M (R + BitVec.ofNat 32 0xC) = BitVec.ofNat 32 c.issuerLen ∧
    memLoad32 M (R + BitVec.ofNat 32 0x10) = c.subject ∧
    memLoad32 M (R + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 c.subjectLen ∧
    memLoad32 M (R + BitVec.ofNat 32 0x18) = BitVec.ofNat 32 (c.notBefore % 2 ^ 32) ∧
    memLoad32 M (R + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 (c.notBefore / 2 ^ 32) ∧
    memLoad32 M (R + BitVec.ofNat 32 0x20) = BitVec.ofNat 32 (c.notAfter % 2 ^ 32) ∧
    memLoad32 M (R + BitVec.ofNat 32 0x24) = BitVec.ofNat 32 (c.notAfter / 2 ^ 32) ∧
    memLoad32 M (R + BitVec.ofNat 32 0x28) = c.key ∧ c.notBefore < 2 ^ 64 ∧ c.notAfter < 2 ^ 64 ∧ c.serial ≠ 0

theorem RcRec.copy {M M' : Word → BitVec 8} {R R' : Word} {c : RcCert} (h : RcRec M R c)
    (hc : ∀ k, k % 4 = 0 → k + 4 ≤ 0x2C →
      memLoad32 M' (R' + BitVec.ofNat 32 k) = memLoad32 M (R + BitVec.ofNat 32 k)) : RcRec M' R' c :=
  ⟨(hc 0 rfl (by decide)).trans h.1, (hc 4 rfl (by decide)).trans h.2.1, (hc 8 rfl (by decide)).trans h.2.2.1,
    (hc 0xC rfl (by decide)).trans h.2.2.2.1, (hc 0x10 rfl (by decide)).trans h.2.2.2.2.1,
    (hc 0x14 rfl (by decide)).trans h.2.2.2.2.2.1, (hc 0x18 rfl (by decide)).trans h.2.2.2.2.2.2.1,
    (hc 0x1C rfl (by decide)).trans h.2.2.2.2.2.2.2.1, (hc 0x20 rfl (by decide)).trans h.2.2.2.2.2.2.2.2.1,
    (hc 0x24 rfl (by decide)).trans h.2.2.2.2.2.2.2.2.2.1, (hc 0x28 rfl (by decide)).trans h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2⟩

/-- The first certificate, if any, at `R`: a `Cert`, or a null serial
pointer. -/
def RcFirst (M : Word → BitVec 8) (R : Word) : Option RcCert → Prop
  | none => memLoad32 M R = 0
  | some c => RcRec M R c

theorem RcFirst.copy {M M' : Word → BitVec 8} {R R' : Word} {c : Option RcCert} (h : RcFirst M R c)
    (hc : ∀ k, k % 4 = 0 → k + 4 ≤ 0x2C →
      memLoad32 M' (R' + BitVec.ofNat 32 k) = memLoad32 M (R + BitVec.ofNat 32 k)) : RcFirst M' R' c := by
  cases c with
  | none =>
    have := hc 0 rfl (by decide); rw [add_ofNat_zero, add_ofNat_zero] at this; exact this.trans h
  | some c => exact RcRec.copy h hc

/-- The serial pointer of the first certificate, if any, at `R`, is not
null. -/
theorem RcFirst.ld0 {M : Word → BitVec 8} {R : Word} {c : Option RcCert} (h : RcFirst M R c) :
    (memLoad32 M R = 0 ↔ c = none) := by
  cases c with
  | none => exact ⟨fun _ => rfl, fun _ => h⟩
  | some c =>
    have h1 := h.1; rw [add_ofNat_zero] at h1
    exact ⟨fun e => absurd (h1.symm.trans e) h.2.2.2.2.2.2.2.2.2.2.2.2.2, fun e => by cases e⟩

/-- The scratch slice after the decoded certificates `dec`, which the
buffer holds. -/
def RcBuf (M : Word → BitVec 8) (fr fp : Word) (fl : Nat) (dec : Bytes) : Prop :=
  dec.length ≤ fl ∧ memLoad32 M fr = fp + BitVec.ofNat 32 dec.length ∧
    memLoad32 M (fr + 4) = BitVec.ofNat 32 (fl - dec.length) ∧ memBytes M fp dec.length = dec

/-- Memory that changed only in the stack region. -/
def RcG (G : Word) (M M' : Word → BitVec 8) : Prop := ∀ x, Sep G 0x740 x 1 → M' x = M x

theorem RcG.trans {G : Word} {M M1 M2 : Word → BitVec 8} (h1 : RcG G M M1) (h2 : RcG G M1 M2) : RcG G M M2 :=
  fun x hx => (h2 x hx).trans (h1 x hx)

theorem RcKeep.g {G : Word} {M M' : Word → BitVec 8} (h : RcKeep G M M') : RcG G M M' :=
  fun _ hx => (RcKeep.kb (lo := 0) h).out (by decide) hx

theorem RcKB.g {G : Word} {lo : Nat} {M M' : Word → BitVec 8} (h : RcKB G lo M M') (hlo : lo ≤ 0x60) :
    RcG G M M' :=
  fun _ hx => h.out hlo hx

/-- The state of `read_chain`'s loop at its top, 0xFA, and after it, 0x4D8,
with `k` certificates left to read from the array of `an` bytes at `ap`. -/
def RcLoopInv (M0 : Word → BitVec 8) (G F out fr fp : Word) (fl : Nat) (g0 : Fin 32 → Word) (ap : Word)
    (an k : Nat) (s : RcSt) (M : Word → BitVec 8) (f : Fin 32 → Word) : Prop :=
  RcRegs F out fr g0 f ∧ RcMemInv M0 G F fr fp fl g0 M ∧ RcWin s.nb s.na f ∧
    f 20 = F + BitVec.ofNat 32 0xE5 ∧ f 9 = F + BitVec.ofNat 32 0xA5 ∧ f 23 = F + BitVec.ofNat 32 0xE5 ∧
    f 8 = rcRawKey ∧ f 22 = BitVec.ofNat 32 k ∧
    memLoad32 M (F + BitVec.ofNat 32 0x24) = ap ∧ memLoad32 M (F + BitVec.ofNat 32 0x28) = BitVec.ofNat 32 an ∧
    memLoad32 M (F + BitVec.ofNat 32 0x2C) = BitVec.ofNat 32 s.pos ∧ s.pos < 2 ^ 32 ∧
    RcFirst M (F + BitVec.ofNat 32 0x30) s.first ∧ RcBuf M fr fp fl s.dec

theorem Sep.rcSub0 {a b : Word} {k n l : Nat} (h : Sep a k b n) (hl : l ≤ n) : Sep a k b l := by
  have := h.subR (c := 0) (l := l) (by omega); rwa [add_ofNat_zero] at this

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

theorem RcCtx.bufG (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {dec : Bytes}
    (h : RcBuf M fr fp fl dec) (hO : RcG G M M') : RcBuf M' fr fp fl dec :=
  ⟨h.1, (memLoad32_congr fun _ hj => hO _ (sep_pt X.frg.symm (by omega)).symm).trans h.2.1,
    (memLoad32_congr fun _ hj => hO _ (sep_pt (X.frg.symm.subR (c := 4) (l := 4) (by decide)) hj).symm).trans
      h.2.2.1,
    (memBytes_congr fun _ hj => hO _ (sep_pt (X.bg.symm.rcSub0 (by have := h.1; omega)) hj).symm).trans h.2.2.2⟩

theorem RcCtx.mcG (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {dd N : Nat} {src : Word}
    (hdN : dd + N ≤ 0x180)
    (h : ∀ x, Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 → M' x = copyBytes M (F + BitVec.ofNat 32 dd) src N x) :
    RcG G M M' :=
  fun x hx => by
    rw [h x (sep_in hx.symm (by decide)).symm]
    exact copyBytes_sep (n := N) (by rw [X.fG]; exact (sep_in hx.symm (by omega)).symm) (Nat.le_refl N)

theorem RcCtx.swG (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {c : Nat} {v : Word}
    (hc : c + 4 ≤ 0x180) : RcG G M (memStore32 M (F + BitVec.ofNat 32 c) v) :=
  fun x hx => X.sw32 M c v x (by rw [X.fG]; exact (sep_in hx.symm (by omega)).symm)

theorem RcCtx.sbG (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {c : Nat} {v : BitVec 8}
    (hc : c + 1 ≤ 0x180) : RcG G M (memStore8 M (F + BitVec.ofNat 32 c) v) :=
  fun x hx => X.sw8 M c v x (by rw [X.fG]; exact (sep_in hx.symm (by omega)).symm)

end

theorem rc_shr (v : Word) (k : Nat) : (v >>> k).extractLsb' 0 8 = v.extractLsb' k 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_zero]

theorem rc_ultLo {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : BitVec.ofNat 32 (a / 2 ^ 32) = BitVec.ofNat 32 (b / 2 ^ 32)) :
    (BitVec.ofNat 32 (a % 2 ^ 32)).ult (BitVec.ofNat 32 (b % 2 ^ 32)) = decide (a < b) := by
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h'
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  apply decide_eq_decide.mpr
  constructor <;> intro <;> omega

theorem rc_ultHi {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : BitVec.ofNat 32 (a / 2 ^ 32) ≠ BitVec.ofNat 32 (b / 2 ^ 32)) :
    (BitVec.ofNat 32 (a / 2 ^ 32)).ult (BitVec.ofNat 32 (b / 2 ^ 32)) = decide (a < b) := by
  have h' : a / 2 ^ 32 ≠ b / 2 ^ 32 := fun e => h (by rw [e])
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  apply decide_eq_decide.mpr
  constructor <;> intro <;> omega

theorem RcWin.set {nb na : Nat} {f : Fin 32 → Word} {rd : Fin 32} {v : Word} (h : RcWin nb na f)
    (hr : rd.val ∉ [19, 21, 24, 27]) : RcWin nb na (upd f rd v) :=
  h.keep (RcK.set (fun _ _ => rfl) hr (by decide))

theorem RcWin.clob {nb na : Nat} {f : Fin 32 → Word} {m : Machine} {v : Word} (h : RcWin nb na f) :
    RcWin nb na (clob (upd f ra v) m jClob) :=
  h.keep (RcK.clob (RcK.set (fun _ _ => rfl) (by decide) (by decide)) (by decide))

/-- Proves `RcWin` of a register file that `upd` and `clob` build from one
that `h` covers. -/
macro "rc_w " h:term : tactic => `(tactic| (
  repeat (first
    | refine RcWin.clob ?_
    | refine RcWin.set ?_ (by decide))
  exact $h))

/-- Four byte stores of a word's bytes are one word store. -/
theorem rc_sb4 (M : Word → BitVec 8) (B v : Word) (c c1 c2 c3 : Nat) (h1 : c1 = c + 1) (h2 : c2 = c + 2)
    (h3 : c3 = c + 3) :
    memStore8 (memStore8 (memStore8 (memStore8 M (B + BitVec.ofNat 32 c) (v.extractLsb' 0 8))
      (B + BitVec.ofNat 32 c1) ((aluEval .srl v (BitVec.ofNat 32 8)).extractLsb' 0 8))
      (B + BitVec.ofNat 32 c2) ((aluEval .srl v (BitVec.ofNat 32 16)).extractLsb' 0 8))
      (B + BitVec.ofNat 32 c3) ((aluEval .srl v (BitVec.ofNat 32 24)).extractLsb' 0 8) =
      memStore32 M (B + BitVec.ofNat 32 c) v := by
  subst h1 h2 h3
  have e : ∀ j, B + BitVec.ofNat 32 c + BitVec.ofNat 32 j = B + BitVec.ofNat 32 (c + j) := add_ofNat_assoc B c
  simp only [memStore32, aluEval, BitVec.toNat_ofNat, rc_shr, Nat.reducePow, Nat.reduceMod]
  rw [← e 1, ← e 2, ← e 3]
  rfl

theorem rc_dec {k : Nat} (hk : 1 ≤ k ∧ k ≤ 4) :
    BitVec.ofNat 32 k + BitVec.ofNat 32 0xFFFFFFFF = BitVec.ofNat 32 (k - 1) := by
  obtain ⟨h1, h4⟩ := hk
  match k, h1, h4 with
  | 0, h, _ => exact absurd h (by decide)
  | 1, _, _ => rfl
  | 2, _, _ => rfl
  | 3, _, _ => rfl
  | 4, _, _ => rfl
  | _ + 5, _, h => exact absurd h (by omega)

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

theorem rc_k0 {k : Nat} (hk : k ≤ 4) (h : k - 1 ≠ 0) : BitVec.ofNat 32 (k - 1) ≠ 0 := by
  match k, hk, h with
  | 0, _, h => exact absurd rfl h
  | 1, _, h => exact absurd rfl h
  | 2, _, _ => decide
  | 3, _, _ => decide
  | 4, _, _ => decide
  | _ + 5, h, _ => exact absurd h (by omega)

/-- Reads a word of the frame through stores to other words of it. -/
macro "rc_ld" : tactic => `(tactic| (
  try simp only [add_ofNat_assoc, Nat.reduceAdd]
  simp (disch := decide) only [rcf_ld32o, memLoad32_store32_same]))

/-- Proves `RcG` of stores to the frame. -/
macro "rc_g" : tactic => `(tactic| (
  repeat (refine RcG.trans ?_ (RcCtx.swG ‹_› (by decide)))
  exact fun _ _ => rfl))

/-- From 0x38C: the `Cert` `c` at `F + 0xE0`. Copies the first
certificate, `c` when there was none, through `F + 0x60` to `F + 0x30`,
and counts down. -/
theorem RcCtx.pRecCopy (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {nb na k pos an : Nat} {c : RcCert} {first : Option RcCert} {ap : Word} {dec : Bytes}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) (hW : RcWin nb na f)
    (ha0 : f a0 = memLoad32 M (F + BitVec.ofNat 32 0x30)) (hC : RcRec M (F + BitVec.ofNat 32 0xE0) c)
    (hm20 : memLoad32 M (F + BitVec.ofNat 32 0x20) = BitVec.ofNat 32 k) (hk : 1 ≤ k ∧ k ≤ 4)
    (hm24 : memLoad32 M (F + BitVec.ofNat 32 0x24) = ap)
    (hm28 : memLoad32 M (F + BitVec.ofNat 32 0x28) = BitVec.ofNat 32 an)
    (hm2C : memLoad32 M (F + BitVec.ofNat 32 0x2C) = BitVec.ofNat 32 pos) (hpos : pos < 2 ^ 32)
    (hF : RcFirst M (F + BitVec.ofNat 32 0x30) first) (hB : RcBuf M fr fp fl dec)
    (kTop : ∀ M' f', RcLoopInv M0 G F out fr fp fl g0 ap an (k - 1) ⟨pos, dec, first.or (some c), nb, na⟩ M' f' →
      k - 1 ≠ 0 → WP trustedRootReadChainCode TRC Q M' 0xFA f')
    (kFin : ∀ M' f', RcLoopInv M0 G F out fr fp fl g0 ap an (k - 1) ⟨pos, dec, first.or (some c), nb, na⟩ M' f' →
      k - 1 = 0 → WP trustedRootReadChainCode TRC Q M' 0x4D8 f') :
    WP trustedRootReadChainCode TRC Q M 0x38C f := by
  obtain ⟨c', hc'⟩ : ∃ c', first.or (some c) = some c' := by cases first <;> exact ⟨_, rfl⟩
  have kM : ∀ (sc : Nat) (f1 : Fin 32 → Word), (sc = 0xE0 ∨ sc = 0x30) → RcRegs F out fr g0 f1 → RcWin nb na f1 →
      f1 a1 = F + BitVec.ofNat 32 sc → RcRec M (F + BitVec.ofNat 32 sc) c' →
      WP trustedRootReadChainCode TRC Q M 0x392 f1 := by
    intro sc f1 hsc hR1 hW1 ha1 hS
    refine WP.aluImm trc_at_392 ?_; wn
    refine WP.aluImm trc_at_394 ?_; wn
    refine X.callMc (off := 0x398) (dd := 0x60) (N := 0x30) (src := F + BitVec.ofNat 32 sc) trc_at_398 trc_at_39c
      (by decide) (by decide) (by rc_r hR1) hI (by trsimp; rw [hR1.2.1]; rfl) (by trsimp; exact ha1)
      (by trsimp) (by decide)
      (by rcases hsc with rfl | rfl <;> (rw [X.fG, X.gc (by decide)]; have := X.gw; omega))
      (by rcases hsc with rfl | rfl <;> (rw [X.fG]; exact X.gsep (Or.inr (by decide)) (by decide) (by decide)))
      (by rcases hsc with rfl | rfl <;> (rw [X.fG, X.fG]; exact X.gsep (by decide) (by decide) (by decide)))
      (fun m3 hI3 hC3 => ?_)
    refine WP.aluImm trc_at_3a0 ?_; wn
    refine WP.aluImm trc_at_3a2 ?_; wn
    refine WP.aluImm trc_at_3a4 ?_; wn
    refine X.callMc (off := 0x3A8) (dd := 0x30) (N := 0x30) (src := F + BitVec.ofNat 32 0x60) trc_at_3a8 trc_at_3ac
      (by decide) (by decide) (by rc_r hR1) hI3 (by trsimp; rw [hR1.2.1]; rfl) (by trsimp; rw [hR1.2.1]; rfl)
      (by trsimp) (by decide) (by rw [X.fG, X.gc (by decide)]; have := X.gw; omega)
      (by rw [X.fG]; exact X.gsep (Or.inr (by decide)) (by decide) (by decide))
      (by rw [X.fG, X.fG]; exact X.gsep (by decide) (by decide) (by decide)) (fun m4 hI4 hC4 => ?_)
    have hO : ∀ {cc : Nat}, cc + 4 ≤ 0x30 → memLoad32 m4.mem (F + BitVec.ofNat 32 cc) = memLoad32 M (F + BitVec.ofNat 32 cc) :=
      fun hcc => (X.cpLdO hC4 (Or.inl hcc) (by decide) (by omega)).trans
        (X.cpLdO hC3 (Or.inl (by omega)) (by decide) (by omega))
    have hF4 : RcRec m4.mem (F + BitVec.ofNat 32 0x30) c' := hS.copy fun kk hk4 hk44 => by
      rw [add_ofNat_assoc, X.cpLd hC4 ⟨by omega, by omega⟩ (by decide), Nat.add_sub_cancel_left, add_ofNat_assoc,
        X.cpLd hC3 ⟨by omega, by omega⟩ (by decide), Nat.add_sub_cancel_left]
    have hB4 : RcBuf m4.mem fr fp fl dec := X.bufG hB ((X.mcG (by decide) hC3).trans (X.mcG (by decide) hC4))
    refine WP.lw trc_at_3b0 (by trsimp; rw [hR1.2.1]; exact X.fal (c := 0x20) (by decide)) ?_; wn
    refine WP.aluImm trc_at_3b2 ?_; wn
    refine WP.aluImm trc_at_3b4 ?_; wn
    refine WP.aluImm trc_at_3b8 ?_; wn
    refine WP.aluImm trc_at_3bc ?_; wn
    refine WP.lui trc_at_3c0 ?_; wn
    refine WP.aluImm trc_at_3c4 ?_; wn
    have e22 : memLoad32 m4.mem (F + 32) + 4294967295 = BitVec.ofNat 32 (k - 1) :=
      ((congrArg (· + (4294967295 : Word)) ((hO (cc := 0x20) (by decide)).trans hm20))).trans (rc_dec hk)
    have hInv : ∀ f2 : Fin 32 → Word, RcRegs F out fr g0 f2 → RcWin nb na f2 → f2 20 = F + BitVec.ofNat 32 0xE5 →
        f2 9 = F + BitVec.ofNat 32 0xA5 → f2 23 = F + BitVec.ofNat 32 0xE5 → f2 8 = rcRawKey →
        f2 22 = BitVec.ofNat 32 (k - 1) →
        RcLoopInv M0 G F out fr fp fl g0 ap an (k - 1) ⟨pos, dec, first.or (some c), nb, na⟩ m4.mem f2 :=
      fun f2 a b c d e g h => ⟨a, hI4, b, c, d, e, g, h, (hO (by decide)).trans hm24, (hO (by decide)).trans hm28,
        (hO (by decide)).trans hm2C, hpos, by rw [hc']; exact hF4, hB4⟩
    refine WP.branch trc_at_3c8 (fun ht => ?_) (fun hf => ?_)
    · have hne : k - 1 ≠ 0 := fun h0 => by
        revert ht; trsimp; rw [hR1.2.1]
        show branchTaken .bne (memLoad32 m4.mem (F + 32) + 4294967295) 0 = true → False
        rw [e22, h0]; decide
      wn
      exact kTop _ _ (hInv _ (by rc_r hR1) (by rc_w hW1) (by trsimp; rw [hR1.2.1]; rfl)
        (by trsimp; rw [hR1.2.1]; rfl) (by trsimp; rw [hR1.2.1]; rfl) (by trsimp <;> decide)
        (by trsimp; rw [hR1.2.1]; exact e22)) hne
    · have h0 : k - 1 = 0 := Classical.byContradiction fun hne => by
        revert hf; trsimp; rw [hR1.2.1]
        show branchTaken .bne (memLoad32 m4.mem (F + 32) + 4294967295) 0 = false → False
        rw [e22, rck_bneT (rc_k0 hk.2 hne)]; decide
      wn
      refine WP.jal trc_at_3cc (by decide) ?_; wn
      exact kFin _ _ (hInv _ (by rc_r hR1) (by rc_w hW1) (by trsimp; rw [hR1.2.1]; rfl)
        (by trsimp; rw [hR1.2.1]; rfl) (by trsimp; rw [hR1.2.1]; rfl) (by trsimp <;> decide)
        (by trsimp; rw [hR1.2.1]; exact e22)) h0
  refine WP.aluImm trc_at_38c ?_; wn
  refine WP.branch trc_at_38e (fun ht => ?_) (fun hf => ?_)
  · have h0 : memLoad32 M (F + BitVec.ofNat 32 0x30) = 0 := by
      revert ht; trsimp; rw [ha0]; simp only [branchTaken, beq_iff_eq]; exact id
    have e : c' = c := by rw [hF.ld0.mp h0] at hc'; exact (Option.some.inj hc').symm
    wn
    exact kM 0xE0 _ (Or.inl rfl) (by rc_r hR) (by rc_w hW) (by trsimp; rw [hR.2.1]; rfl) (e ▸ hC)
  · cases first with
    | none =>
      revert hf; trsimp; rw [ha0, (hF : memLoad32 M (F + BitVec.ofNat 32 0x30) = 0)]
      intro h; exact absurd h (by decide)
    | some c0 =>
      have e : c' = c0 := (Option.some.inj hc').symm
      wn
      refine WP.aluImm trc_at_390 ?_; wn
      exact kM 0x30 _ (Or.inr rfl) (by rc_r hR) (by rc_w hW) (by trsimp; rw [hR.2.1]; rfl) (e ▸ hF)

theorem RcCtx.fal2 (X : RcCtx M0 G F out fr fp fl p n g0) {c d : Nat} (h4 : (c + d) % 4 = 0) :
    (aluEval .add F (BitVec.ofNat 32 c) + BitVec.ofNat 32 d).toNat % 4 = 0 := by
  show (F + BitVec.ofNat 32 c + BitVec.ofNat 32 d).toNat % 4 = 0
  rw [add_ofNat_assoc]; exact X.fal h4

theorem RcCtx.flo2 (X : RcCtx M0 G F out fr fp fl p n g0) {c d k : Nat} (h : c + d + k ≤ 0x180) :
    Sep (aluEval .add F (BitVec.ofNat 32 c) + BitVec.ofNat 32 d) k TRC trustedRootReadChainCode.length := by
  show Sep (F + BitVec.ofNat 32 c + BitVec.ofNat 32 d) k TRC trustedRootReadChainCode.length
  rw [add_ofNat_assoc]; exact X.flo h

/-- From 0x348: the certificate `c` in the registers and the frame, and the
new window `nb`–`na`. Stores the `Cert` at `F + 0xE0`, copies the first
certificate through `F + 0x60` to `F + 0x30`, and counts down. -/
theorem RcCtx.pRecMem (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {nb na k pos an : Nat} {c : RcCert} {first : Option RcCert} {ap : Word} {dec : Bytes}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) (hW : RcWin nb na f)
    (h20 : f 20 = c.serial) (h22 : f 22 = BitVec.ofNat 32 c.serialLen)
    (hm18 : memLoad32 M (F + BitVec.ofNat 32 0x18) = c.issuer)
    (hm1C : memLoad32 M (F + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 c.issuerLen)
    (hm10 : memLoad32 M (F + BitVec.ofNat 32 0x10) = c.subject)
    (hm14 : memLoad32 M (F + BitVec.ofNat 32 0x14) = BitVec.ofNat 32 c.subjectLen)
    (h9 : f 9 = BitVec.ofNat 32 (c.notBefore % 2 ^ 32)) (h8 : f 8 = BitVec.ofNat 32 (c.notBefore / 2 ^ 32))
    (h23 : f 23 = BitVec.ofNat 32 (c.notAfter % 2 ^ 32)) (h18 : f 18 = BitVec.ofNat 32 (c.notAfter / 2 ^ 32))
    (hcb : c.notBefore < 2 ^ 64) (hca : c.notAfter < 2 ^ 64) (ha1 : f a1 = c.key) (hs0 : c.serial ≠ 0)
    (hm20 : memLoad32 M (F + BitVec.ofNat 32 0x20) = BitVec.ofNat 32 k) (hk : 1 ≤ k ∧ k ≤ 4)
    (hm24 : memLoad32 M (F + BitVec.ofNat 32 0x24) = ap)
    (hm28 : memLoad32 M (F + BitVec.ofNat 32 0x28) = BitVec.ofNat 32 an)
    (hm2C : memLoad32 M (F + BitVec.ofNat 32 0x2C) = BitVec.ofNat 32 pos) (hpos : pos < 2 ^ 32)
    (hF : RcFirst M (F + BitVec.ofNat 32 0x30) first) (hB : RcBuf M fr fp fl dec)
    (kTop : ∀ M' f', RcLoopInv M0 G F out fr fp fl g0 ap an (k - 1) ⟨pos, dec, first.or (some c), nb, na⟩ M' f' →
      k - 1 ≠ 0 → WP trustedRootReadChainCode TRC Q M' 0xFA f')
    (kFin : ∀ M' f', RcLoopInv M0 G F out fr fp fl g0 ap an (k - 1) ⟨pos, dec, first.or (some c), nb, na⟩ M' f' →
      k - 1 = 0 → WP trustedRootReadChainCode TRC Q M' 0x4D8 f') :
    WP trustedRootReadChainCode TRC Q M 0x348 f := by
  refine WP.aluImm trc_at_348 ?_; wn
  refine WP.aluImm trc_at_34c ?_; wn
  refine WP.aluImm trc_at_350 ?_; wn
  refine WP.sw trc_at_354 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xE0) (k := 4) (by decide)) ?_; wn
  refine WP.sb trc_at_356 (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xE4) (k := 1) (by decide)) ?_; wn
  refine WP.sb trc_at_35a (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xE5) (k := 1) (by decide)) ?_; wn
  refine WP.sb trc_at_35e (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xE6) (k := 1) (by decide)) ?_; wn
  refine WP.sb trc_at_362 (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xE7) (k := 1) (by decide)) ?_; wn
  refine WP.lw trc_at_366 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0x18) (by decide)) ?_; wn
  refine WP.sw trc_at_368 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE8) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xE8) (k := 4) (by decide)) ?_; wn
  refine WP.lw trc_at_36a (by trsimp; rw [hR.2.1]; exact X.fal (c := 0x1C) (by decide)) ?_; wn
  refine WP.sw trc_at_36c (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xEC) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xEC) (k := 4) (by decide)) ?_; wn
  refine WP.lw trc_at_36e (by trsimp; rw [hR.2.1]; exact X.fal (c := 0x10) (by decide)) ?_; wn
  refine WP.sw trc_at_370 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xF0) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xF0) (k := 4) (by decide)) ?_; wn
  refine WP.lw trc_at_372 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0x30) (by decide)) ?_; wn
  refine WP.lw trc_at_374 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0x14) (by decide)) ?_; wn
  refine WP.sw trc_at_376 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xF4) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xF4) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_378 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xF8) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xF8) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_37a (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xFC) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xFC) (k := 4) (by decide)) ?_; wn
  refine WP.aluImm trc_at_37c ?_; wn
  refine WP.sw trc_at_37e (by trsimp; rw [hR.2.1]; exact X.fal2 (c := 0x100) (d := 0) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo2 (c := 0x100) (d := 0) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_382 (by trsimp; rw [hR.2.1]; exact X.fal2 (c := 0x100) (d := 4) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo2 (c := 0x100) (d := 4) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_386 (by trsimp; rw [hR.2.1]; exact X.fal2 (c := 0x100) (d := 8) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo2 (c := 0x100) (d := 8) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_388 (by trsimp; rw [hR.2.1]; exact X.fal2 (c := 0x100) (d := 0xC) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo2 (c := 0x100) (d := 0xC) (k := 4) (by decide)) ?_; wn
  rw [hR.2.1]
  simp only [BitVec.ofNat_eq_ofNat]
  rw [rc_sb4 _ _ _ 228 229 230 231 rfl rfl rfl]
  simp only [aluEval, add_ofNat_assoc, Nat.reduceAdd]
  simp (disch := decide) only [rcf_ld32o]
  rw [hm18, hm1C, hm10, hm14, h20, h22, h9, h8, h23, h18, ha1]
  refine X.pRecCopy (by rc_r hR) ?_ (by rc_w hW) (by trsimp; rc_ld) ?_ (by rc_ld; exact hm20) hk
    (by rc_ld; exact hm24) (by rc_ld; exact hm28) (by rc_ld; exact hm2C) hpos
    (hF.copy fun kk _ _ => by
      simp only [add_ofNat_assoc]; simp (disch := first | decide | omega) only [rcf_ld32o])
    (X.bufG hB (by rc_g)) kTop kFin
  · repeat (refine X.stI ?_ (by decide) (X.sw32 _ _ _))
    exact hI
  · exact ⟨by rc_ld, by rc_ld, by rc_ld, by rc_ld, by rc_ld, by rc_ld, by rc_ld, by rc_ld, by rc_ld, by rc_ld,
      by rc_ld, hcb, hca, hs0⟩

end

end C3.RV32
