import C3BootProofs.Proofs.TrustedRootReadChainFrame

/-!
# `p384_key` inside `read_chain`

`parse_cert` reads the subject public key with `p384_key`, which the
compiler inlined at 0x2E0 to 0x47E of `read_chain`. Every path through it
reaches 0x308 with the key's address or 0 in `a1`, the value `rcKey`
gives. The frame's words at `F + 0x10` and above and the registers in
`rcKL` are as they were at 0x2E0.
-/

namespace C3.RV32

open C3.Image C3.Json C3.RV32.Dq C3.RV32.P3

set_option maxRecDepth 20000

/-- The bit-string part of `rcKey`, from the reader `b` after the
algorithm. -/
def rcKeyB (L : Bytes) (p : Word) (b : RcRd) : Word :=
  match derElement 3 (rcView L b) with
  | .error _ => 0
  | .ok bt =>
    if ¬(bt.len ≠ 0 ∧ (rcView L b).getD bt.header 0 = 0) then 0
    else if bt.len - 1 ≠ 0x61 then 0
    else if b.2 - (bt.header + bt.len) ≠ 0 then 0
    else if rcFsOk (rcView L (b.1 + bt.header + 1, 0x61)) then p + BitVec.ofNat 32 (b.1 + bt.header + 1)
    else 0

/-- The algorithm part of `rcKey`, from the reader `r` over the key's
contents. -/
def rcKeyA (L : Bytes) (p : Word) (r : RcRd) : Word :=
  match derElement 0x30 (rcView L r) with
  | .error _ => 0
  | .ok a =>
    match rcAlg L r with
    | .error _ => 0
    | .ok ((oo, ol), par) =>
      if rcCurveOk L par = false then 0
      else if rcView L (oo, ol) ≠ oidEcPublicKey then 0
      else rcKeyB L p (rcAdv r a)

theorem rcKey_eq (L : Bytes) (p : Word) (r : RcRd) :
    rcKey L p r = match derElement 0x30 (rcView L r) with
      | .error _ => 0
      | .ok s => if r.2 - (s.header + s.len) ≠ 0 then 0 else rcKeyA L p (rcIn r s) := rfl

/-- The registers that the inlined `p384_key` keeps. -/
abbrev rcKL : List Nat := [8, 9, 18, 19, 20, 21, 22, 23, 24, 27]

/-- What follows the inlined `p384_key`: the block at 0x308, entered with
the key `v` in `a1`, the registers of `rcKL` as in `w`, and memory that
changed from `M` only below `F + 0x10` and in the scratch area. -/
def RcKeyK (M0 : Word → BitVec 8) (G F out fr fp : Word) (fl : Nat) (g0 w : Fin 32 → Word) (Q : Post)
    (M : Word → BitVec 8) (v : Word) : Prop :=
  ∀ (M' : Word → BitVec 8) (f' : Fin 32 → Word), RcRegs F out fr g0 f' → RcMemInv M0 G F fr fp fl g0 M' →
    RcKB G 0x10 M M' → RcK rcKL w f' → f' a1 = v → WP trustedRootReadChainCode TRC Q M' 0x308 f'

theorem RcKeyK.mono {M0 : Word → BitVec 8} {G F out fr fp : Word} {fl : Nat} {g0 w : Fin 32 → Word}
    {Q : Post} {M M1 : Word → BitVec 8} {v : Word} (k : RcKeyK M0 G F out fr fp fl g0 w Q M v)
    (h : RcKB G 0x10 M M1) : RcKeyK M0 G F out fr fp fl g0 w Q M1 v :=
  fun M' f' a b c d e => k M' f' a b (h.trans c) d e

/-- Proves `RcRegs` of a register file that `upd` and `clob` build from one
that `h` covers. -/
macro "rc_r " h:term : tactic => `(tactic| (
  repeat (first
    | refine RcRegs.clob ?_
    | refine RcRegs.set ?_ (by decide))
  exact $h))

theorem rck_beqT : branchTaken .beq (0 : Word) 0 = true := rfl
theorem rck_bneF : branchTaken .bne (0 : Word) 0 = false := rfl

theorem rck_beqF {x : Word} (h : x ≠ 0) : branchTaken .beq x 0 = false := by
  simp only [branchTaken, beq_eq_false_iff_ne]; exact h

theorem rck_bneT {x : Word} (h : x ≠ 0) : branchTaken .bne x 0 = true := by
  simp only [branchTaken, bne_iff_ne, ne_eq]; exact h

theorem rck_pne {M : Word → BitVec 8} {G B : Word} {L : Bytes} (hL : RcL M G B L) {i : Nat}
    (hi : i ≤ L.length) : B + BitVec.ofNat 32 i ≠ 0 := fun e => by
  have := hL.w hi; have := hL.pos; rw [e] at *; simp at *; omega

theorem rck_nz {x : Nat} (h : x ≠ 0) (hx : x < 2 ^ 32) : BitVec.ofNat 32 x ≠ 0 := fun e => by
  have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this
  rw [show (0 : Word).toNat = 0 from rfl] at this; omega

theorem rck_m61 {x : Nat} (h : x ≠ 0x61) (hx : x < 2 ^ 32) : BitVec.ofNat 32 x + 0xFFFFFF9F ≠ 0 := fun e => by
  have h2 : BitVec.ofNat 32 x = 0x61 := by
    have := congrArg (· + (0x61 : Word)) e
    rwa [BitVec.add_assoc, show (0xFFFFFF9F : Word) + 0x61 = 0 from by decide,
      show BitVec.ofNat 32 x + (0 : Word) = BitVec.ofNat 32 x from BitVec.add_zero _,
      show (0 : Word) + 0x61 = 0x61 from rfl] at this
  have := congrArg BitVec.toNat h2
  rw [BitVec.toNat_ofNat, show (0x61 : Word).toNat = 0x61 from rfl] at this; omega

theorem rck_e61 : BitVec.ofNat 32 0x61 + 0xFFFFFF9F = (0 : Word) := by decide

theorem rck_z0 {f : Fin 32 → Word} (h : f 0 = 0) : aluEval .add (f 0) 0 = 0 := by rw [h]; rfl

theorem rck_ze {v : BitVec 8} {c : Nat} (hc : c < 256) : v.zeroExtend 32 = BitVec.ofNat 32 c ↔ v.toNat = c := by
  constructor
  · intro e; have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
    have := v.isLt; omega
  · intro e; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; have := v.isLt; omega

theorem rck_sepG {M : Word → BitVec 8} {G B : Word} {L : Bytes} (hL : RcL M G B L) {i l : Nat}
    (h : i + l ≤ L.length + 14) : Sep (B + BitVec.ofNat 32 i) l G 0x5C0 := by
  have := (hL.sep.sub (c := i) (l := l) h).subR (c := 0) (l := 0x5C0) (by decide)
  rwa [add_ofNat_zero] at this

theorem rck_andT (x : Word) : x &&& ((0 : Word) + 0xFFFFFFFF) = x := by
  rw [show (0 : Word) + 0xFFFFFFFF = 0xFFFFFFFF from rfl]; exact and_ones x

theorem rck_andF (x : Word) : x &&& ((1 : Word) + 0xFFFFFFFF) = 0 := by
  rw [show (1 : Word) + 0xFFFFFFFF = 0#32 from by decide, BitVec.and_zero]; rfl

theorem rck_tag {V : Bytes} {u : DerTlv} (h : derTlv V = .ok u) (hV : ∀ x ∈ V, x < 256) : u.tag < 256 := by
  cases V with
  | nil => cases h
  | cons c rest => rw [derTlv_tag h]; exact hV c (List.mem_cons_self ..)

theorem rck_viewLt {L : Bytes} (hL : ∀ x ∈ L, x < 256) (r : RcRd) : ∀ x ∈ rcView L r, x < 256 :=
  fun x hx => hL x (List.mem_of_mem_drop (List.mem_of_mem_take hx))

/-- The parameters' tag that `Der::algorithm` returns is a byte. -/
theorem rck_algTag {L : Bytes} {r : RcRd} {x : Nat × Nat} {q : Nat} {u : DerTlv}
    (h : rcAlg L r = .ok (x, some (q, u))) (hL : ∀ x ∈ L, x < 256) : u.tag < 256 := by
  unfold rcAlg at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hU
  split at h
  · cases h; exact rck_tag hU (rck_viewLt hL _)
  · cases h

theorem RcL.lt {M : Word → BitVec 8} {G B : Word} {L : Bytes} (hL : RcL M G B L) : ∀ x ∈ L, x < 256 := by
  rw [← hL.bytes]; exact memBytes_mem_lt

theorem rck_kl_cases : ∀ q : Fin 32, q.val ∈ rcKL →
    q = 8 ∨ q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 20 ∨ q = 21 ∨ q = 22 ∨ q = 23 ∨ q = 24 ∨ q = 27 := by decide

/-- `s3` and `s5` reloaded from the frame. -/
theorem RcK.restore {w f : Fin 32 → Word} {v19 v21 : Word} (h : RcK [8, 9, 18, 20, 22, 23, 24, 27] w f)
    (e19 : v19 = w 19) (e21 : v21 = w 21) : RcK rcKL w (upd (upd f 19 v19) 21 v21) := fun q hq => by
  rcases rck_kl_cases q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp +decide only [upd_app, ↓reduceIte] <;> first | exact e19 | exact e21 | exact h _ (by decide)

/-- `s3` and `s5` saved in the frame. -/
theorem RcK.drop {w f : Fin 32 → Word} (h : RcK rcKL w f) : RcK [8, 9, 18, 20, 22, 23, 24, 27] w f :=
  h.mono (by decide)

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

/-- 0x306 sets `a1` to 0 and goes on to 0x308. -/
theorem RcCtx.key306 (_X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f w : Fin 32 → Word}
    {Q : Post} (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) (hK : RcK rcKL w f)
    (k : RcKeyK M0 G F out fr fp fl g0 w Q M 0) : WP trustedRootReadChainCode TRC Q M 0x306 f := by
  refine WP.aluImm trc_at_306 ?_
  exact k _ _ (by rc_r hR) hI RcKB.refl (by rc_k hK) (by trsimp <;> exact rck_z0 hR.1)

/-- From 0x440, after `Der::bit_string`: the bit string's checks and
`p384_from_sec1`. -/
theorem RcCtx.keyBits (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f w : Fin 32 → Word}
    {Q : Post} {B : Word} {L : Bytes} {b : RcRd}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) (hK : RcK rcKL w f) (hL : RcL M G B L)
    (hB : RcBitsOut M (F + BitVec.ofNat 32 0xE0) (F + BitVec.ofNat 32 0x60) B L b (rcElem L 3 b))
    (hb : b.1 + b.2 ≤ L.length)
    (k : RcKeyK M0 G F out fr fp fl g0 w Q M (rcKeyB L B b)) : WP trustedRootReadChainCode TRC Q M 0x440 f := by
  have hw := hL.hw
  refine WP.lw trc_at_440 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
  refine WP.aluImm trc_at_442 ?_; wn
  rcases hE : derElement 3 (rcView L b) with e | bt
  · simp only [rcElem, hE] at hB
    have hv : rcKeyB L B b = 0 := by simp only [rcKeyB, hE]
    rw [hv] at k
    refine WP.branch trc_at_444 (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hB.1]; decide)); wn
    exact k _ _ (by rc_r hR) hI RcKB.refl (by rc_k hK) (by trsimp <;> exact rck_z0 hR.1)
  · have hbd := derElement_bound hE
    rw [rcd_view_len hb] at hbd
    simp only [rcElem, hE] at hB
    by_cases hc : bt.len ≠ 0 ∧ (rcView L b).getD bt.header 0 = 0
    · simp only [RcBitsOut] at hB
      rw [ite_eq_left hc] at hB
      obtain ⟨e0, e4, eR, -⟩ := hB
      have e0' : memLoad32 M (F + 0xE0) = B + BitVec.ofNat 32 (b.1 + bt.header + 1) := e0
      have e4' : memLoad32 M (F + 0xE4) = BitVec.ofNat 32 (bt.len - 1) := by
        rw [show F + (0xE4 : Word) = F + BitVec.ofNat 32 0xE0 + 4 from (add_ofNat_assoc F 0xE0 4).symm]; exact e4
      have e6c : memLoad32 M (F + 0x6C) = BitVec.ofNat 32 (b.2 - (bt.header + bt.len)) := by
        rw [show F + (0x6C : Word) = F + BitVec.ofNat 32 0x60 + 0xC from (add_ofNat_assoc F 0x60 0xC).symm]
        exact eR.2.1
      refine WP.branch trc_at_444 (fun ht => absurd ht (by
        trsimp; rw [hR.2.1, e0', rck_beqF (rck_pne hL (by omega))]; decide)) (fun _ => ?_); wn
      refine WP.lw trc_at_448 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0xE4) (by decide)) ?_; wn
      refine WP.aluImm trc_at_44a ?_; wn
      by_cases h61 : bt.len - 1 ≠ 0x61
      · have hv : rcKeyB L B b = 0 := by
          unfold rcKeyB; rw [hE]; dsimp only
          rw [ite_eq_right (fun h => h hc), ite_eq_left h61]
        rw [hv] at k
        refine WP.branch trc_at_44e (fun _ => ?_) (fun hf => absurd hf (by
          trsimp; rw [hR.2.1, e4', ev_add, rck_bneT (rck_m61 h61 (by omega))]; decide)); wn
        exact k _ _ (by rc_r hR) hI RcKB.refl (by rc_k hK) (by trsimp <;> exact rck_z0 hR.1)
      replace h61 : bt.len - 1 = 0x61 := Decidable.of_not_not h61
      refine WP.branch trc_at_44e (fun ht => absurd ht (by
        trsimp; rw [hR.2.1, e4', h61]; decide)) (fun _ => ?_); wn
      refine WP.lw trc_at_452 (by (try trsimp); rw [hR.2.1]; exact X.fal (c := 0x6C) (by decide)) ?_; wn
      by_cases hz : b.2 - (bt.header + bt.len) ≠ 0
      · have hv : rcKeyB L B b = 0 := by
          unfold rcKeyB; rw [hE]; dsimp only
          rw [ite_eq_right (fun h => h hc), ite_eq_right (fun h => h h61), ite_eq_left hz]
        rw [hv] at k
        refine WP.branch trc_at_454 (fun _ => ?_) (fun hf => absurd hf (by
          trsimp; rw [hR.2.1, e6c, rck_bneT (rck_nz hz (by omega))]; decide)); wn
        exact k _ _ (by rc_r hR) hI RcKB.refl (by rc_k hK) (by trsimp <;> exact rck_z0 hR.1)
      replace hz : b.2 - (bt.header + bt.len) = 0 := Decidable.of_not_not hz
      refine WP.branch trc_at_454 (fun ht => absurd ht (by
        trsimp; rw [hR.2.1, e6c, hz]; decide)) (fun _ => ?_); wn
      have hlen : bt.len = 0x62 := by omega
      have hview : memBytes M (B + BitVec.ofNat 32 (b.1 + bt.header + 1)) 0x61 =
          rcView L (b.1 + bt.header + 1, 0x61) := hL.view2 (by omega)
      have hg0 : (rcView L (b.1 + bt.header + 1, 0x61)).getD 0 0 =
          (M (B + BitVec.ofNat 32 (b.1 + bt.header + 1) + 0)).toNat := by
        rw [← hview]; exact memBytes_getD (by decide)
      refine WP.lbu trc_at_458 ?_; wn
      refine WP.aluImm trc_at_45c ?_; wn
      by_cases h4 : (M (B + BitVec.ofNat 32 (b.1 + bt.header + 1) + 0)).toNat ≠ 4
      · have hv : rcKeyB L B b = 0 := by
          unfold rcKeyB; rw [hE]; dsimp only
          rw [ite_eq_right (fun h => h hc), ite_eq_right (fun h => h h61), ite_eq_right (fun h => h hz),
            ite_eq_right (fun h => h4 (hg0 ▸ h.1))]
        rw [hv] at k
        refine WP.branch trc_at_45e (fun _ => ?_) (fun hf => absurd hf (by
          trsimp; rw [hR.2.1, e0', show (4 : Word) = BitVec.ofNat 32 4 from rfl]
          simp only [branchTaken, bne_eq_false_iff_eq]
          exact fun e => h4 ((rck_ze (by decide)).mp e))); wn
        exact X.key306 (by rc_r hR) hI (by rc_k hK) k
      replace h4 : (M (B + BitVec.ofNat 32 (b.1 + bt.header + 1) + 0)).toNat = 4 := Decidable.of_not_not h4
      have hv : rcKeyB L B b = if rcFsOk (rcView L (b.1 + bt.header + 1, 0x61)) then
          B + BitVec.ofNat 32 (b.1 + bt.header + 1) else 0 := by
        unfold rcKeyB; rw [hE]; dsimp only
        rw [ite_eq_right (fun h => h hc), ite_eq_right (fun h => h h61), ite_eq_right (fun h => h hz)]
      rw [hv] at k
      refine WP.branch trc_at_45e (fun ht => absurd ht (by
        trsimp; rw [hR.2.1, e0', show (4 : Word) = BitVec.ofNat 32 4 from rfl, (rck_ze (by decide)).mpr h4]
        decide)) (fun _ => ?_); wn
      refine WP.aluImm trc_at_462 ?_; wn
      refine WP.alu trc_at_464 ?_; wn
      refine WP.sw trc_at_466 (by trsimp; rw [hR.2.1]; exact X.fal (c := 4) (by decide))
        (by trsimp; rw [hR.2.1]; exact X.flo (c := 4) (k := 4) (by decide)) ?_; wn
      rw [hR.2.1, e0']
      have hKB3 : RcKB G 0x10 M (memStore32 M (F + 4) (B + BitVec.ofNat 32 (b.1 + bt.header + 1))) :=
        X.stB (c := 4) (k := 4) (by decide) (X.sw32 M 4 _)
      have hI3 : RcMemInv M0 G F fr fp fl g0 (memStore32 M (F + 4) (B + BitVec.ofNat 32 (b.1 + bt.header + 1))) :=
        X.stI hI (c := 4) (k := 4) (by decide) (X.sw32 M 4 _)
      have hL3 := hL.kb hKB3 (by decide)
      refine X.callFs (off := 0x468) (oc := 0xE0) (inp := B + BitVec.ofNat 32 (b.1 + bt.header + 1))
        trc_at_468 trc_at_46c (by decide) (by decide) (by rc_r hR) hI3 (by decide)
        (by trsimp; rfl) (by trsimp) (rck_sepG hL (by omega)) (by rw [hL.w (by omega)]; omega)
        (fun m2 hK2 _ hI2 hres => ?_)
      rw [hL3.view2 (by omega)] at hres
      have h4m : memLoad32 m2.mem (F + 4) = B + BitVec.ofNat 32 (b.1 + bt.header + 1) :=
        (X.keepLd hK2 (c := 4) (by decide)).trans (memLoad32_store32_same _ _ _)
      refine WP.lw trc_at_470 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
      refine WP.aluImm trc_at_472 ?_; wn
      refine WP.lw trc_at_474 (by trsimp; rw [hR.2.1]; exact X.fal (c := 4) (by decide)) ?_; wn
      refine WP.alu trc_at_476 ?_; wn
      refine WP.jal trc_at_478 (by decide) ?_; wn
      refine k _ _ (by rc_r hR) hI2 (hKB3.trans hK2.kb) (by rc_k hK) ?_
      trsimp
      rw [hR.2.1, h4m, show F + (0xE0 : Word) = F + BitVec.ofNat 32 0xE0 from rfl, hres]
      by_cases hfs : rcFsOk (rcView L (b.1 + bt.header + 1, 0x61))
      · rw [ite_eq_left hfs, ite_eq_left hfs]; exact rck_andT _
      · rw [ite_eq_right hfs, ite_eq_right hfs]; exact rck_andF _
    · simp only [RcBitsOut] at hB
      rw [ite_eq_right hc] at hB
      have hv : rcKeyB L B b = 0 := by simp only [rcKeyB, hE, hc, not_false_eq_true, ite_true]
      rw [hv] at k
      refine WP.branch trc_at_444 (fun _ => ?_) (fun hf => absurd hf (by
        trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hB.1]; decide)); wn
      exact k _ _ (by rc_r hR) hI RcKB.refl (by rc_k hK) (by trsimp <;> exact rck_z0 hR.1)

/-- Read-only data is apart from the stack below the frame. -/
theorem RcCtx.roG (X : RcCtx M0 G F out fr fp fl p n g0) {a : Word} {l : Nat}
    (h : roWindowAddress ≤ a.toNat ∧ a.toNat + l ≤ roWindowAddress + 0x1400) : Sep a l G 0x5C0 :=
  (sep_low (rc_roSub X.ro h) (by decide)).symm

/-- A frame word that a call leaving everything above `G + 0x5C0` alone keeps. -/
theorem RcCtx.eqLd (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8}
    (hE : ∀ x, Sep G 0x5C0 x 1 → M' x = M x) {c : Nat} (hc : c + 4 ≤ 0x180) :
    memLoad32 M' (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by
    rw [X.fG, add_ofNat_assoc]
    exact hE _ (rc_g0' (sep_offsets G (c := 0) (n := 0x5C0) (d := 0x5C0 + c + j) (k := 1)
      (Or.inl (by omega)) (by omega) (by omega)))

/-- A frame reader that such a call keeps. -/
theorem RcCtx.eqRd (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8}
    (hE : ∀ x, Sep G 0x5C0 x 1 → M' x = M x) {c : Nat} {B : Word} {L : Bytes} {b : RcRd}
    (hr : RcRdAt M (F + BitVec.ofNat 32 c) B L b) (hc : c + 0x10 ≤ 0x180) : RcRdAt M' (F + BitVec.ofNat 32 c) B L b :=
  hr.keep (by rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, rcf_e]; exact X.eqLd hE (by omega))
    (by rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, rcf_e]; exact X.eqLd hE (by omega))

/-- From 0x434: `Der::bit_string` on the reader at `F + 0x60`, then the
checks from 0x440. -/
theorem RcCtx.keyBitsAt (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f w : Fin 32 → Word}
    {Q : Post} {B : Word} {L : Bytes} {b : RcRd}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) (hK : RcK rcKL w f) (hL : RcL M G B L)
    (hr : RcRdAt M (F + BitVec.ofNat 32 0x60) B L b)
    (k : RcKeyK M0 G F out fr fp fl g0 w Q M (rcKeyB L B b)) : WP trustedRootReadChainCode TRC Q M 0x434 f := by
  refine WP.aluImm trc_at_434 ?_; wn
  refine WP.aluImm trc_at_436 ?_; wn
  refine X.callBits (off := 0x438) (oc := 0xE0) (dc := 0x60) trc_at_438 trc_at_43c (by decide) (by decide)
    (by rc_r hR) hI (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl)
    hL hr (fun m2 hK2 _ hI2 hB => ?_)
  exact X.keyBits (by rc_r hR) hI2 (by rc_k hK) (hL.keep hK2) hB hr.2.2 (k.mono hK2.kb)

/-- From 0x410: compares the algorithm's OID with `id-ecPublicKey`, with
`s3` 0 exactly when the parameters name `secp384r1`, and `s3` and `s5`
saved at `F + 8` and `F + 0xC`. -/
theorem RcCtx.keyOid (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f w : Fin 32 → Word}
    {Q : Post} {B : Word} {L : Bytes} {b : RcRd} {oo ol : Nat} {c : Bool}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hK : RcK [8, 9, 18, 20, 22, 23, 24, 27] w f)
    (h8 : memLoad32 M (F + BitVec.ofNat 32 8) = w 19) (hC : memLoad32 M (F + BitVec.ofNat 32 0xC) = w 21)
    (hL : RcL M G B L) (hr : RcRdAt M (F + BitVec.ofNat 32 0x60) B L b)
    (ha4 : f a4 = B + BitVec.ofNat 32 oo) (h21 : f 21 = BitVec.ofNat 32 ol) (hoo : oo + ol ≤ L.length)
    (h19 : f 19 = if c then 0 else 1)
    (k : RcKeyK M0 G F out fr fp fl g0 w Q M
      (if c = false then 0 else if rcView L (oo, ol) ≠ oidEcPublicKey then 0 else rcKeyB L B b)) :
    WP trustedRootReadChainCode TRC Q M 0x410 f := by
  have hw := hL.hw
  refine WP.aluImm trc_at_410 ?_; wn
  refine WP.alu trc_at_412 ?_; wn
  refine WP.alu trc_at_414 ?_; wn
  refine WP.lui trc_at_416 ?_; wn
  refine WP.aluImm trc_at_41a ?_; wn
  refine X.callSlNe (off := 0x41E) (pa := B + BitVec.ofNat 32 oo) (pl := ol) (qa := rcEcKey) (ql := 7)
    trc_at_41e trc_at_422 (by decide) (by decide) (by rc_r hR) hI
    (by trsimp; exact ha4) (by trsimp; exact h21) (by trsimp <;> decide) (by trsimp; rw [hR.1]; rfl)
    (by omega) (by decide) (rck_sepG hL (by omega)) (X.roG ⟨by decide, by decide⟩) (fun m2 hK2 hE hI2 hres => ?_)
  rw [hL.view2 hoo, (X.codeAt hI).ko] at hres
  refine WP.aluImm trc_at_426 ?_; wn
  cases c
  · refine WP.branch trc_at_428 (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [h19]; decide)); wn
    refine WP.lw trc_at_47a (by trsimp; rw [hR.2.1]; exact X.fal (c := 8) (by decide)) ?_; wn
    refine WP.lw trc_at_47c (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xC) (by decide)) ?_; wn
    refine WP.jal trc_at_47e (by decide) ?_; wn
    refine k _ _ (by rc_r hR) hI2 hK2.kb (RcK.restore (by rc_k hK) ?_ ?_) (by trsimp <;> exact rck_z0 hR.1)
    · (try trsimp); rw [hR.2.1]; exact (X.keepLd hK2 (c := 8) (by decide)).trans h8
    · (try trsimp); rw [hR.2.1]; exact (X.keepLd hK2 (c := 0xC) (by decide)).trans hC
  · refine WP.branch trc_at_428 (fun ht => absurd ht (by
      trsimp; rw [h19]; decide)) (fun _ => ?_); wn
    refine WP.lw trc_at_42c (by trsimp; rw [hR.2.1]; exact X.fal (c := 8) (by decide)) ?_; wn
    refine WP.lw trc_at_42e (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xC) (by decide)) ?_; wn
    have e19 : memLoad32 m2.mem (F + 8) = w 19 := (X.keepLd hK2 (c := 8) (by decide)).trans h8
    have e21 : memLoad32 m2.mem (F + 0xC) = w 21 := (X.keepLd hK2 (c := 0xC) (by decide)).trans hC
    by_cases hoid : rcView L (oo, ol) = oidEcPublicKey
    · rw [ite_eq_left hoid] at hres
      refine WP.branch trc_at_430 (fun ht => absurd ht (by
        trsimp; rw [hres]; decide)) (fun _ => ?_); wn
      refine X.keyBitsAt (w := w) (by rc_r hR) hI2 ?_ (hL.keep hK2)
        (X.eqRd hE hr (by decide)) ?_
      · refine RcK.restore (by rc_k hK) ?_ ?_
        · (try trsimp); rw [hR.2.1]; exact e19
        · (try trsimp); rw [hR.2.1]; exact e21
      · simp only [Bool.true_eq_false, ↓reduceIte, hoid, ne_eq, not_true_eq_false] at k
        exact k.mono hK2.kb
    · rw [ite_eq_right hoid] at hres
      refine WP.branch trc_at_430 (fun _ => ?_) (fun hf => absurd hf (by
        trsimp; rw [hres]; decide)); wn
      simp only [Bool.true_eq_false, ↓reduceIte, ne_eq, hoid, not_false_eq_true] at k
      refine k _ _ (by rc_r hR) hI2 hK2.kb (RcK.restore (by rc_k hK) ?_ ?_) (by trsimp <;> exact rck_z0 hR.1)
      · (try trsimp); rw [hR.2.1]; exact e19
      · (try trsimp); rw [hR.2.1]; exact e21

/-- From 0x3CE: `Der::algorithm` on the reader at `F + 0x60`, then the
curve and OID checks and the bit string. -/
theorem RcCtx.keyAlg (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f w : Fin 32 → Word}
    {Q : Post} {B : Word} {L : Bytes} {r : RcRd}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) (hK : RcK rcKL w f) (hL : RcL M G B L)
    (hr : RcRdAt M (F + BitVec.ofNat 32 0x60) B L r)
    (k : RcKeyK M0 G F out fr fp fl g0 w Q M (rcKeyA L B r)) : WP trustedRootReadChainCode TRC Q M 0x3CE f := by
  have hw := hL.hw
  refine WP.aluImm trc_at_3ce ?_; wn
  refine WP.aluImm trc_at_3d0 ?_; wn
  refine X.callAlg (off := 0x3D2) (oc := 0xE0) (dc := 0x60) trc_at_3d2 trc_at_3d6 (by decide) (by decide)
    (by rc_r hR) hI (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl)
    hL hr (fun m2 hK2 _ hI2 hA hAR => ?_)
  have hL2 := hL.keep hK2
  refine WP.lw trc_at_3da (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
  rcases hAlg : rcAlg L r with _ | ⟨⟨oo, ol⟩, par⟩
  · rw [hAlg] at hA
    have hA' : memLoad32 m2.mem (F + 0xE0) = 0 := hA
    have hv : rcKeyA L B r = 0 := by
      unfold rcKeyA; split
      · rfl
      · rw [hAlg]
    rw [hv] at k
    refine WP.branch trc_at_3dc (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR.2.1, hA']; decide)); wn
    exact X.key306 (by rc_r hR) hI2 (by rc_k hK) (k.mono hK2.kb)
  · rw [hAlg] at hA
    obtain ⟨e0, e4, hoo, hpar⟩ := hA
    have e0' : memLoad32 m2.mem (F + 0xE0) = B + BitVec.ofNat 32 oo := e0
    obtain ⟨a, ha⟩ : ∃ a, derElement 0x30 (rcView L r) = .ok a := by
      unfold rcAlg at hAlg; split at hAlg
      · cases hAlg
      · exact ⟨_, ‹_›⟩
    have hv : rcKeyA L B r = if rcCurveOk L par = false then 0
        else if rcView L (oo, ol) ≠ oidEcPublicKey then 0 else rcKeyB L B (rcAdv r a) := by
      unfold rcKeyA; rw [ha]; dsimp only; rw [hAlg]
    rw [hv] at k
    obtain ⟨hr2, -⟩ := hAR a ha
    refine WP.branch trc_at_3dc (fun ht => absurd ht (by
      trsimp; rw [hR.2.1, e0', rck_beqF (rck_pne hL (by omega))]; decide)) (fun _ => ?_); wn
    refine WP.sw trc_at_3de (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xC) (by decide))
      (by trsimp; rw [hR.2.1]; exact X.flo (c := 0xC) (k := 4) (by decide)) ?_; wn
    refine WP.sw trc_at_3e0 (by trsimp; rw [hR.2.1]; exact X.fal (c := 8) (by decide))
      (by trsimp; rw [hR.2.1]; exact X.flo (c := 8) (k := 4) (by decide)) ?_; wn
    rw [hR.2.1]
    have hKB3 : RcKB G 0x10 m2.mem (memStore32 (memStore32 m2.mem (F + 12) (f 21)) (F + 8) (f 19)) :=
      (X.stB (c := 0xC) (k := 4) (by decide) (X.sw32 _ 0xC _)).trans
        (X.stB (c := 8) (k := 4) (by decide) (X.sw32 _ 8 _))
    have hI3 : RcMemInv M0 G F fr fp fl g0 (memStore32 (memStore32 m2.mem (F + 12) (f 21)) (F + 8) (f 19)) :=
      X.stI (X.stI hI2 (c := 0xC) (k := 4) (by decide) (X.sw32 _ 0xC _)) (c := 8) (k := 4) (by decide)
        (X.sw32 _ 8 _)
    have hL3 := hL2.kb hKB3 (by decide)
    have ld3 : ∀ c, 0x10 ≤ c → c + 4 ≤ 0x180 →
        memLoad32 (memStore32 (memStore32 m2.mem (F + 12) (f 21)) (F + 8) (f 19)) (F + BitVec.ofNat 32 c) =
          memLoad32 m2.mem (F + BitVec.ofNat 32 c) := fun c h1 h2 =>
      (rcf_ld32o (d := 8) (Or.inr (by omega)) (by omega) (by decide)).trans
        (rcf_ld32o (d := 0xC) (Or.inr (by omega)) (by omega) (by decide))
    have h8 : memLoad32 (memStore32 (memStore32 m2.mem (F + 12) (f 21)) (F + 8) (f 19)) (F + BitVec.ofNat 32 8) =
        w 19 := (memLoad32_store32_same _ _ _).trans (hK 19 (by decide))
    have hC : memLoad32 (memStore32 (memStore32 m2.mem (F + 12) (f 21)) (F + 8) (f 19)) (F + BitVec.ofNat 32 0xC) =
        w 21 := (rcf_ld32o (B := F) (c := 0xC) (d := 8) (Or.inr (by decide)) (by decide) (by decide)).trans
          ((memLoad32_store32_same _ _ _).trans (hK 21 (by decide)))
    have hr3 : RcRdAt (memStore32 (memStore32 m2.mem (F + 12) (f 21)) (F + 8) (f 19)) (F + BitVec.ofNat 32 0x60)
        B L (rcAdv r a) :=
      hr2.keep (by rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, rcf_e]; exact ld3 _ (by decide) (by decide))
        (by rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, rcf_e]; exact ld3 _ (by decide) (by decide))
    have e4' : memLoad32 (memStore32 (memStore32 m2.mem (F + 12) (f 21)) (F + 8) (f 19)) (F + 0xE4) =
        BitVec.ofNat 32 ol := (ld3 0xE4 (by decide) (by decide)).trans (by
          rw [show F + BitVec.ofNat 32 0xE4 = F + BitVec.ofNat 32 0xE0 + 4 from (add_ofNat_assoc F 0xE0 4).symm]
          exact e4)
    refine WP.lw trc_at_3e2 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE8) (by decide)) ?_; wn
    refine WP.lw trc_at_3e4 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE4) (by decide)) ?_; wn
    refine WP.aluImm trc_at_3e6 ?_; wn
    have hKB := hK2.kb.trans hKB3
    rcases par with _ | ⟨q, u⟩
    · have e8' : memLoad32 (memStore32 (memStore32 m2.mem (F + 12) (f 21)) (F + 8) (f 19)) (F + 0xE8) = 0 :=
        (ld3 0xE8 (by decide) (by decide)).trans (by
          rw [show F + BitVec.ofNat 32 0xE8 = F + BitVec.ofNat 32 0xE0 + 8 from (add_ofNat_assoc F 0xE0 8).symm]
          exact hpar)
      refine WP.branch trc_at_3e8 (fun _ => ?_) (fun hf => absurd hf (by
        trsimp; rw [hR.2.1, e8']; decide)); wn
      exact X.keyOid (c := false) (by rc_r hR) hI3 (by rc_k (hK.mono (by decide))) h8 hC hL3 hr3
        (by trsimp; exact e0') (by trsimp; rw [hR.2.1]; exact e4') hoo (by trsimp <;> rfl) (k.mono hKB)
    obtain ⟨p8, pC, p18, pq⟩ := hpar
    have e8' : memLoad32 (memStore32 (memStore32 m2.mem (F + 12) (f 21)) (F + 8) (f 19)) (F + 0xE8) =
        B + BitVec.ofNat 32 (q + u.header) :=
      (ld3 0xE8 (by decide) (by decide)).trans (by
        rw [show F + BitVec.ofNat 32 0xE8 = F + BitVec.ofNat 32 0xE0 + 8 from (add_ofNat_assoc F 0xE0 8).symm]
        exact p8)
    have eC' : memLoad32 (memStore32 (memStore32 m2.mem (F + 12) (f 21)) (F + 8) (f 19)) (F + 0xEC) =
        BitVec.ofNat 32 u.len :=
      (ld3 0xEC (by decide) (by decide)).trans (by
        rw [show F + BitVec.ofNat 32 0xEC = F + BitVec.ofNat 32 0xE0 + 0xC from (add_ofNat_assoc F 0xE0 0xC).symm]
        exact pC)
    have e18 : memStore32 (memStore32 m2.mem (F + 12) (f 21)) (F + 8) (f 19) (F + 0xF8) =
        BitVec.ofNat 8 u.tag :=
      (rcf_st32o _ F _ (c := 0xF8) (d := 8) (by decide) (by decide) (by decide)).trans
        ((rcf_st32o _ F _ (c := 0xF8) (d := 0xC) (by decide) (by decide) (by decide)).trans (by
          rw [show F + BitVec.ofNat 32 0xF8 = F + BitVec.ofNat 32 0xE0 + 0x18 from
            (add_ofNat_assoc F 0xE0 0x18).symm]
          exact p18))
    have htl : u.tag < 256 := rck_algTag hAlg hL.lt
    refine WP.branch trc_at_3e8 (fun ht => absurd ht (by
      trsimp; rw [hR.2.1, e8', rck_beqF (rck_pne hL (by omega))]; decide)) (fun _ => ?_); wn
    refine WP.lbu trc_at_3ea ?_; wn
    refine WP.aluImm trc_at_3ee ?_; wn
    by_cases htag : u.tag ≠ 6
    · have hc : rcCurveOk L (some (q, u)) = false := by
        show (u.tag == 6 && _) = false
        rw [beq_false_of_ne htag]
        rfl
      rw [hc] at k
      refine WP.branch trc_at_3f0 (fun _ => ?_) (fun hf => absurd hf (by
        trsimp; rw [hR.2.1, e18, show (6 : Word) = BitVec.ofNat 32 6 from rfl]
        simp only [branchTaken, bne_eq_false_iff_eq]
        intro e; apply htag; have := (rck_ze (by decide)).mp e
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl] at this)); wn
      exact X.keyOid (c := false) (by rc_r hR) hI3 (by rc_k (hK.mono (by decide))) h8 hC hL3 hr3
        (by trsimp; exact e0') (by trsimp; rw [hR.2.1]; exact e4') hoo (by trsimp <;> rfl) (k.mono hKB)
    replace htag : u.tag = 6 := Decidable.of_not_not htag
    have hc : rcCurveOk L (some (q, u)) = (rcView L (q + u.header, u.len) == oidSecp384r1) := by
      show (u.tag == 6 && _) = _
      rw [htag]
      rfl
    rw [hc] at k
    refine WP.branch trc_at_3f0 (fun ht => absurd ht (by
      trsimp; rw [hR.2.1, e18, htag]; decide)) (fun _ => ?_); wn
    refine WP.lw trc_at_3f4 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xEC) (by decide)) ?_; wn
    refine WP.aluImm trc_at_3f6 ?_; wn
    refine WP.lui trc_at_3f8 ?_; wn
    refine WP.aluImm trc_at_3fc ?_; wn
    refine WP.alu trc_at_400 ?_; wn
    refine X.callSlEq (off := 0x402) (pa := B + BitVec.ofNat 32 (q + u.header)) (pl := u.len) (qa := rcCurveKey)
      (ql := 5) trc_at_402 trc_at_406 (by decide) (by decide) (by rc_r hR) hI3
      (by trsimp; rw [hR.2.1]; exact e8') (by trsimp; rw [hR.2.1]; exact eC') (by trsimp <;> decide)
      (by trsimp) (by omega) (by decide) (rck_sepG hL (by omega)) (X.roG ⟨by decide, by decide⟩)
      (fun m4 hK4 hE4 hI4 hres => ?_)
    rw [hL3.view2 (by omega), (X.codeAt hI3).kp] at hres
    refine WP.alu trc_at_40a ?_; wn
    refine WP.aluImm trc_at_40c ?_; wn
    refine X.keyOid (by rc_r hR) hI4 (by rc_k (hK.mono (by decide)))
      ((X.keepLd hK4 (c := 8) (by decide)).trans h8) ((X.keepLd hK4 (c := 0xC) (by decide)).trans hC)
      (hL3.keep hK4) (X.eqRd hE4 hr3 (by decide))
      (by trsimp; exact e0') (by trsimp; rw [hR.2.1]; exact e4') hoo ?_ (k.mono (hKB.trans hK4.kb))
    trsimp; rw [hres]
    by_cases heq : rcView L (q + u.header, u.len) = oidSecp384r1
    · simp only [beq_iff_eq.mpr heq, heq, ↓reduceIte]; decide
    · simp only [beq_false_of_ne heq, heq, ↓reduceIte]; decide

/-- From 0x2E0: `p384_key` on the reader at `F + 0xD0`, up to the join at
0x308 with the key's address, or 0, in `a1`. -/
theorem RcCtx.keySeq (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f w : Fin 32 → Word}
    {Q : Post} {B : Word} {L : Bytes} {r : RcRd}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) (hK : RcK rcKL w f) (hL : RcL M G B L)
    (hr : RcRdAt M (F + BitVec.ofNat 32 0xD0) B L r)
    (k : RcKeyK M0 G F out fr fp fl g0 w Q M (rcKey L B r)) : WP trustedRootReadChainCode TRC Q M 0x2E0 f := by
  have hw := hL.hw
  have hr2 := hr.2.2
  refine WP.aluImm trc_at_2e0 ?_; wn
  refine WP.aluImm trc_at_2e2 ?_; wn
  refine X.callSeq (off := 0x2E4) (oc := 0xE0) (dc := 0xD0) trc_at_2e4 trc_at_2e8 (by decide) (by decide)
    (by rc_r hR) hI (by decide) (by decide) (by decide) (by trsimp; rw [hR.2.1]; rfl) (by trsimp; rw [hR.2.1]; rfl)
    hL hr (fun m2 hK2 _ hI2 hS => ?_)
  have hL2 := hL.keep hK2
  refine WP.lw trc_at_2ec (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xE0) (by decide)) ?_; wn
  rcases hE : derElement 0x30 (rcView L r) with e | t
  · simp only [rcElem, hE] at hS
    have hv : rcKey L B r = 0 := by rw [rcKey_eq, hE]
    rw [hv] at k
    refine WP.branch trc_at_2ee (fun _ => ?_) (fun hf => absurd hf (by
      trsimp; rw [hR.2.1, show F + 0xE0 = F + BitVec.ofNat 32 0xE0 from rfl, hS.1]; decide)); wn
    exact X.key306 (by rc_r hR) hI2 (by rc_k hK) (k.mono hK2.kb)
  simp only [rcElem, hE] at hS
  obtain ⟨e0, ⟨i8, iC, ib⟩, ⟨d8, dC, -⟩, hb⟩ := hS
  have e0' : memLoad32 m2.mem (F + 0xE0) = B + BitVec.ofNat 32 (r.1 + t.header) := e0
  refine WP.branch trc_at_2ee (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, e0', rck_beqF (rck_pne hL (by omega))]; decide)) (fun _ => ?_); wn
  refine WP.aluImm trc_at_2f0 ?_; wn
  refine WP.lw trc_at_2f2 (by
    trsimp; rw [hR.2.1]; simp only [ev_add, BitVec.add_assoc, BitVec.reduceAdd]; exact X.fal (c := 0xE4) (by decide)) ?_; wn
  refine WP.lw trc_at_2f4 (by
    trsimp; rw [hR.2.1]; simp only [ev_add, BitVec.add_assoc, BitVec.reduceAdd]; exact X.fal (c := 0xE8) (by decide)) ?_; wn
  refine WP.lw trc_at_2f6 (by
    trsimp; rw [hR.2.1]; simp only [ev_add, BitVec.add_assoc, BitVec.reduceAdd]; exact X.fal (c := 0xEC) (by decide)) ?_; wn
  refine WP.lw trc_at_2f8 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0xDC) (by decide)) ?_; wn
  refine WP.aluImm trc_at_2fa ?_; wn
  refine WP.sw trc_at_2fc (by
      trsimp; rw [hR.2.1]; simp only [ev_add, BitVec.add_assoc, BitVec.reduceAdd]; exact X.fal (c := 0x64) (by decide))
    (by trsimp; rw [hR.2.1]; simp only [ev_add, BitVec.add_assoc, BitVec.reduceAdd]; exact X.flo (c := 0x64) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_2fe (by
      trsimp; rw [hR.2.1]; simp only [ev_add, BitVec.add_assoc, BitVec.reduceAdd]; exact X.fal (c := 0x68) (by decide))
    (by
      trsimp; rw [hR.2.1]; simp only [ev_add, BitVec.add_assoc, BitVec.reduceAdd]
      exact X.flo (c := 0x68) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_300 (by
      trsimp; rw [hR.2.1]; simp only [ev_add, BitVec.add_assoc, BitVec.reduceAdd]; exact X.fal (c := 0x6C) (by decide))
    (by
      trsimp; rw [hR.2.1]; simp only [ev_add, BitVec.add_assoc, BitVec.reduceAdd]
      exact X.flo (c := 0x6C) (k := 4) (by decide)) ?_; wn
  refine WP.sw trc_at_302 (by trsimp; rw [hR.2.1]; exact X.fal (c := 0x60) (by decide))
    (by trsimp; rw [hR.2.1]; exact X.flo (c := 0x60) (k := 4) (by decide)) ?_; wn
  rw [hR.2.1]
  simp only [ev_add, BitVec.add_assoc, BitVec.reduceAdd]
  have hKS : RcKeep G m2.mem (memStore32 (memStore32 (memStore32 (memStore32 m2.mem (F + 100#32)
      (memLoad32 m2.mem (F + 228#32))) (F + 104#32) (memLoad32 m2.mem (F + 232#32))) (F + 108#32)
      (memLoad32 m2.mem (F + 236#32))) (F + 96) (memLoad32 m2.mem (F + 224))) :=
    (((X.stK (c := 0x64) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0x64 _)).trans
      (X.stK (c := 0x68) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0x68 _))).trans
      (X.stK (c := 0x6C) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0x6C _))).trans
      (X.stK (c := 0x60) (k := 4) ⟨by decide, by decide⟩ (X.sw32 _ 0x60 _))
  have hI4 : RcMemInv M0 G F fr fp fl g0 (memStore32 (memStore32 (memStore32 (memStore32 m2.mem (F + 100#32)
      (memLoad32 m2.mem (F + 228#32))) (F + 104#32) (memLoad32 m2.mem (F + 232#32))) (F + 108#32)
      (memLoad32 m2.mem (F + 236#32))) (F + 96) (memLoad32 m2.mem (F + 224))) :=
    X.stI (X.stI (X.stI (X.stI hI2 (c := 0x64) (k := 4) (by decide) (X.sw32 _ 0x64 _))
      (c := 0x68) (k := 4) (by decide) (X.sw32 _ 0x68 _)) (c := 0x6C) (k := 4) (by decide) (X.sw32 _ 0x6C _))
      (c := 0x60) (k := 4) (by decide) (X.sw32 _ 0x60 _)
  have hr4 : RcRdAt (memStore32 (memStore32 (memStore32 (memStore32 m2.mem (F + 100#32)
      (memLoad32 m2.mem (F + 228#32))) (F + 104#32) (memLoad32 m2.mem (F + 232#32))) (F + 108#32)
      (memLoad32 m2.mem (F + 236#32))) (F + 96) (memLoad32 m2.mem (F + 224))) (F + BitVec.ofNat 32 0x60)
      B L (rcIn r t) := by
    refine ⟨?_, ?_, ib⟩
    · rw [show F + BitVec.ofNat 32 0x60 + 8 = F + BitVec.ofNat 32 0x68 from add_ofNat_assoc F 0x60 8]
      refine (rcf_ld32o (B := F) (c := 0x68) (d := 0x60) (Or.inr (by decide)) (by decide) (by decide)).trans
        ((rcf_ld32o (B := F) (c := 0x68) (d := 0x6C) (Or.inl (by decide)) (by decide) (by decide)).trans
          ((memLoad32_store32_same _ _ _).trans ?_))
      rw [show F + 232#32 = F + BitVec.ofNat 32 0xE0 + 8 from (add_ofNat_assoc F 0xE0 8).symm]; exact i8
    · rw [show F + BitVec.ofNat 32 0x60 + 0xC = F + BitVec.ofNat 32 0x6C from add_ofNat_assoc F 0x60 0xC]
      refine (rcf_ld32o (B := F) (c := 0x6C) (d := 0x60) (Or.inr (by decide)) (by decide) (by decide)).trans
        ((memLoad32_store32_same _ _ _).trans ?_)
      rw [show F + 236#32 = F + BitVec.ofNat 32 0xE0 + 0xC from (add_ofNat_assoc F 0xE0 0xC).symm]; exact iC
  have dC' : memLoad32 m2.mem (F + 220) = BitVec.ofNat 32 (r.2 - (t.header + t.len)) :=
    (congrArg (memLoad32 m2.mem) (add_ofNat_assoc F 0xD0 0xC)).symm.trans dC
  rw [rcKey_eq, hE] at k; dsimp only at k
  by_cases hz : r.2 - (t.header + t.len) ≠ 0
  · rw [ite_eq_left hz] at k
    refine WP.branch trc_at_304 (fun ht => absurd ht (by
      trsimp; rw [dC', rck_beqF (rck_nz hz (by omega))]; decide)) (fun _ => ?_); wn
    exact X.key306 (by rc_r hR) hI4 (by rc_k hK) (k.mono (hK2.trans hKS).kb)
  rw [ite_eq_right hz] at k
  replace hz : r.2 - (t.header + t.len) = 0 := Decidable.of_not_not hz
  refine WP.branch trc_at_304 (fun _ => ?_) (fun hf => absurd hf (by
    trsimp; rw [dC', hz]; decide)); wn
  exact X.keyAlg (by rc_r hR) hI4 (by rc_k hK) ((hL.keep hK2).keep hKS) hr4 (k.mono (hK2.trans hKS).kb)

end

end C3.RV32
