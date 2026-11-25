import C3BootProofs.Proofs.AcceptExtractLib
import C3BootProofs.Proofs.AcceptExtractErr
import C3BootProofs.Proofs.TufMetaCalls

/-!
# Tools for the extract stage's head

The head, from 0xC12 to 0xD8C, writes only a few ranges of the frame and
the frames of its callees below `sp`. `AceHM` says what memory holds between
0xC54 and 0xD8C, and `AceHR` names the registers that the head keeps.
`ace_fail1A6A` and `ace_fail1A66` are its two ways into the exit at 0x7D6.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

/-- `x` lies outside the ranges the head writes from 0xC58 on: the callees'
frames below `sp`, and `sp + 0x30`, `sp + 0x350`, `sp + 0x1310`, and the
array at `sp + 0x1ED0`. -/
def AceL (B x : Word) : Prop :=
  (x.toNat < B.toNat + 0x38BC ∨ B.toNat + 0x3A50 ≤ x.toNat) ∧
  (x.toNat < B.toNat + 0x3A80 ∨ B.toNat + 0x3A84 ≤ x.toNat) ∧
  (x.toNat < B.toNat + 0x3DA0 ∨ B.toNat + 0x3DA8 ≤ x.toNat) ∧
  (x.toNat < B.toNat + 0x4D60 ∨ B.toNat + 0x4D7C ≤ x.toNat) ∧
  (x.toNat < B.toNat + 0x5920 ∨ B.toNat + 0x5A04 ≤ x.toNat)

/-- `x` lies outside every range the head writes: those of `AceL`, the
expiry at `sp + 0x20`, and the slice at `sp + 0x1FDC`. -/
def AceU (B x : Word) : Prop :=
  AceL B x ∧ (x.toNat < B.toNat + 0x3A70 ∨ B.toNat + 0x3A78 ≤ x.toNat) ∧
    (x.toNat < B.toNat + 0x5A2C ∨ B.toNat + 0x5A34 ≤ x.toNat)

theorem ace_sepX {B x : Word} (F : Fr B 0x5A70) {c n : Nat} (hc : c + n ≤ 0x5A70)
    (h : x.toNat < B.toNat + c ∨ B.toNat + c + n ≤ x.toNat) : Sep x 1 (B + BitVec.ofNat 32 c) n := by
  have hh := F.hi
  rcases h with h | h
  · exact sep_of_le (by rw [F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)
  · exact (sep_of_le (by rw [F.at c (by omega)]; omega) (by have := x.isLt; omega)).symm

theorem ace_ofSep {x a : Word} {n : Nat} (h : Sep x 1 a n) :
    x.toNat < a.toNat ∨ a.toNat + n ≤ x.toNat := by
  rcases Nat.lt_or_ge x.toNat a.toNat with h1 | h1
  · exact Or.inl h1
  · rcases Nat.lt_or_ge x.toNat (a.toNat + n) with h2 | h2
    · exfalso
      apply h 0 (by decide) (x.toNat - a.toNat) (by omega)
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have := x.isLt
      omega
    · exact Or.inr h2

/-- Outside the stack, the head writes nothing. -/
theorem ace_U_out {B x : Word} (h : x.toNat < B.toNat ∨ B.toNat + 0x5A70 ≤ x.toNat) : AceU B x := by
  rcases h with h | h
  · exact ⟨⟨.inl (by omega), .inl (by omega), .inl (by omega), .inl (by omega), .inl (by omega)⟩,
      .inl (by omega), .inl (by omega)⟩
  · exact ⟨⟨.inr (by omega), .inr (by omega), .inr (by omega), .inr (by omega), .inr (by omega)⟩,
      .inr (by omega), .inr (by omega)⟩

theorem ace_U_sep {B x : Word} (h : Sep x 1 B 0x5A70) : AceU B x :=
  ace_U_out (ace_ofSep h)

/-- The frame slots that later stages read, and the saved registers, are
outside what the head writes. -/
theorem ace_U_at {B x : Word} {k : Nat} (hx : x.toNat = B.toNat + 0x3A50 + k)
    (hk : (0x34 ≤ k ∧ k < 0x48) ∨ (0x108 ≤ k ∧ k < 0x244) ∨ (0x1FE4 ≤ k ∧ k < 0x2020)) : AceU B x := by
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨⟨.inr (by omega), .inr (by omega), .inl (by omega), .inl (by omega), .inl (by omega)⟩,
      .inr (by omega), .inl (by omega)⟩
  · exact ⟨⟨.inr (by omega), .inr (by omega), .inl (by omega), .inl (by omega), .inl (by omega)⟩,
      .inr (by omega), .inl (by omega)⟩
  · exact ⟨⟨.inr (by omega), .inr (by omega), .inr (by omega), .inr (by omega), .inr (by omega)⟩,
      .inr (by omega), .inr (by omega)⟩

/-- The expiry and the slice at `sp + 0x1FDC` are outside what the head
writes after 0xC54. -/
theorem ace_L_at {B x : Word} {k : Nat} (hx : x.toNat = B.toNat + 0x3A50 + k)
    (hk : (0x20 ≤ k ∧ k < 0x28) ∨ (0x1FDC ≤ k ∧ k < 0x1FE4)) : AceL B x := by
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨.inr (by omega), .inl (by omega), .inl (by omega), .inl (by omega), .inl (by omega)⟩
  · exact ⟨.inr (by omega), .inr (by omega), .inr (by omega), .inr (by omega), .inr (by omega)⟩

theorem ace_slotAdd {B : Word} (F : Fr B 0x5A70) {k j : Nat} (h : 0x3A50 + k + j ≤ 0x5A70) :
    (acSlot B k + BitVec.ofNat 32 j).toNat = B.toNat + 0x3A50 + k + j := by
  rw [ace_slot, F.at _ h]; omega

/-! ## The ranges the head writes -/

section
variable {B x : Word} (F : Fr B 0x5A70)
include F

theorem AceL.frame (h : AceL B x) {c n : Nat} (h1 : 0x38BC ≤ c) (h2 : c + n ≤ 0x3A50) :
    Sep x 1 (B + BitVec.ofNat 32 c) n := by
  refine ace_sepX F (by omega) ?_
  rcases h.1 with h | h
  · exact .inl (by omega)
  · exact .inr (by omega)

theorem AceL.s30 (h : AceL B x) {c n : Nat} (h1 : 0x3A80 ≤ c) (h2 : c + n ≤ 0x3A84) :
    Sep x 1 (B + BitVec.ofNat 32 c) n := by
  refine ace_sepX F (by omega) ?_
  rcases h.2.1 with h | h
  · exact .inl (by omega)
  · exact .inr (by omega)

theorem AceL.s350 (h : AceL B x) {c n : Nat} (h1 : 0x3DA0 ≤ c) (h2 : c + n ≤ 0x3DA8) :
    Sep x 1 (B + BitVec.ofNat 32 c) n := by
  refine ace_sepX F (by omega) ?_
  rcases h.2.2.1 with h | h
  · exact .inl (by omega)
  · exact .inr (by omega)

theorem AceL.s1310 (h : AceL B x) {c n : Nat} (h1 : 0x4D60 ≤ c) (h2 : c + n ≤ 0x4D7C) :
    Sep x 1 (B + BitVec.ofNat 32 c) n := by
  refine ace_sepX F (by omega) ?_
  rcases h.2.2.2.1 with h | h
  · exact .inl (by omega)
  · exact .inr (by omega)

theorem AceL.s1ED0 (h : AceL B x) {c n : Nat} (h1 : 0x5920 ≤ c) (h2 : c + n ≤ 0x5A04) :
    Sep x 1 (B + BitVec.ofNat 32 c) n := by
  refine ace_sepX F (by omega) ?_
  rcases h.2.2.2.2 with h | h
  · exact .inl (by omega)
  · exact .inr (by omega)

theorem AceU.s20 (h : AceU B x) {c n : Nat} (h1 : 0x3A70 ≤ c) (h2 : c + n ≤ 0x3A78) :
    Sep x 1 (B + BitVec.ofNat 32 c) n := by
  refine ace_sepX F (by omega) ?_
  rcases h.2.1 with h | h
  · exact .inl (by omega)
  · exact .inr (by omega)

theorem AceU.s1FDC (h : AceU B x) {c n : Nat} (h1 : 0x5A2C ≤ c) (h2 : c + n ≤ 0x5A34) :
    Sep x 1 (B + BitVec.ofNat 32 c) n := by
  refine ace_sepX F (by omega) ?_
  rcases h.2.2 with h | h
  · exact .inl (by omega)
  · exact .inr (by omega)

end

/-! ## Memory from 0xC58 to 0xD8C -/

/-- Memory between 0xC58 and 0xD8C: the machine at 0xC12 outside what the
head writes, the earlier expiry at `sp + 0x20`, and `keys`'s slice at
`sp + 0x1FDC`. -/
structure AceHM (X : AceCtx) (M : Word → BitVec 8) : Prop where
  mem : ∀ x, AceU X.B x → M x = X.K.mem x
  exp : aceU64 M (acSlot X.B 0x20) = min (aceU64 X.K.mem (acSlot X.B 0x20)) (aceU64 X.K.mem (acSlot X.B 0x28))
  fp : memLoad32 M (acSlot X.B 0x1FDC) = X.Bf + 0x6800
  fl : memLoad32 M (acSlot X.B 0x1FE0) = 0x5040

theorem ace_load_eq {M M' : Word → BitVec 8} {a : Word} (h : ∀ j, j < 4 → M' (a + BitVec.ofNat 32 j) = M (a + BitVec.ofNat 32 j)) :
    memLoad32 M' a = memLoad32 M a :=
  memLoad32_shift h

theorem AceHM.mono {X : AceCtx} {M M' : Word → BitVec 8} (h : AceHM X M) (F : Fr X.B 0x5A70)
    (hM : ∀ x, AceL X.B x → M' x = M x) : AceHM X M' := by
  have hL : ∀ k j, ((0x20 ≤ k ∧ k < 0x28) ∨ (0x1FDC ≤ k ∧ k < 0x1FE4)) → j < 4 → k + j < 0x28 ∨ 0x1FDC ≤ k →
      (0x20 ≤ k + j ∧ k + j < 0x28) ∨ (0x1FDC ≤ k + j ∧ k + j < 0x1FE4) →
      M' (acSlot X.B k + BitVec.ofNat 32 j) = M (acSlot X.B k + BitVec.ofNat 32 j) := fun k j _ hj _ hkj =>
    hM _ (ace_L_at (by rw [ace_slotAdd F (by omega)]; omega) hkj)
  refine ⟨fun x hx => (hM x hx.1).trans (h.mem x hx), ?_, ?_, ?_⟩
  · rw [← h.exp]
    unfold aceU64
    rw [ace_load_eq fun j hj => hL 0x20 j (.inl ⟨by decide, by decide⟩) hj (.inl (by omega)) (.inl ⟨by omega, by omega⟩)]
    rw [show acSlot X.B 0x20 + 4 = acSlot X.B 0x24 by unfold acSlot; rw [BitVec.add_assoc]; rfl]
    rw [ace_load_eq fun j hj => hL 0x24 j (.inl ⟨by decide, by decide⟩) hj (.inl (by omega)) (.inl ⟨by omega, by omega⟩)]
  · rw [← h.fp]
    exact ace_load_eq fun j hj => hL 0x1FDC j (.inr ⟨by decide, by decide⟩) hj (.inr (by decide))
      (.inr ⟨by omega, by omega⟩)
  · rw [← h.fl]
    exact ace_load_eq fun j hj => hL 0x1FE0 j (.inr ⟨by decide, by decide⟩) hj (.inr (by decide))
      (.inr ⟨by omega, by omega⟩)

/-! ## Registers -/

/-- The registers the head keeps from 0xC12: `sp`, `gp`, `tp`, `s3`, `s5`,
`s9`, and `s11`. -/
structure AceHR (X : AceCtx) (f : Fin 32 → Word) : Prop where
  rz : f 0 = 0
  rsp : f (2 : Fin 32) = X.B + 0x3A50
  rgp : f (3 : Fin 32) = X.g
  rtp : f (4 : Fin 32) = X.t
  r19 : f (19 : Fin 32) = acSlot X.B 0x890
  r21 : f (21 : Fin 32) = reg X.K 21
  r25 : f (25 : Fin 32) = reg X.K 25
  r27 : f (27 : Fin 32) = reg X.K 27

theorem AceHR.up {X : AceCtx} {f : Fin 32 → Word} (h : AceHR X f) {rd : Fin 32} {v : Word}
    (hr : rd.val ∉ [0, 2, 3, 4, 19, 21, 25, 27]) : AceHR X (upd f rd v) := by
  have k : ∀ q : Fin 32, q.val ∈ [0, 2, 3, 4, 19, 21, 25, 27] → upd f rd v q = f q := fun q hq => by
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp only [upd_app, h0, ↓reduceIte]; exact h.rz.symm
    · have : q ≠ rd := fun e => hr (e ▸ hq)
      simp only [upd_app, h0, this, ↓reduceIte]
  exact ⟨by simp only [upd_app, ↓reduceIte, Fin.val_zero], (k 2 (by decide)).trans h.rsp, (k 3 (by decide)).trans h.rgp,
    (k 4 (by decide)).trans h.rtp, (k 19 (by decide)).trans h.r19, (k 21 (by decide)).trans h.r21,
    (k 25 (by decide)).trans h.r25, (k 27 (by decide)).trans h.r27⟩

theorem AceHR.cl {X : AceCtx} {f : Fin 32 → Word} (h : AceHR X f) {m : Machine} {cl : List (Fin 32)}
    (hc : ∀ q : Fin 32, q.val ∈ [0, 2, 3, 4, 19, 21, 25, 27] → q ∉ cl) : AceHR X (clob f m cl) := by
  have k : ∀ q : Fin 32, q.val ∈ [0, 2, 3, 4, 19, 21, 25, 27] → clob f m cl q = f q := fun q hq => by
    simp only [clob_app, hc q hq, ↓reduceIte]
  exact ⟨(k 0 (by decide)).trans h.rz, (k 2 (by decide)).trans h.rsp, (k 3 (by decide)).trans h.rgp,
    (k 4 (by decide)).trans h.rtp, (k 19 (by decide)).trans h.r19, (k 21 (by decide)).trans h.r21,
    (k 25 (by decide)).trans h.r25, (k 27 (by decide)).trans h.r27⟩

/-- Rebuilds `AceHR` through a chain of `upd`s and `clob`s. -/
macro "hr" : tactic => `(tactic| first
  | assumption
  | (repeat (first | refine AceHR.up ?_ (by decide) | refine AceHR.cl ?_ (by decide))); assumption)

/-! ## What memory outside the head's writes gives -/

section
variable {X : AceCtx} {M : Word → BitVec 8} (O : X.Ok) (hm : ∀ x, AceU X.B x → M x = X.K.mem x)
include O hm

theorem ace_saves : ∀ k, k < 13 → memLoad32 M (X.B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = X.v k := by
  intro k hk
  rw [← O.inv.saves k hk]
  refine ace_load_eq fun j hj => hm _ (ace_U_at (k := 0x201C - 4 * k + j) ?_ (.inr (.inr ⟨by omega, by omega⟩)))
  have := O.lay.fr.hi
  rw [add_ofNat_assoc, O.lay.fr.at _ (by omega)]
  omega

theorem ace_out : ∀ x, Sep x 1 X.B 0x5A70 → Sep x 1 X.Bf acBufLen → M x = X.M0 x := fun x h1 h2 =>
  (hm x (ace_U_sep h1)).trans (O.inv.out x h1 h2)

theorem ace_inv {n : Machine} (hn : n.mem = M) (h2 : reg n (2 : Fin 32) = X.B + 0x3A50) (h3 : reg n (3 : Fin 32) = X.g)
    (h4 : reg n (4 : Fin 32) = X.t) : AcInv X.B X.Bf X.g X.t X.v X.M0 n :=
  ⟨h2, h3, h4, by rw [hn]; exact ace_saves O hm, by rw [hn]; exact ace_out O hm⟩

theorem ace_res : memLoad32 M (acSlot X.B 0x40) = X.r := by
  rw [← O.pre.res]
  exact ace_load_eq fun j hj => hm _ (ace_U_at (k := 0x40 + j) (by rw [ace_slotAdd O.lay.fr (by omega)]; omega)
    (.inl ⟨by omega, by omega⟩))

set_option maxRecDepth 100000 in
theorem ace_code : CodeIn M AC bootMainClosure0Code := fun i hi => by
  have hAC : 0x40000000 ≤ AC.toNat := by decide
  have hACl : AC.toNat + bootMainClosure0Code.length ≤ 2 ^ 32 := by decide
  have hi32 : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  have h : (AC + BitVec.ofNat 32 i).toNat = AC.toNat + i := by
    rw [BitVec.toNat_add, hi32]; omega
  have := O.lay.fr.hi
  rw [hm _ (ace_U_out (.inr (by rw [h]; omega)))]
  exact O.code i hi

theorem ace_env : AcExtractEnv M := O.env M (ace_out O hm)

theorem ace_doc : memBytes M X.D X.json.length = X.json := by
  refine (ace_memBytes_ext (M := X.K.mem) fun i hi => hm _ (ace_U_sep (ace_bufOut O.lay ?_ ?_))).trans O.pre.doc
  · have := O.pre.docLo; have := O.pre.docHi
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := O.lay.hi; omega
  · have := O.pre.docLo; have := O.pre.docHi
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := O.lay.hi; unfold acBufLen at *; omega

theorem ace_kept : ∀ x, AceKept X.B X.Bf x → M x = X.K.mem x := by
  intro x hx
  rcases hx with ⟨h1, -⟩ | ⟨k, hk, rfl⟩
  · exact hm x (ace_U_sep h1)
  · refine hm _ (ace_U_at (k := k) ?_ ?_)
    · have := O.lay.fr.hi
      rcases hk with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [O.lay.fr.at _ (by omega)] <;> omega
    · rcases hk with h | h
      · exact .inl h
      · exact .inr (.inl h)

end

/-! ## The exits -/

/-- At the head's exits: `AcInv`, and the exit at 0x7D6 or `P` at 0xD8C. -/
def aceHQ (X : AceCtx) (P : Machine → Prop) : Post := fun pc M f =>
  ∀ n : Machine, n.pc = pc → n.mem = M → (∀ q, reg n q = f q) →
    AcInv X.B X.Bf X.g X.t X.v X.M0 n ∧ (AcFail X.B X.r n ∨ (n.pc = AC + BitVec.ofNat 32 0xD8C ∧ P n))

theorem WP.here {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}
    (k : Q (base + BitVec.ofNat 32 off) M f) : WP code base Q M off f := fun _ _ m s =>
  ⟨m, .refl m, by rw [s.pc, s.mem, show reg m = f from funext s.regs]; exact k⟩

theorem ace_stage {X : AceCtx} (O : X.Ok) {P : Machine → Prop}
    (k : WP bootMainClosure0Code AC (aceHQ X P) X.K.mem 0xC12 (reg X.K)) : X.stage X.K 0xD8C P := by
  obtain ⟨m', c, q⟩ := k (by decide) O.code X.K O.st
  exact ⟨m', c, .inr (q m' rfl rfl fun _ => rfl)⟩

section
variable {X : AceCtx} {P : Machine → Prop} {M : Word → BitVec 8} {f : Fin 32 → Word}

set_option maxRecDepth 100000 in
theorem ace_zeAnd : ∀ b : BitVec 8, (b.zeroExtend 32 &&& (0xFF : Word)).toNat = b.toNat := by decide

/-- From 0x1A6A, with the code to log in `s0`, to the exit at 0x7D6. -/
theorem ace_f1A6A (O : X.Ok) (hm : ∀ x, AceU X.B x → M x = X.K.mem x) (R : AceHR X f)
    (he : (f 8 &&& 0xFF).toNat < 0x27) : WP bootMainClosure0Code AC (aceHQ X P) M 0x1A6A f := by
  refine WP.alu ac_at_1a6a ?_
  refine WP.jal ac_at_1a6c (by decide) ?_
  refine WP.here fun n hpc hn hr => ?_
  refine ⟨ace_inv O hm hn (by rw [hr]; rsimp; exact R.rsp) (by rw [hr]; rsimp; exact R.rgp)
    (by rw [hr]; rsimp; exact R.rtp), .inl (.inr (.inr (.inl ⟨by rw [hpc]; rfl, by rw [hn]; exact ace_res O hm, ?_⟩)))⟩
  rw [hr]; rsimp; rw [R.rz, ev_add, show (0 : Word) + f 8 = f 8 from BitVec.zero_add _]; exact he

/-- From 0x1A66, with the code to log at `sp + 0x354`, to the exit at 0x7D6. -/
theorem ace_f1A66 (O : X.Ok) (hm : ∀ x, AceU X.B x → M x = X.K.mem x) (R : AceHR X f)
    (he : (M (X.B + 0x3A50 + 0x354)).toNat < 0x27) : WP bootMainClosure0Code AC (aceHQ X P) M 0x1A66 f := by
  refine WP.lbu ac_at_1a66 ?_
  refine ace_f1A6A O hm (by hr) ?_
  rsimp; rw [R.rsp]
  rw [ace_zeAnd]; exact he

end

end C3.RV32.Ac
