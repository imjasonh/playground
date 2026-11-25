import C3BootProofs.Proofs.AcceptExtractHead
import C3BootProofs.Proofs.AcceptExtractSeq
import C3BootProofs.Proofs.TrustedRootLiftChain
import C3BootProofs.Proofs.AcceptExtractTsa

/-!
# Tools for the certificate-authority loop, and its tail

The loop at 0xD8C, before each certificate authority, takes the next item
of `certificateAuthorities`, reads its chain with `read_chain`, and keeps
its Fulcio key. When the items run out, the tail from 0xE2E zeroes the log
array at `sp + 0x350` and opens a cursor over `tlogs` at `sp + 0x1860`,
which `AceTlogStage` starts from at 0xEBA.

`AcaU` names what one pass of the loop leaves alone, and `AcaT` is memory
in a pass before the Fulcio array changes. `aceca_e2e` proves the tail.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

set_option maxRecDepth 100000

local notation "MCS" => (BitVec.ofNat 32 memcpyStubAddress : Word)

/-! ## The ranges a pass writes -/

/-- `x` lies outside the stack ranges that a pass of the loop or the tail
writes: the callees' frames from `sp - 0x740`, `sp + 0x2C`, the log array
at `sp + 0x350`, `field`'s result at `sp + 0x890`, the cursor and the
results at `sp + 0x1310`, and the cursor at `sp + 0x1860`. -/
def AcaW (B x : Word) : Prop :=
  (x.toNat < B.toNat + 0x3310 ∨ B.toNat + 0x3A50 ≤ x.toNat) ∧
  (x.toNat < B.toNat + 0x3A7C ∨ B.toNat + 0x3A80 ≤ x.toNat) ∧
  (x.toNat < B.toNat + 0x3DA0 ∨ B.toNat + 0x3FA0 ≤ x.toNat) ∧
  (x.toNat < B.toNat + 0x42E0 ∨ B.toNat + 0x42E8 ≤ x.toNat) ∧
  (x.toNat < B.toNat + 0x4D60 ∨ B.toNat + 0x4DB0 ≤ x.toNat) ∧
  (x.toNat < B.toNat + 0x52B0 ∨ B.toNat + 0x52BC ≤ x.toNat)

/-- `x` lies outside what the callees write: the ranges of `AcaW`, the
slice at `sp + 0x1FDC`, and `keys`'s free part from `fp`. -/
def AcaV (B Bf fp x : Word) : Prop :=
  AcaW B x ∧ (x.toNat < B.toNat + 0x5A2C ∨ B.toNat + 0x5A34 ≤ x.toNat) ∧
    (x.toNat < fp.toNat ∨ Bf.toNat + 0xB840 ≤ x.toNat)

/-- `x` lies outside everything a pass writes: the ranges of `AcaV`, and
the Fulcio array at `sp + 0x1ED0`. -/
def AcaU (B Bf fp x : Word) : Prop :=
  AcaV B Bf fp x ∧ (x.toNat < B.toNat + 0x5920 ∨ B.toNat + 0x5A20 ≤ x.toNat)

theorem AcaW.sep {B x : Word} (F : Fr B 0x5A70) (h : AcaW B x) {c n : Nat}
    (hr : (0x3310 ≤ c ∧ c + n ≤ 0x3A50) ∨ (0x3A7C ≤ c ∧ c + n ≤ 0x3A80) ∨ (0x3DA0 ≤ c ∧ c + n ≤ 0x3FA0) ∨
      (0x42E0 ≤ c ∧ c + n ≤ 0x42E8) ∨ (0x4D60 ≤ c ∧ c + n ≤ 0x4DB0) ∨ (0x52B0 ≤ c ∧ c + n ≤ 0x52BC)) :
    Sep x 1 (B + BitVec.ofNat 32 c) n := by
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := h
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ace_sepX F (by omega) ?_
    rcases w1 with w | w
    · exact .inl (by omega)
    · exact .inr (by omega)
  · refine ace_sepX F (by omega) ?_
    rcases w2 with w | w
    · exact .inl (by omega)
    · exact .inr (by omega)
  · refine ace_sepX F (by omega) ?_
    rcases w3 with w | w
    · exact .inl (by omega)
    · exact .inr (by omega)
  · refine ace_sepX F (by omega) ?_
    rcases w4 with w | w
    · exact .inl (by omega)
    · exact .inr (by omega)
  · refine ace_sepX F (by omega) ?_
    rcases w5 with w | w
    · exact .inl (by omega)
    · exact .inr (by omega)
  · refine ace_sepX F (by omega) ?_
    rcases w6 with w | w
    · exact .inl (by omega)
    · exact .inr (by omega)

/-- A byte of the stack is outside `Buffers`. -/
theorem aceca_stkBuf {B Bf x : Word} (lay : AceLayout B Bf) {k : Nat} (hx : x.toNat = B.toNat + k)
    (hk : k < 0x5A70) : x.toNat < Bf.toNat ∨ Bf.toNat + acBufLen ≤ x.toNat := by
  rcases Nat.lt_or_ge x.toNat Bf.toNat with h | h
  · exact .inl h
  · rcases Nat.lt_or_ge x.toNat (Bf.toNat + acBufLen) with h' | h'
    · exfalso
      rcases ace_ofSep (ace_bufOut lay h h') with e | e <;> omega
    · exact .inr h'

/-- The frame slots a pass reads back, and the saved registers, are outside
what the callees write. -/
theorem aceca_V_at {B Bf fp x : Word} (lay : AceLayout B Bf) (hfp : Bf.toNat ≤ fp.toNat) {k : Nat}
    (hx : x.toNat = B.toNat + k)
    (hk : (0x3A50 ≤ k ∧ k < 0x3A7C) ∨ (0x3A80 ≤ k ∧ k < 0x3DA0) ∨ (0x52BC ≤ k ∧ k < 0x5A2C) ∨
      (0x5A34 ≤ k ∧ k < 0x5A70)) :
    AcaV B Bf fp x := by
  have hk' : k < 0x5A70 := by rcases hk with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hb : x.toNat < fp.toNat ∨ Bf.toNat + 0xB840 ≤ x.toNat := by
    rcases aceca_stkBuf lay hx hk' with h | h
    · exact .inl (by omega)
    · exact .inr (by unfold acBufLen at h; omega)
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨⟨.inr (by omega), .inl (by omega), .inl (by omega), .inl (by omega), .inl (by omega),
      .inl (by omega)⟩, .inl (by omega), hb⟩
  · exact ⟨⟨.inr (by omega), .inr (by omega), .inl (by omega), .inl (by omega), .inl (by omega),
      .inl (by omega)⟩, .inl (by omega), hb⟩
  · exact ⟨⟨.inr (by omega), .inr (by omega), .inr (by omega), .inr (by omega), .inr (by omega),
      .inr (by omega)⟩, .inl (by omega), hb⟩
  · exact ⟨⟨.inr (by omega), .inr (by omega), .inr (by omega), .inr (by omega), .inr (by omega),
      .inr (by omega)⟩, .inr (by omega), hb⟩

theorem aceca_U_at {B Bf fp x : Word} (lay : AceLayout B Bf) (hfp : Bf.toNat ≤ fp.toNat) {k : Nat}
    (hx : x.toNat = B.toNat + k)
    (hk : (0x3A50 ≤ k ∧ k < 0x3A7C) ∨ (0x3A80 ≤ k ∧ k < 0x3DA0) ∨ (0x5A20 ≤ k ∧ k < 0x5A2C) ∨
      (0x5A34 ≤ k ∧ k < 0x5A70)) :
    AcaU B Bf fp x := by
  refine ⟨aceca_V_at lay hfp hx ?_, ?_⟩
  · rcases hk with h | h | ⟨h1, h2⟩ | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl ⟨by omega, h2⟩))
    · exact .inr (.inr (.inr h))
  · rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inr (by omega)
    · exact .inr (by omega)

/-- Outside the stack and `keys`'s free part, a pass writes nothing. -/
theorem aceca_U_out {B Bf fp x : Word} (h : x.toNat < B.toNat ∨ B.toNat + 0x5A70 ≤ x.toNat)
    (hb : x.toNat < fp.toNat ∨ Bf.toNat + 0xB840 ≤ x.toNat) : AcaU B Bf fp x := by
  rcases h with h | h
  · exact ⟨⟨⟨.inl (by omega), .inl (by omega), .inl (by omega), .inl (by omega), .inl (by omega),
      .inl (by omega)⟩, .inl (by omega), hb⟩, .inl (by omega)⟩
  · exact ⟨⟨⟨.inr (by omega), .inr (by omega), .inr (by omega), .inr (by omega), .inr (by omega),
      .inr (by omega)⟩, .inr (by omega), hb⟩, .inr (by omega)⟩

/-- Memory in a pass from `n0` at 0xD8C, before the Fulcio array changes:
`n0`'s outside what the callees write, and `keys`'s slice at
`sp + 0x1FDC`. -/
structure AcaT (X : AceCtx) (n0 : Machine) (fp : Word) (M : Word → BitVec 8) : Prop where
  mem : ∀ x, AcaV X.B X.Bf fp x → M x = n0.mem x
  fp : memLoad32 M (acSlot X.B 0x1FDC) = memLoad32 n0.mem (acSlot X.B 0x1FDC)
  fl : memLoad32 M (acSlot X.B 0x1FE0) = memLoad32 n0.mem (acSlot X.B 0x1FE0)

theorem AcaT.mono {X : AceCtx} {n0 : Machine} {fp : Word} {M M' : Word → BitVec 8} (h : AcaT X n0 fp M)
    (F : Fr X.B 0x5A70) (hM : ∀ x, AcaW X.B x → M' x = M x) : AcaT X n0 fp M' := by
  have hW : ∀ k j, 0x1FDC ≤ k → k + j < 0x1FE4 →
      M' (acSlot X.B k + BitVec.ofNat 32 j) = M (acSlot X.B k + BitVec.ofNat 32 j) := fun k j h1 h2 => by
    refine hM _ ?_
    have hx := ace_slotAdd F (k := k) (j := j) (by omega)
    exact ⟨.inr (by omega), .inr (by omega), .inr (by omega), .inr (by omega), .inr (by omega),
      .inr (by omega)⟩
  refine ⟨fun x hx => (hM x hx.1).trans (h.mem x hx), ?_, ?_⟩
  · rw [← h.fp]; exact ace_load_eq fun j hj => hW 0x1FDC j (by decide) (by omega)
  · rw [← h.fl]; exact ace_load_eq fun j hj => hW 0x1FE0 j (by decide) (by omega)

theorem aceca_bf {X : AceCtx} {n : Machine} {off : Nat} {fp : Word} (A : AceAt X n off fp) :
    X.Bf.toNat ≤ fp.toNat := by
  have := A.fr.lo; omega

/-! ## What memory outside a pass's writes gives -/

section
variable {X : AceCtx} {n0 : Machine} {off : Nat} {fp : Word} {M : Word → BitVec 8} (O : X.Ok)
  (A : AceAt X n0 off fp) (hm : ∀ x, AcaU X.B X.Bf fp x → M x = n0.mem x)
include O A hm

theorem aceca_saves : ∀ k, k < 13 → memLoad32 M (X.B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = X.v k := by
  intro k hk
  rw [← A.inv.saves k hk]
  refine ace_load_eq fun j hj => hm _ (aceca_U_at O.lay (aceca_bf A) (k := 0x5A6C - 4 * k + j) ?_
    (.inr (.inr (.inr ⟨by omega, by omega⟩))))
  have := O.lay.fr.hi
  rw [add_ofNat_assoc, O.lay.fr.at _ (by omega)]

omit O in
theorem aceca_out : ∀ x, Sep x 1 X.B 0x5A70 → Sep x 1 X.Bf acBufLen → M x = X.M0 x := fun x h1 h2 => by
  refine (hm x (aceca_U_out (ace_ofSep h1) ?_)).trans (A.inv.out x h1 h2)
  rcases ace_ofSep h2 with h | h
  · exact .inl (by have := aceca_bf A; omega)
  · exact .inr (by unfold acBufLen at h; omega)

theorem aceca_inv {n : Machine} (hn : n.mem = M) (h2 : reg n (2 : Fin 32) = X.B + 0x3A50)
    (h3 : reg n (3 : Fin 32) = X.g) (h4 : reg n (4 : Fin 32) = X.t) : AcInv X.B X.Bf X.g X.t X.v X.M0 n :=
  ⟨h2, h3, h4, by rw [hn]; exact aceca_saves O A hm, by rw [hn]; exact aceca_out A hm⟩

theorem aceca_kept : ∀ x, AceKept X.B X.Bf x → M x = X.K.mem x := by
  intro x hx
  refine (hm x ?_).trans (A.keep.mem x hx)
  have hbf := O.lay.hi
  unfold acBufLen at hbf
  have e68 : (X.Bf + 0x6800).toNat = X.Bf.toNat + 0x6800 := by
    rw [BitVec.toNat_add]
    have : (0x6800 : Word).toNat = 0x6800 := rfl
    omega
  have hlo := A.fr.lo
  rcases hx with ⟨h1, h2⟩ | ⟨k, hk, rfl⟩
  · have h2' := ace_ofSep h2
    rw [e68] at h2'
    refine aceca_U_out (ace_ofSep h1) ?_
    rcases h2' with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  · have hk' : k < 0x244 := by rcases hk with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
    refine aceca_U_at O.lay (aceca_bf A) (k := 0x3A50 + k) (O.lay.fr.at _ (by omega)) ?_
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inr (.inl ⟨by omega, by omega⟩)
    · exact .inr (.inl ⟨by omega, by omega⟩)

theorem aceca_res : memLoad32 M (acSlot X.B 0x40) = X.r := by
  rw [← O.pre.res]
  refine ace_load_eq fun j hj => ?_
  have e : acSlot X.B 0x40 + BitVec.ofNat 32 j = acSlot X.B (0x40 + j) := by
    rw [ace_slot, Nat.add_assoc]
  rw [e]
  exact aceca_kept O A hm _ (.inr ⟨0x40 + j, .inl ⟨by omega, by omega⟩, rfl⟩)

theorem aceca_code : CodeIn M AC bootMainClosure0Code := fun i hi => by
  have hAC : 0x40000000 ≤ AC.toNat := by decide
  have hACl : AC.toNat + bootMainClosure0Code.length ≤ 2 ^ 32 := by decide
  have hi32 : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  have h : (AC + BitVec.ofNat 32 i).toNat = AC.toNat + i := by
    rw [BitVec.toNat_add, hi32]; omega
  have := O.lay.hi
  unfold acBufLen at this
  rw [hm _ (aceca_U_out (.inr (by rw [h]; have := O.lay.fr.hi; omega)) (.inr (by rw [h]; omega)))]
  exact A.code i hi

theorem aceca_env : AcExtractEnv M := O.env M (aceca_out A hm)

theorem aceca_slotEq {k : Nat}
    (hk : (0x3A50 ≤ 0x3A50 + k ∧ 0x3A50 + k + 4 ≤ 0x3A7C) ∨ (0x3A80 ≤ 0x3A50 + k ∧ 0x3A50 + k + 4 ≤ 0x3DA0)) :
    memLoad32 M (acSlot X.B k) = memLoad32 n0.mem (acSlot X.B k) :=
  ace_load_eq fun j hj => hm _ (aceca_U_at O.lay (aceca_bf A) (k := 0x3A50 + k + j)
    (by rw [ace_slotAdd O.lay.fr (by omega)]; omega) (by
      rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact .inl ⟨by omega, by omega⟩
      · exact .inr (.inl ⟨by omega, by omega⟩)))

theorem aceca_exp {n : Machine} (hn : n.mem = M) : AceExpiry X.B X.K n := by
  unfold AceExpiry
  rw [hn, ← A.exp]
  unfold aceU64
  rw [show acSlot X.B 0x20 + 4 = acSlot X.B 0x24 by unfold acSlot; rw [BitVec.add_assoc]; rfl,
    aceca_slotEq O A hm (k := 0x20) (.inl ⟨by omega, by omega⟩),
    aceca_slotEq O A hm (k := 0x24) (.inl ⟨by omega, by omega⟩)]

theorem aceca_doc : memBytes M X.D X.json.length = X.json := by
  refine (ace_memBytes_ext (M := X.K.mem) fun i hi => ?_).trans O.pre.doc
  have hlo := O.pre.docLo; have hhi := O.pre.docHi; have hb := O.lay.hi; have hf := A.fr.lo
  unfold acBufLen at hb
  have hy : (X.D + BitVec.ofNat 32 i).toNat = X.D.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e68 : (X.Bf + 0x6800).toNat = X.Bf.toNat + 0x6800 := by
    rw [BitVec.toNat_add]
    have : (0x6800 : Word).toNat = 0x6800 := rfl
    omega
  have hs : Sep (X.D + BitVec.ofNat 32 i) 1 X.B 0x5A70 :=
    ace_bufOut O.lay (by omega) (by unfold acBufLen; omega)
  refine (hm _ (aceca_U_out (ace_ofSep hs) (.inl (by omega)))).trans (A.keep.mem _ (.inl ⟨hs, ?_⟩))
  exact sep_of_le (by rw [e68]; omega) (by rw [e68]; omega)

/-- A span of the document in memory. -/
theorem aceca_docBytes {p : Word} {n : Nat} (h1 : X.D.toNat ≤ p.toNat)
    (h2 : p.toNat + n ≤ X.D.toNat + X.json.length) :
    memBytes M p n = slice X.json (p.toNat - X.D.toNat) n := by
  have hhi := O.pre.docHi; have hb := O.lay.hi
  have e : p = X.D + BitVec.ofNat 32 (p.toNat - X.D.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := p.isLt; omega
  have h := tuf_memBytes_drop_take (M := M) (p := X.D) (n := X.json.length) (h := p.toNat - X.D.toNat) (l := n)
    (by omega)
  rw [aceca_doc O A hm, ← e] at h
  exact h.symm

end

section
variable {X : AceCtx} {n0 : Machine} {off : Nat} {fp : Word} {M : Word → BitVec 8} (O : X.Ok)
  (A : AceAt X n0 off fp) (hv : ∀ x, AcaV X.B X.Bf fp x → M x = n0.mem x)
include O A hv

/-- `keys`'s used part, below `fp`, is as at 0xD8C. -/
theorem aceca_buf : ∀ y, X.Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp.toNat → M y = n0.mem y := by
  intro y h1 h2
  have hhi := A.fr.hi
  have hs : Sep y 1 X.B 0x5A70 := ace_bufOut O.lay (by omega) (by unfold acBufLen; omega)
  exact hv y (aceca_U_out (ace_ofSep hs) (.inl h2)).1

/-- The Fulcio array is as at 0xD8C. -/
theorem aceca_arr : AceSame M (acSlot X.B 0x1ED0) n0.mem (acSlot X.B 0x1ED0) 0x100 := fun c hc =>
  hv _ (aceca_V_at O.lay (aceca_bf A) (k := 0x3A50 + 0x1ED0 + c)
    (by rw [ace_slotAdd O.lay.fr (k := 0x1ED0) (j := c) (by omega)]; omega)
    (.inr (.inr (.inl ⟨by omega, by omega⟩))))

end

/-- A span of `Buffers` is apart from the stack frame. -/
theorem aceca_bufSep {X : AceCtx} (O : X.Ok) {c k : Nat} (hc : c + k ≤ 0x5A70) {p : Word} {n : Nat}
    (h1 : X.Bf.toNat ≤ p.toNat) (h2 : p.toNat + n ≤ X.Bf.toNat + acBufLen) :
    Sep (X.B + BitVec.ofNat 32 c) k p n := by
  have hb := O.lay.hi
  have e : p = X.Bf + BitVec.ofNat 32 (p.toNat - X.Bf.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := p.isLt; omega
  rw [e]; exact (O.lay.sep.sub hc).subR (by omega)

theorem aceca_ldAt {M : Word → BitVec 8} {a b v : Word} (h : a = b) (hb : memLoad32 M b = v) :
    memLoad32 M a = v := h ▸ hb

theorem aceca_al {X : AceCtx} (O : X.Ok) {w : Word} (k : Nat) (hk : k % 4 = 0) (hk2 : 0x3A50 + k ≤ 0x5A70)
    (h : w = acSlot X.B k) : w.toNat % 4 = 0 := by
  rw [h]; exact ace_al4 O.lay.fr (by omega) hk2

/-! ## The exits -/

/-- At the loop's exits: `AcInv`, and the exit at 0x7D6, `P` at 0xEBA, or
`L` back at 0xD8C. -/
def acaQ (X : AceCtx) (P L : Machine → Prop) : Post := fun pc M f =>
  ∀ n : Machine, n.pc = pc → n.mem = M → (∀ q, reg n q = f q) →
    AcInv X.B X.Bf X.g X.t X.v X.M0 n ∧
      (AcFail X.B X.r n ∨ (n.pc = AC + BitVec.ofNat 32 0xEBA ∧ P n) ∨ (n.pc = AC + BitVec.ofNat 32 0xD8C ∧ L n))

/-- `AceCaStage`'s goal at 0xEBA. -/
def acaP (X : AceCtx) (jr : Json) (n : Machine) : Prop :=
  ∃ fp fs tlogs, AceAt X n 0xEBA fp ∧ AceTlogInv X n fp jr fs tlogs []

/-- Back at 0xD8C with the first of `rest` read. -/
def acaL (X : AceCtx) (jr : Json) (rest : List Json) (n : Machine) : Prop :=
  ∃ j rest' fp fs, rest = j :: rest' ∧ AceAt X n 0xD8C fp ∧ AceCaInv X n fp jr rest' fs

section
variable {X : AceCtx} {P L : Machine → Prop} {n0 : Machine} {off : Nat} {fp : Word} {M : Word → BitVec 8}
  {f : Fin 32 → Word}

/-- From 0x1A6A, with the code to log in `s0`, to the exit at 0x7D6. -/
theorem aceca_f1A6A (O : X.Ok) (A : AceAt X n0 off fp) (hm : ∀ x, AcaU X.B X.Bf fp x → M x = n0.mem x)
    (R : AceHR X f) (he : (f 8 &&& 0xFF).toNat < 0x27) :
    WP bootMainClosure0Code AC (acaQ X P L) M 0x1A6A f := by
  refine WP.alu ac_at_1a6a ?_
  refine WP.jal ac_at_1a6c (by decide) ?_
  refine WP.here fun n hpc hn hr => ?_
  refine ⟨aceca_inv O A hm hn (by rw [hr]; rsimp; exact R.rsp) (by rw [hr]; rsimp; exact R.rgp)
    (by rw [hr]; rsimp; exact R.rtp),
    .inl (.inr (.inr (.inl ⟨by rw [hpc]; rfl, by rw [hn]; exact aceca_res O A hm, ?_⟩)))⟩
  rw [hr]; rsimp; rw [R.rz, ev_add, show (0 : Word) + f 8 = f 8 from BitVec.zero_add _]; exact he

end

/-! ## The tail, from 0xE2E to 0xEBA -/

/-- The copy of the cursor that `elements` left at `F + a` to `F + d`:
seven bytes by `memcpy`, then a word and a byte, with `P` naming the bytes
that the copy and the stores between them leave alone. -/
theorem aceca_ccopy {M2 M3 M5 : Word → BitVec 8} {F q : Word} {d a l k : Nat} {P : Word → Prop}
    (hd : d + 12 ≤ 0x1000)
    (hP : ∀ c, 5 ≤ c → c < 12 → P (F + BitVec.ofNat 32 (d + c)))
    (t4 : memLoad32 M2 (F + BitVec.ofNat 32 (a + 4)) = BitVec.ofNat 32 l)
    (t8 : memLoad32 M2 (F + BitVec.ofNat 32 (a + 8)) = BitVec.ofNat 32 k)
    (hO3 : ∀ x, P x → M3 x = copyBytes M2 (F + BitVec.ofNat 32 (d + 5)) (F + BitVec.ofNat 32 (a + 5)) 7 x)
    (hM5 : memStore8 (memStore32 M3 (F + BitVec.ofNat 32 d) q) (F + BitVec.ofNat 32 (d + 4))
      (M2 (F + BitVec.ofNat 32 (a + 4))) = M5) :
    PmCc M5 (F + BitVec.ofNat 32 d) q l k ∧
      ∀ x, Sep x 1 (F + BitVec.ofNat 32 d) 12 → P x → M5 x = M2 x := by
  have oC : Out M2 (copyBytes M2 (F + BitVec.ofNat 32 (d + 5)) (F + BitVec.ofNat 32 (a + 5)) 7)
      (F + BitVec.ofNat 32 (d + 5)) 7 := fun x hx => copyBytes_sep hx.symm (Nat.le_refl _)
  have hcp : ∀ c, 5 ≤ c → c < 12 → M5 (F + BitVec.ofNat 32 (d + c)) = M2 (F + BitVec.ofNat 32 (a + c)) := by
    intro c hc1 hc2
    rw [← hM5, memStore8_ne ?_]
    · rw [out_store32 _ _ _ _ ?_, hO3 _ (hP c hc1 hc2)]
      · have := copyBytes_at (M := M2) (dst := F + BitVec.ofNat 32 (d + 5)) (src := F + BitVec.ofNat 32 (a + 5))
          (N := 7) (i := c - 5) (by omega) (by decide)
        rw [add_ofNat_assoc, add_ofNat_assoc, show d + 5 + (c - 5) = d + c by omega,
          show a + 5 + (c - 5) = a + c by omega] at this
        exact this
      · exact sep_offsets F (c := d + c) (n := 1) (d := d) (k := 4) (Or.inr (by omega)) (by omega) (by omega)
    · exact sep_byte0 (sep_offsets F (c := d + c) (n := 1) (d := d + 4) (k := 1) (Or.inr (by omega)) (by omega)
        (by omega)) (by decide)
  refine ⟨⟨?_, ?_, ?_⟩, fun x hx hS => ?_⟩
  · rw [← hM5, (out_store8 _ _ _).load32 (sep_offsets F (c := d + 4) (n := 1) (d := d) (k := 4)
      (Or.inr (by omega)) (by omega) (by omega)), memLoad32_store32_same]
  · rw [← t4]
    refine memLoad32_shift fun j hj => ?_
    show M5 (F + BitVec.ofNat 32 d + BitVec.ofNat 32 4 + BitVec.ofNat 32 j) =
      M2 (F + BitVec.ofNat 32 (a + 4) + BitVec.ofNat 32 j)
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [add_ofNat_assoc, Nat.add_zero]
      rw [← hM5, memStore8_same]
    · simp only [add_ofNat_assoc, Nat.add_assoc]
      rw [hcp (4 + j) (by omega) (by omega)]
  · rw [← t8]
    refine memLoad32_shift fun j hj => ?_
    show M5 (F + BitVec.ofNat 32 d + BitVec.ofNat 32 8 + BitVec.ofNat 32 j) =
      M2 (F + BitVec.ofNat 32 (a + 8) + BitVec.ofNat 32 j)
    simp only [add_ofNat_assoc, Nat.add_assoc]
    rw [hcp (8 + j) (by omega) (by omega)]
  · have h4 : Sep x 1 (F + BitVec.ofNat 32 (d + 4)) 1 := by
      have := sep_in hx (d := 4) (l := 1) (by decide); rwa [add_ofNat_assoc] at this
    have h0 : Sep x 1 (F + BitVec.ofNat 32 d) 4 := by
      have := sep_in hx (d := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    have h5 : Sep x 1 (F + BitVec.ofNat 32 (d + 5)) 7 := by
      have := sep_in hx (d := 5) (l := 7) (by decide); rwa [add_ofNat_assoc] at this
    rw [← hM5, memStore8_ne (sep_byte0 h4 (by decide)), out_store32 _ _ _ _ h0, hO3 _ hS, oC _ h5]

/-- A word of the frame through a change that leaves three ranges alone. -/
theorem aceca_ld3 {B : Word} (F : Fr B 0x5A70) {M M' : Word → BitVec 8} {c1 n1 c2 n2 c3 n3 k : Nat}
    (h : ∀ x, Sep x 1 (B + BitVec.ofNat 32 c1) n1 → Sep x 1 (B + BitVec.ofNat 32 c2) n2 →
      Sep x 1 (B + BitVec.ofNat 32 c3) n3 → M' x = M x)
    (h1 : 0x3A50 + k + 4 ≤ c1 ∨ c1 + n1 ≤ 0x3A50 + k) (h2 : 0x3A50 + k + 4 ≤ c2 ∨ c2 + n2 ≤ 0x3A50 + k)
    (h3 : 0x3A50 + k + 4 ≤ c3 ∨ c3 + n3 ≤ 0x3A50 + k)
    (hk : 0x3A50 + k + 4 ≤ 0x5A70) (hc1 : c1 + n1 ≤ 0x5A70) (hc2 : c2 + n2 ≤ 0x5A70) (hc3 : c3 + n3 ≤ 0x5A70) :
    memLoad32 M' (acSlot B k) = memLoad32 M (acSlot B k) :=
  ace_load_eq fun j hj => by
    rw [ace_slot]
    refine h _ (ace_sepB' F ?_ (by omega) hc1) (ace_sepB' F ?_ (by omega) hc2) (ace_sepB' F ?_ (by omega) hc3)
    · rcases h1 with h1 | h1
      · exact .inl (by omega)
      · exact .inr (by omega)
    · rcases h2 with h2 | h2
      · exact .inl (by omega)
      · exact .inr (by omega)
    · rcases h3 with h3 | h3
      · exact .inl (by omega)
      · exact .inr (by omega)

set_option maxHeartbeats 4000000 in
/-- From 0xE7A, after `elements` on `tlogs`: the cursor's copy at
`sp + 0x1860`, the log count, and `AceTlogInv`, or the exit with
`elements`' error. -/
theorem aceca_e7a {X : AceCtx} (O : X.Ok) {n0 : Machine} {fp : Word} {jr : Json} {fs : List FulcioKey}
    (A : AceAt X n0 0xD8C fp) (I : AceCaInv X n0 fp jr [] fs) {L : Machine → Prop}
    {M Mx : Word → BitVec 8} {f : Fin 32 → Word} (T : AcaT X n0 fp M) (R : AceHR X f)
    (h26 : f 26 = reg n0 26) {jc : Json} {vq : Word} {vl : Nat}
    (hf : jr.field (ascii!"tlogs") = some jc) (hv : AceVal X.D X.json vq vl jc)
    (hz : ∀ i, i < 16 → memLoad32 M (acSlot X.B (0x350 + 0x20 * i)) = 0)
    (hc : CurRes Mx M (acSlot X.B 0x1320) 0x21 (curOpen 91 vq (slice X.json (vq.toNat - X.D.toNat) vl))) :
    WP bootMainClosure0Code AC (acaQ X (acaP X jr) L) M 0xE7A f := by
  have F := O.lay.fr
  have hh := F.hi
  have hm : ∀ x, AcaU X.B X.Bf fp x → M x = n0.mem x := fun x hx => T.mem x hx.1
  have e1 : X.B + 0x3A50 + 4880 + 16 = acSlot X.B 0x1320 := by simp only [acSlot]; bv_omega
  have e2 : X.B + 0x3A50 + 4880 + 20 = acSlot X.B 0x1320 + 4 := by simp only [acSlot]; bv_omega
  refine WP.lui ac_at_e7a ?_; wn
  refine WP.aluImm ac_at_e7c ?_; wn
  refine WP.alu ac_at_e80 ?_; wn
  simp only [ev_add, show (4096 : Word) + 784 = 0x1310 by rfl, BitVec.add_comm (0x1310 : Word), R.rsp]
  refine WP.lw ac_at_e82 (by rsimp; rw [e1]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.lbu ac_at_e84 ?_; wn
  rw [e1, e2]
  rcases hco : curOpen 91 vq (slice X.json (vq.toNat - X.D.toNat) vl) with _ | ⟨q, l, k⟩ <;> rw [hco] at hc
  · obtain ⟨-, t0, t4⟩ := hc
    refine WP.branch ac_at_e88 (fun _ => ?_) (fun eb => ?_) <;> wn
    · refine aceca_f1A6A O A hm (by hr) ?_
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
  refine WP.branch ac_at_e88 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; (try rw [t0] at eb)
    have e0 : vq = 0 := by simpa [branchTaken] using eb
    rw [e0] at hD; simp at hD; omega
  refine WP.lui ac_at_e8c ?_; wn
  refine WP.aluImm ac_at_e8e ?_; wn
  refine WP.alu ac_at_e92 ?_; wn
  refine WP.lui ac_at_e96 ?_; wn
  refine WP.aluImm ac_at_e98 ?_; wn
  refine WP.alu ac_at_e9c ?_; wn
  refine WP.aluImm ac_at_e9e ?_; wn
  have E := aceca_env O A hm
  have EM : McEnv M (MCS + 8) (acSlot X.B 0x1310 + BitVec.ofNat 32 (0x550 + 5))
      (acSlot X.B 0x1310 + BitVec.ofNat 32 (0x10 + 5)) (X.B + BitVec.ofNat 32 0x3A40) 7 := by
    refine ⟨by rw [show MCS + 8 = BitVec.ofNat 32 memcpyBodyAddress by decide]; exact E.body, ?_, ?_, ?_, ?_, ?_,
      ace_al4 F (by decide) (by decide), by rw [F.at _ (by decide)]; omega, ?_, ?_⟩
    · rw [ace_slot]; exact ace_hs F (by decide) (by decide) (by decide)
    · exact ace_hs F (by decide) (by decide) (by decide)
    · rw [ace_slot]; exact ace_sepB' F (.inr (by decide)) (by decide) (by decide)
    · rw [ace_slot]; exact ace_sepB' F (.inr (by decide)) (by decide) (by decide)
    · rw [ace_slot, ace_slot]; exact ace_sepB' F (.inr (by decide)) (by decide) (by decide)
    · rw [ace_slot, F.at _ (by decide)]; omega
    · rw [ace_slot, F.at _ (by decide)]; omega
  refine WP.callMemcpy (tb := MCS) (N := 7) ac_at_ea0 ac_at_ea4 (by decide) (by decide) (by decide) E.stub EM
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp <;> rfl)
    (by rsimp; rw [R.rsp]; bv_omega)
    (ace_cs F (by decide)) (by rw [ace_slot]; exact ace_cs F (by decide)) fun m3 hO3 => ?_
  generalize m3.mem = M3 at hO3
  have e2C : X.B + 0x3A50 + 0x2C = acSlot X.B 0x2C := by simp only [acSlot]; bv_omega
  refine WP.sw ac_at_ea8 (by rsimp; rw [R.rsp, e2C]; exact ace_al4 F (by decide) (by decide))
    (by rsimp; rw [R.rsp, e2C]; exact ace_cs F (by decide)) ?_; wn
  refine WP.lui ac_at_eaa ?_; wn
  refine WP.aluImm ac_at_eac ?_; wn
  refine WP.alu ac_at_eb0 ?_; wn
  simp only [ev_add, R.rsp]
  rw [e2C]
  have e3 : (4096 : Word) + 784 + (X.B + 0x3A50) + 0x550 = acSlot X.B 0x1310 + BitVec.ofNat 32 0x550 := by
    simp only [acSlot]; bv_omega
  refine WP.sw ac_at_eb2 (by rsimp; rw [e3, ace_slot]; exact ace_al4 F (by decide) (by decide))
    (by rsimp; rw [e3, ace_slot]; exact ace_cs F (by decide)) ?_; wn
  have e4 : (4096 : Word) + 784 + (X.B + 0x3A50) + 0x554 = acSlot X.B 0x1310 + BitVec.ofNat 32 (0x550 + 4) := by
    simp only [acSlot]; bv_omega
  refine WP.sb ac_at_eb6 (by rsimp; rw [e4, ace_slot]; exact ace_cs F (by decide)) ?_; wn
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
  obtain ⟨⟨c0, c4, c8⟩, hfa⟩ := aceca_ccopy (F := acSlot X.B 0x1310) (d := 0x550) (a := 0x10)
    (P := fun x => Sep x 1 (X.B + BitVec.ofNat 32 0x3A40) 16 ∧ Sep x 1 (acSlot X.B 0x2C) 4) (by decide)
    (fun c h1 h2 => by
      rw [ace_slot]
      exact ⟨ace_sepB' F (.inr (by omega)) (by omega) (by decide),
        ace_sepB' F (.inr (by omega)) (by omega) (by decide)⟩)
    t4' t8' (fun x hx => (memStore32_get_sep hx.2.symm).trans (hO3 x hx.1)) hn.symm
  rw [ace_slot] at hfa
  have hfa' : ∀ x, Sep x 1 (X.B + BitVec.ofNat 32 (0x3A50 + 0x1310 + 0x550)) 12 →
      Sep x 1 (X.B + BitVec.ofNat 32 0x3A40) 16 → Sep x 1 (X.B + BitVec.ofNat 32 (0x3A50 + 0x2C)) 4 →
      n.mem x = M x := fun x h1 h2 h3 => hfa x h1 ⟨h2, h3⟩
  have hM5 : ∀ x, AcaW X.B x → n.mem x = M x := fun x hx =>
    hfa' x (hx.sep F (.inr (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩))))))
      (hx.sep F (.inl ⟨by decide, by decide⟩)) (hx.sep F (.inr (.inl ⟨by decide, by decide⟩)))
  have T5 := T.mono F hM5
  have hm5 : ∀ x, AcaU X.B X.Bf fp x → n.mem x = n0.mem x := fun x hx => T5.mem x hx.1
  have rg : ∀ q : Fin 32, reg n q = _ := hrg
  have hsk := skipWs_le (slice X.json (vq.toNat - X.D.toNat) vl) 1
  have hjl := O.pre.docHi
  rw [hlen] at hsk
  have hst : St n.mem AC n 0xEBA (reg n) := ⟨hpc, rfl, fun _ => rfl⟩
  refine ⟨aceca_inv O A hm5 rfl (by rw [hrg]; rsimp; exact R.rsp) (by rw [hrg]; rsimp; exact R.rgp)
    (by rw [hrg]; rsimp; exact R.rtp), .inr (.inl ⟨hpc, fp, fs, js,
      ⟨aceca_code O A hm5, hst,
        aceca_inv O A hm5 rfl (by rw [hrg]; rsimp; exact R.rsp) (by rw [hrg]; rsimp; exact R.rgp)
          (by rw [hrg]; rsimp; exact R.rtp),
        ⟨by rw [T5.fp]; exact A.fr.ptr, by rw [T5.fl]; exact A.fr.len, A.fr.lo, A.fr.hi⟩,
        ⟨aceca_kept O A hm5, ?_⟩, aceca_exp O A hm5 rfl⟩,
      ⟨I.root, ?_, I.cas, ⟨[], by rw [hf]; rfl, rfl⟩, ?_, ?_, ?_, ?_, by rw [hrg]; rsimp; exact R.r19⟩⟩)⟩
  · intro q hq
    have : q = 21 ∨ q = 25 ∨ q = 27 := by revert hq; revert q; decide
    rcases this with rfl | rfl | rfl <;> rw [hrg] <;> rsimp
    · exact R.r21
    · exact R.r25
    · exact R.r27
  · have ho := I.obj
    unfold AceObj at ho ⊢
    rw [hrg]; rsimp
    rw [h26, aceca_slotEq O A hm5 (k := 0x30) (.inr ⟨by omega, by omega⟩)]
    exact ho
  · have k0 : acSlot X.B 0x1860 = acSlot X.B 0x1310 + BitVec.ofNat 32 0x550 := by
      simp only [acSlot]; bv_omega
    refine ⟨vq, vl, _, ?_, ?_, ?_, by omega, hD, hvl, hE⟩
    · rw [k0]; exact c0
    · rw [k0]; exact c4
    · rw [k0]; exact c8
  · exact ace_array_move I.fulcio (aceca_arr O A T5.mem) (aceca_buf O A T5.mem)
  · refine ⟨Nat.zero_le _, fun i h => absurd h (Nat.not_lt_zero _), fun i _ hi => ?_⟩
    rw [add_ofNat_assoc, show 0x3A50 + 0x350 + 0x20 * i = 0x3A50 + (0x350 + 0x20 * i) by omega]
    show memLoad32 n.mem (acSlot X.B (0x350 + 0x20 * i)) = 0
    rw [aceca_ld3 F hfa' (k := 0x350 + 0x20 * i) (.inl (by omega)) (.inr (by omega)) (.inr (by omega)) (by omega) (by decide) (by decide)
      (by decide)]
    exact hz i hi
  · rw [hn, memLoad32_store8_sep ?_, memLoad32_store32_sep ?_, memLoad32_store32_same]
    · rfl
    · rw [ace_slot]
      exact ace_sepB' F (k := 0x3A50 + 0x2C) (.inr (by decide)) (by decide) (by decide)
    · rw [ace_slot]
      exact ace_sepB' F (k := 0x3A50 + 0x2C) (.inr (by decide)) (by decide) (by decide)

set_option maxHeartbeats 4000000 in
/-- From 0xE40, with the log array zeroed: `field` for `tlogs`, then
`elements` on it. -/
theorem aceca_e40 {X : AceCtx} (O : X.Ok) {n0 : Machine} {fp : Word} {jr : Json} {fs : List FulcioKey}
    (A : AceAt X n0 0xD8C fp) (I : AceCaInv X n0 fp jr [] fs) {L : Machine → Prop}
    {M : Word → BitVec 8} {f : Fin 32 → Word} (T : AcaT X n0 fp M) (R : AceHR X f)
    (h26 : f 26 = reg n0 26)
    (hz : ∀ i, i < 16 → memLoad32 M (acSlot X.B (0x350 + 0x20 * i)) = 0) :
    WP bootMainClosure0Code AC (acaQ X (acaP X jr) L) M 0xE40 f := by
  have F := O.lay.fr
  have hh := F.hi
  have hm : ∀ x, AcaU X.B X.Bf fp x → M x = n0.mem x := fun x hx => T.mem x hx.1
  have E := aceca_env O A hm
  have hobj := I.obj
  unfold AceObj at hobj
  rw [← aceca_slotEq O A hm (k := 0x30) (.inr ⟨by omega, by omega⟩)] at hobj
  have hobj' := hobj
  obtain ⟨hD, hn, hJV⟩ := hobj'
  have hjl := O.pre.docHi
  have hD0 := O.pre.docLo
  have hbh := O.lay.hi
  unfold acBufLen at hbh
  have e30 : X.B + 0x3A50 + 0x30 = acSlot X.B 0x30 := by simp only [acSlot]; bv_omega
  refine WP.lui ac_at_e40 ?_; wn
  refine WP.aluImm ac_at_e44 ?_; wn
  refine WP.aluImm ac_at_e48 ?_; wn
  refine WP.aluImm ac_at_e4c ?_; wn
  refine WP.aluImm ac_at_e50 ?_; wn
  refine WP.alu ac_at_e52 ?_; wn
  refine WP.lw ac_at_e54 (by rsimp; rw [R.rsp, e30]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.callField (tb := BitVec.ofNat 32 jsonFieldAddress) (out := acSlot X.B 0x890)
    (s := X.B + BitVec.ofNat 32 0x394C) (p := reg n0 26) (kq := (img% roWindowAddress + 0x7F2))
    (n := (memLoad32 M (acSlot X.B 0x30)).toNat) (kl := 5)
    ac_at_e56 ac_at_e5a (by decide) (by decide) (by decide) E.field
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; simp only [ev_add]; exact (BitVec.zero_add _).trans h26)
    (by rsimp; rw [R.rsp, e30]; simp)
    (by rsimp <;> rfl)
    (by rsimp <;> rfl)
    (by rsimp; rw [R.rsp]; bv_omega)
    (ace_al4 F (by decide) (by decide)) (ace_al4 (c := 0x3A50 + 0x890) F (by decide) (by decide))
    (by rw [F.at _ (by decide)]; omega) (by decide) (by omega) (by omega)
    (tuf_fieldSep (by rw [F.at _ (by decide)]; omega) (O.lay.ro.sub (by decide)))
    (ace_bufSep O (by decide) hD (by omega))
    (tuf_sep_ro (O.lay.ro.sub (by decide)) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x890)) 8 _ _ from
      ace_sepB' F (.inr (by decide)) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x890)) 8 _ _ from ace_hs F (by decide) (by decide) (by decide))
    (ace_cs F (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x890)) 8 _ _ from ace_cs F (by decide)) fun m2 hR => ?_
  rw [aceca_docBytes O A hm hD (by omega), E.kTlogs] at hR
  generalize m2.mem = M2 at hR
  have hOF := ObjField false _ jr (ascii!"tlogs") hJV
  obtain ⟨M1, hO1, hF⟩ := hR
  have hf2 : ∀ x, Sep x 1 (X.B + BitVec.ofNat 32 (0x3A50 + 0x890)) 8 → Sep x 1 (X.B + BitVec.ofNat 32 0x394C) 260 →
      M2 x = M x := fun x h1 h2 => (hF.out x h1).trans (hO1 x h2)
  have hM2 : ∀ x, AcaW X.B x → M2 x = M x := fun x hx =>
    hf2 x (hx.sep F (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))) (hx.sep F (.inl ⟨by decide, by decide⟩))
  have T2 := T.mono F hM2
  have hm2 : ∀ x, AcaU X.B X.Bf fp x → M2 x = n0.mem x := fun x hx => T2.mem x hx.1
  have e890 : acSlot X.B 0x890 = X.B + BitVec.ofNat 32 (0x3A50 + 0x890) := rfl
  have e894 : acSlot X.B 0x890 + 4 = X.B + BitVec.ofNat 32 (0x3A50 + 0x894) := by
    simp only [acSlot]; bv_omega
  have e0 : acSlot X.B 0x890 + 0 = acSlot X.B 0x890 := by bv_omega
  rcases hf : jr.field (ascii!"tlogs") with _ | jc <;> rw [hf] at hOF
  · rw [hOF] at hF
    obtain ⟨-, t0, t4⟩ := hF
    refine WP.lw ac_at_e5e (aceca_al O 0x890 (by decide) (by decide) (by rsimp; rw [R.r19]; bv_omega)) ?_; wn
    refine WP.branch ac_at_e62 (fun _ => ?_) (fun eb => ?_) <;> wn
    · refine WP.lbu ac_at_1410 ?_; wn
      refine WP.jal ac_at_1414 (by decide) ?_; wn
      refine aceca_f1A6A O A hm2 (by hr) ?_
      rsimp; rw [R.r19, t4, ace_zeAnd]; decide
    · rsimp at eb; rw [R.r19] at eb; (try rw [e0] at eb); rw [t0] at eb
      exact absurd eb (by decide)
  obtain ⟨vp, vl, hok, hden⟩ := hOF
  rw [hok] at hF
  have hden' := ace_den hn hden
  have hvb := hden'.1
  have hsl : (slice X.json ((reg n0 26).toNat - X.D.toNat) (memLoad32 M (acSlot X.B 0x30)).toNat).length =
      (memLoad32 M (acSlot X.B 0x30)).toNat := by
    simp only [slice, List.length_take, List.length_drop]; omega
  have hvl : vp + vl ≤ (memLoad32 M (acSlot X.B 0x30)).toNat := hsl ▸ hden.1
  have hq : (reg n0 26 + BitVec.ofNat 32 vp).toNat = (reg n0 26).toNat + vp := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨hF0, t0, t4⟩ := hF
  refine WP.lw ac_at_e5e (aceca_al O 0x890 (by decide) (by decide) (by rsimp; rw [R.r19]; bv_omega)) ?_; wn
  refine WP.branch ac_at_e62 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [R.r19] at eb; (try rw [e0] at eb); rw [t0] at eb
    have e0 : reg n0 26 + BitVec.ofNat 32 vp = 0 := by simpa [branchTaken] using eb
    rw [e0] at hq; simp at hq; omega
  refine WP.lw ac_at_e66 (by rsimp; rw [R.r19, e894]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_e6a ?_; wn
  refine WP.aluImm ac_at_e6c ?_; wn
  refine WP.alu ac_at_e70 ?_; wn
  have hq1 : X.D.toNat ≤ (reg n0 26 + BitVec.ofNat 32 vp).toNat := by omega
  have hq2 : (reg n0 26 + BitVec.ofNat 32 vp).toNat + vl ≤ X.D.toNat + X.json.length := by omega
  have E2 := aceca_env O A hm2
  refine WP.callElements (tb := RJE) (out := acSlot X.B 0x1320) (s := X.B + BitVec.ofNat 32 0x3A40)
    (p := reg n0 26 + BitVec.ofNat 32 vp) (n := vl) ac_at_e72 ac_at_e76 (by decide) (by decide) (by decide)
    E2.elems (by rw [show RJE + 0xFFFFFAB2 = RSW by decide]; exact E2.skipWs)
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; rw [R.r19]; (try rw [e0]); rw [t0])
    (by rsimp; rw [R.r19, t4])
    (by rsimp; rw [R.rsp]; bv_omega)
    (by omega) (ace_al4 F (by decide) (by decide)) (ace_al4 (c := 0x3A50 + 0x1320) F (by decide) (by decide))
    (ace_hs F (by decide) (by decide) (by decide)) (ace_hs F (by decide) (by decide) (by decide))
    (ace_bufSep O (by decide) hq1 hq2)
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from
      ace_sepB' F (.inr (by decide)) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from ace_hs F (by decide) (by decide) (by decide))
    (ace_cs F (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from ace_cs F (by decide)) fun m3 hC => ?_
  rw [aceca_docBytes O A hm2 hq1 hq2] at hC
  generalize m3.mem = M3 at hC
  obtain ⟨M1', hO', hc⟩ := hC
  have hf3 : ∀ x, Sep x 1 (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 → Sep x 1 (X.B + BitVec.ofNat 32 0x3A40) 16 →
      M3 x = M2 x := fun x h1 h2 => (hc.out x h1).trans (hO' x h2)
  have hM3 : ∀ x, AcaW X.B x → M3 x = M2 x := fun x hx =>
    hf3 x (hx.sep F (.inr (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩)))))) (hx.sep F (.inl ⟨by decide, by decide⟩))
  refine aceca_e7a O A I (T2.mono F hM3) (by hr) (by rsimp; exact h26) hf
    ⟨hq1, by rw [hq, show (reg n0 26).toNat + vp - X.D.toNat = (reg n0 26).toNat - X.D.toNat + vp by omega]; exact hden'⟩ ?_ hc
  intro i hi
  rw [ace_ld2 F hf3 (.inl (by omega)) (.inr (by omega)) (by omega) (by decide) (by decide),
    ace_ld2 F hf2 (.inl (by omega)) (.inr (by omega)) (by omega) (by decide) (by decide)]
  exact hz i hi

set_option maxHeartbeats 4000000 in
/-- The loop at 0xE34 that zeroes the log array, with `m` entries left. -/
theorem aceca_zl {X : AceCtx} (O : X.Ok) {n0 : Machine} {fp : Word} {jr : Json} {fs : List FulcioKey}
    (A : AceAt X n0 0xD8C fp) (I : AceCaInv X n0 fp jr [] fs) {L : Machine → Prop} :
    ∀ m, m ≤ 16 → 0 < m → ∀ (M : Word → BitVec 8) (f : Fin 32 → Word), AcaT X n0 fp M → AceHR X f →
      f 26 = reg n0 26 → f 10 = acSlot X.B (0x350 + 0x20 * (16 - m)) → f 11 = BitVec.ofNat 32 m →
      (∀ i, i < 16 - m → memLoad32 M (acSlot X.B (0x350 + 0x20 * i)) = 0) →
      WP bootMainClosure0Code AC (acaQ X (acaP X jr) L) M 0xE34 f := by
  have F := O.lay.fr
  have hh := F.hi
  intro m
  induction m with
  | zero => intro _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ m ih =>
    intro hm _ M f T R h26 h10 h11 hz
    have ea : acSlot X.B (0x350 + 0x20 * (16 - (m + 1))) + 0 =
        X.B + BitVec.ofNat 32 (0x3DA0 + 0x20 * (15 - m)) := by
      unfold acSlot; rw [show (0 : Word) = BitVec.ofNat 32 0 from rfl, add_ofNat_assoc]; congr 2; omega
    refine WP.sw ac_at_e34 (by rw [h10, ea]; exact ace_al4 F (by omega) (by omega))
      (by rw [h10, ea]; exact ace_cs F (by omega)) ?_
    wn
    rw [h10, ea]
    have hx0 : f x0 = 0 := R.rz
    rw [hx0]
    have ha : f a0 = acSlot X.B (0x350 + 0x20 * (16 - (m + 1))) := h10
    have hb : f a1 = BitVec.ofNat 32 (m + 1) := h11
    have hS : ∀ x, AcaW X.B x → memStore32 M (X.B + BitVec.ofNat 32 (0x3DA0 + 0x20 * (15 - m))) 0 x = M x :=
      fun x hx => memStore32_get_sep (hx.sep F (.inr (.inr (.inl ⟨by omega, by omega⟩)))).symm
    have T' := T.mono F hS
    have hz' : ∀ i, i < 16 - m → memLoad32 (memStore32 M (X.B + BitVec.ofNat 32 (0x3DA0 + 0x20 * (15 - m))) 0)
        (acSlot X.B (0x350 + 0x20 * i)) = 0 := by
      intro i hi
      rcases Nat.lt_or_ge i (16 - (m + 1)) with hl | hl
      · rw [show acSlot X.B (0x350 + 0x20 * i) = X.B + BitVec.ofNat 32 (0x3A50 + (0x350 + 0x20 * i)) from rfl,
          memLoad32_store32_sep (ace_sepB' F (.inr (by omega)) (by omega) (by omega))]
        exact hz i hl
      · rw [show acSlot X.B (0x350 + 0x20 * i) = X.B + BitVec.ofNat 32 (0x3DA0 + 0x20 * (15 - m)) by
          unfold acSlot; congr 2; omega, memLoad32_store32_same]
    refine WP.aluImm ac_at_e38 ?_; wn
    refine WP.aluImm ac_at_e3c ?_; wn
    have r11 : aluEval .add (f a1) 4294967295 = BitVec.ofNat 32 m := by
      rw [hb, ev_add]; apply BitVec.eq_of_toNat_eq
      have : (4294967295 : Word).toNat = 4294967295 := rfl
      rw [BitVec.toNat_add, this, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    refine WP.branch ac_at_e3e (fun eb => ?_) (fun eb => ?_) <;> wn
    · rcases Nat.eq_zero_or_pos m with h0 | h0
      · exfalso; rsimp at eb; rw [r11, h0] at eb; simp [branchTaken] at eb
      refine ih (by omega) h0 _ _ T' (by hr) (by rsimp; exact h26) ?_ (by rsimp; exact r11) hz'
      rsimp; rw [ha, ev_add, show (32 : Word) = BitVec.ofNat 32 32 from rfl]; unfold acSlot
      rw [add_ofNat_assoc, show 0x3A50 + (0x350 + 0x20 * (16 - (m + 1))) + 32 = 0x3A50 + (0x350 + 0x20 * (16 - m)) by
        omega]
    · rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        exact aceca_e40 O A I T' (by hr) (by rsimp; exact h26) hz'
      · exfalso; rsimp at eb; rw [r11] at eb
        have : BitVec.ofNat 32 m ≠ 0 := by
          intro e; have h := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat] at h
          have : (0 : Word).toNat = 0 := rfl
          omega
        simp [branchTaken] at eb
        exact this eb

/-- From 0xE2E, when `next_element` found no more certificate authorities:
the tail to 0xEBA. -/
theorem aceca_e2e {X : AceCtx} (O : X.Ok) {n0 : Machine} {fp : Word} {jr : Json} {fs : List FulcioKey}
    (A : AceAt X n0 0xD8C fp) (I : AceCaInv X n0 fp jr [] fs) {L : Machine → Prop}
    {M : Word → BitVec 8} {f : Fin 32 → Word} (T : AcaT X n0 fp M) (R : AceHR X f)
    (h26 : f 26 = reg n0 26) :
    WP bootMainClosure0Code AC (acaQ X (acaP X jr) L) M 0xE2E f := by
  refine WP.aluImm ac_at_e2e ?_; wn
  refine WP.aluImm ac_at_e30 ?_; wn
  refine WP.branch ac_at_e32 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb
  refine aceca_zl O A I 16 (by decide) (by decide) M _ T (by hr) (by rsimp; exact h26) ?_ (by rsimp <;> rfl)
    (fun i hi => absurd hi (Nat.not_lt_zero _))
  rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega

end C3.RV32.Ac
