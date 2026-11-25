import C3BootProofs.Proofs.TrustedRootReadChainCtx

/-!
# `read_chain`'s error writers and calls

`RcKeep G M M'` says a callee changed memory only in the two parts of the
stack region that callees use: the stack below the frame, and the frame's
scratch area from `F + 0x60` up to the saved registers. The words below
`F + 0x60`, which hold the array cursor, the first certificate, and values
that live across calls, stay.

Each `RcCtx.call…` lemma is one callee's theorem in that frame: it proves
the callee's preconditions from `RcCtx`, and hands the continuation the
callee's result and `RcKeep`, or the exact writes of a callee that writes
outside the scratch area.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

/-- Memory that changed only in the stack below the frame and in the
frame's scratch area. -/
def RcKeep (G : Word) (M M' : Word → BitVec 8) : Prop :=
  ∀ x, Sep G 0x5C0 x 1 → Sep (G + BitVec.ofNat 32 0x620) 0xEC x 1 → M' x = M x

theorem RcKeep.refl {G : Word} {M : Word → BitVec 8} : RcKeep G M M := fun _ _ _ => rfl

theorem RcKeep.trans {G : Word} {M M1 M2 : Word → BitVec 8} (h1 : RcKeep G M M1) (h2 : RcKeep G M1 M2) :
    RcKeep G M M2 :=
  fun x a b => (h2 x a b).trans (h1 x a b)

/-- A range of the stack region inside another. -/
theorem rc_gin {G x : Word} {a k b l : Nat} (h : Sep (G + BitVec.ofNat 32 a) k x 1) (hab : a ≤ b)
    (hbl : b + l ≤ a + k) : Sep (G + BitVec.ofNat 32 b) l x 1 := by
  have := h.sub (c := b - a) (l := l) (by omega)
  rwa [add_ofNat_assoc, show a + (b - a) = b by omega] at this

theorem rc_g0 {G x : Word} {k : Nat} (h : Sep G k x 1) : Sep (G + BitVec.ofNat 32 0) k x 1 := by
  rwa [add_ofNat_zero]

theorem rc_g0' {G x : Word} {k : Nat} (h : Sep (G + BitVec.ofNat 32 0) k x 1) : Sep G k x 1 := by
  rwa [add_ofNat_zero] at h

/-- `RcKeep` from a callee whose writes stay in the range `a`, `k` below
the frame and the range `b`, `l` in the scratch area. -/
theorem RcKeep.of2 {G : Word} {M M' : Word → BitVec 8} {a k b l : Nat} (hak : a + k ≤ 0x5C0)
    (hb : 0x620 ≤ b) (hbl : b + l ≤ 0x70C)
    (h : ∀ x, Sep (G + BitVec.ofNat 32 a) k x 1 → Sep (G + BitVec.ofNat 32 b) l x 1 → M' x = M x) :
    RcKeep G M M' :=
  fun x xa xb => h x (rc_gin (rc_g0 xa) (by omega) (by omega)) (rc_gin xb hb (by omega))

/-- `RcKeep` from a callee whose writes stay in the scratch area. -/
theorem RcKeep.of1 {G : Word} {M M' : Word → BitVec 8} {b l : Nat} (hb : 0x620 ≤ b) (hbl : b + l ≤ 0x70C)
    (h : ∀ x, Sep (G + BitVec.ofNat 32 b) l x 1 → M' x = M x) : RcKeep G M M' :=
  fun x _ xb => h x (rc_gin xb hb (by omega))

theorem RcKeep.foot {G fr fp : Word} {fl : Nat} {M M' : Word → BitVec 8} (h : RcKeep G M M') :
    ∀ x, Sep (G + BitVec.ofNat 32 0) 0x70C x 1 → Sep fr 8 x 1 → Sep fp fl x 1 → M' x = M x :=
  fun x hx _ _ => h x (rc_g0' (rc_gin hx (by omega) (by omega))) (rc_gin hx (by omega) (by omega))

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

/-- A byte of the stack region outside both changed parts. -/
theorem RcCtx.keepAt (_X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} (h : RcKeep G M M')
    {d : Nat} (hd : 0x5C0 ≤ d ∧ d < 0x620 ∨ 0x70C ≤ d ∧ d < 0x740) :
    M' (G + BitVec.ofNat 32 d) = M (G + BitVec.ofNat 32 d) :=
  h _ (rc_g0' (sep_offsets G (c := 0) (n := 0x5C0) (d := d) (k := 1) (Or.inl (by omega)) (by omega) (by omega)))
    (sep_offsets G (c := 0x620) (n := 0xEC) (d := d) (k := 1) (by omega) (by omega) (by omega))

/-- A word of the frame below `F + 0x60` stays. -/
theorem RcCtx.keepLd (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} (h : RcKeep G M M')
    {c : Nat} (hc : c + 4 ≤ 0x60) :
    memLoad32 M' (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by
    rw [X.fG, add_ofNat_assoc]; exact X.keepAt h (Or.inl ⟨by omega, by omega⟩)

/-- A byte of the frame below `F + 0x60` stays. -/
theorem RcCtx.keepB (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} (h : RcKeep G M M')
    {c : Nat} (hc : c < 0x60) : M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  rw [X.fG]; exact X.keepAt h (Or.inl ⟨by omega, by omega⟩)

/-- Bytes apart from the stack region stay. -/
theorem RcCtx.keepOut (_X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} (h : RcKeep G M M')
    {a : Word} {l : Nat} (ha : Sep a l G 0x740) : memBytes M' a l = memBytes M a l :=
  memBytes_congr fun j hj =>
    h _ (rc_g0' ((ha.shift hj).symm.sub (c := 0) (l := 0x5C0) (by omega)))
      ((ha.shift hj).symm.sub (c := 0x620) (l := 0xEC) (by omega))

/-- The `Err` writer at 0x484, with the error byte in `a0`. -/
theorem RcCtx.e484 (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {e : Option Nat} {r : Except (Option Nat) (RcCert × RcSt)} (hr : r = .error e)
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hb : ∀ b, e = some b → (f a0).extractLsb' 0 8 = BitVec.ofNat 8 b) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x484 f :=
  X.errW trc_at_484 trc_at_488 id hr hR hI hb

/-- The `Err` writer at 0x504, with the error byte in `s2`. -/
theorem RcCtx.e504 (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {e : Option Nat} {r : Except (Option Nat) (RcCert × RcSt)} (hr : r = .error e)
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hb : ∀ b, e = some b → (f 18).extractLsb' 0 8 = BitVec.ofNat 8 b) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x504 f :=
  X.errW trc_at_504 trc_at_508 (fun h => WP.jal trc_at_50c (by decide) h) hr hR hI hb

/-- The `Err` writer at 0x4C8, with the error byte in `s0`. -/
theorem RcCtx.e4c8 (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {e : Option Nat} {r : Except (Option Nat) (RcCert × RcSt)} (hr : r = .error e)
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hb : ∀ b, e = some b → (f 8).extractLsb' 0 8 = BitVec.ofNat 8 b) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x4C8 f :=
  X.errW trc_at_4c8 trc_at_4cc (fun h => WP.jal trc_at_4d0 (by decide) h) hr hR hI hb

/-- An error byte that a `lbu` loaded. -/
theorem rc_lbuB {e : Option Nat} {v : BitVec 8} (h : ∀ b, e = some b → v = BitVec.ofNat 8 b) :
    ∀ b, e = some b → (v.zeroExtend 32).extractLsb' 0 8 = BitVec.ofNat 8 b :=
  fun b hb => by rw [ri_ze]; exact h b hb

/-- The error path at `pc` that loads the error byte at `F + c` into `a0`
and goes to 0x484. -/
theorem RcCtx.eA0 (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {e : Option Nat} {r : Except (Option Nat) (RcCert × RcSt)} {pc : Nat} {c o : Word}
    (h1 : fetchRel trustedRootReadChainCode pc = some (.load .lbu a0 sp c, 4))
    (h2 : fetchRel trustedRootReadChainCode (pc + 4) = some (.jal 0 o, 2))
    (hj : (pc + 4 + o.toNat) % 2 ^ 32 = 0x484)
    (hr : r = .error e) (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hb : ∀ b, e = some b → M (F + c) = BitVec.ofNat 8 b) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M pc f := by
  refine WP.lbu h1 ?_
  refine WP.jal (by simpa using h2) (by rw [show (4 : Word).toNat = 4 from rfl, hj]) ?_
  rw [show (4 : Word).toNat = 4 from rfl, hj]
  exact X.e484 hr (by rc_regs hR) hI (by trsimp; rw [hR.2.1]; exact rc_lbuB hb)

/-- The error path at 0x480: the error byte at `F + 0x64`. -/
theorem RcCtx.e480 (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {e : Option Nat} {r : Except (Option Nat) (RcCert × RcSt)} (hr : r = .error e)
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hb : ∀ b, e = some b → M (F + 0x64) = BitVec.ofNat 8 b) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x480 f := by
  refine WP.lbu trc_at_480 ?_
  exact X.e484 hr (by rc_regs hR) hI (by trsimp; rw [hR.2.1]; exact rc_lbuB hb)

/-- The error path at 0x4C2: the error byte at `F + 0xD4`. -/
theorem RcCtx.e4c2 (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {e : Option Nat} {r : Except (Option Nat) (RcCert × RcSt)} (hr : r = .error e)
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hb : ∀ b, e = some b → M (F + 0xD4) = BitVec.ofNat 8 b) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x4C2 f :=
  X.eA0 trc_at_4c2 trc_at_4c6 (by decide) hr hR hI hb

/-- The error path at 0x68: the error byte at `F + 0xE1`. -/
theorem RcCtx.e068 (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {e : Option Nat} {r : Except (Option Nat) (RcCert × RcSt)} (hr : r = .error e)
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hb : ∀ b, e = some b → M (F + 0xE1) = BitVec.ofNat 8 b) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x68 f :=
  X.eA0 trc_at_68 trc_at_6c (by decide) hr hR hI hb

/-- The error path at 0x4FC: the error byte at `F + 0xE4`. -/
theorem RcCtx.e4fc (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {e : Option Nat} {r : Except (Option Nat) (RcCert × RcSt)} (hr : r = .error e)
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hb : ∀ b, e = some b → M (F + 0xE4) = BitVec.ofNat 8 b) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x4FC f :=
  X.eA0 trc_at_4fc trc_at_500 (by decide) hr hR hI hb

/-- The error path at 0x4F0: error 0x21. -/
theorem RcCtx.e4f0 (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {r : Except (Option Nat) (RcCert × RcSt)} (hr : r = .error (some 0x21))
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x4F0 f := by
  refine WP.aluImm trc_at_4f0 ?_; wn
  refine WP.jal trc_at_4f4 (by decide) ?_; wn
  exact X.e484 hr (by rc_regs hR) hI (by
    intro b hb; cases hb; trsimp; rw [hR.1]; rfl)

/-- The error path at `pc` that loads the error byte at `F + c` into `s2`
and goes to 0x504. -/
theorem RcCtx.eS2 (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {e : Option Nat} {r : Except (Option Nat) (RcCert × RcSt)} {pc : Nat} {c o : Word}
    (h1 : fetchRel trustedRootReadChainCode pc = some (.load .lbu 18 sp c, 4))
    (h2 : fetchRel trustedRootReadChainCode (pc + 4) = some (.jal 0 o, 2))
    (hj : (pc + 4 + o.toNat) % 2 ^ 32 = 0x504)
    (hr : r = .error e) (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hb : ∀ b, e = some b → M (F + c) = BitVec.ofNat 8 b) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M pc f := by
  refine WP.lbu h1 ?_
  refine WP.jal (by simpa using h2) (by rw [show (4 : Word).toNat = 4 from rfl, hj]) ?_
  rw [show (4 : Word).toNat = 4 from rfl, hj]
  exact X.e504 hr (by rc_regs hR) hI (by trsimp; rw [hR.2.1]; exact rc_lbuB hb)

/-- The error path at 0x4D2: the error byte at `F + 0xE4`. -/
theorem RcCtx.e4d2 (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {e : Option Nat} {r : Except (Option Nat) (RcCert × RcSt)} (hr : r = .error e)
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hb : ∀ b, e = some b → M (F + 0xE4) = BitVec.ofNat 8 b) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x4D2 f :=
  X.eS2 trc_at_4d2 trc_at_4d6 (by decide) hr hR hI hb

/-- The error path at 0x4F6: the error byte at `F + 0xE1`. -/
theorem RcCtx.e4f6 (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {e : Option Nat} {r : Except (Option Nat) (RcCert × RcSt)} (hr : r = .error e)
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hb : ∀ b, e = some b → M (F + 0xE1) = BitVec.ofNat 8 b) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x4F6 f :=
  X.eS2 trc_at_4f6 trc_at_4fa (by decide) hr hR hI hb

/-- The error path at 0x502: error 1. -/
theorem RcCtx.e502 (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {r : Except (Option Nat) (RcCert × RcSt)} (hr : r = .error (some 1))
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M) :
    WP trustedRootReadChainCode TRC (trPost (rcMem M0 G out fr fp fl r) g0) M 0x502 f := by
  refine WP.aluImm trc_at_502 ?_; wn
  exact X.e504 hr (by rc_regs hR) hI (by intro b hb; cases hb; trsimp; rw [hR.1]; rfl)

end

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

theorem RcCtx.fneg (X : RcCtx M0 G F out fr fp fl p n g0) {w : Word} {k : Nat} (hk : 0 < k ∧ k ≤ 0x5C0)
    (hw : w.toNat = 2 ^ 32 - k) : F + w = G + BitVec.ofNat 32 (0x5C0 - k) := by
  rw [← X.fg]; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hw]
  have := X.gw; omega

theorem RcCtx.ga4 (X : RcCtx M0 G F out fr fp fl p n g0) {c : Nat} (hc : c ≤ 0x740) (h4 : c % 4 = 0) :
    (G + BitVec.ofNat 32 c).toNat % 4 = 0 := by
  rw [X.gc hc]; have := X.ga; omega

theorem RcCtx.fal (X : RcCtx M0 G F out fr fp fl p n g0) {c : Nat} (h4 : c % 4 = 0) :
    (F + BitVec.ofNat 32 c).toNat % 4 = 0 :=
  aligned_add X.fa4 h4

/-- `F` as the top of a callee's stack of `k` bytes. -/
theorem RcCtx.ftop (X : RcCtx M0 G F out fr fp fl p n g0) {k : Nat} (hk : k ≤ 0x5C0) :
    F = G + BitVec.ofNat 32 (0x5C0 - k) + BitVec.ofNat 32 k := by
  rw [add_ofNat_assoc, show 0x5C0 - k + k = 0x5C0 by omega, X.fg]

/-- The call of a callee that keeps `RcKeep`. -/
theorem RcCtx.callK (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {off : Nat} {hi lo tb : Word} {P : Machine → Prop}
    (h1 : fetchRel trustedRootReadChainCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootReadChainCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TRC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = tb)
    (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hcallee : ∀ m1 : Machine, m1.pc = tb → m1.mem = M →
      (∀ x, reg m1 x = upd f ra (TRC + BitVec.ofNat 32 (off + 8)) x) →
      ∃ m2, Steps m1 m2 ∧ m2.pc = TRC + BitVec.ofNat 32 (off + 8) ∧ (RcKeep G M m2.mem ∧ P m2) ∧
        reg m2 sp = reg m1 sp ∧ ∀ q : Fin 32, q.val ∈ trSaved → reg m2 q = reg m1 q)
    (k : ∀ m2 : Machine, RcKeep G M m2.mem → P m2 → RcMemInv M0 G F fr fp fl g0 m2.mem →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f :=
  X.call (c := 0) (l := 0x70C) h1 h2 htgt hI (by decide) hcallee (fun _ hP => hP.1.foot)
    (fun m2 hP hI' => k m2 hP.1 hP.2 hI')

theorem FieldRes.self {M M' : Word → BitVec 8} {out : Word} {r : Except Nat (Word × Nat)}
    (h : FieldRes M M' out r) : FieldRes M' M' out r := by
  rcases r with _ | ⟨_, _⟩
  · exact ⟨fun _ _ => rfl, h.2⟩
  · exact ⟨fun _ _ => rfl, h.2⟩

theorem CurRes.self {M M' : Word → BitVec 8} {out : Word} {e : BitVec 8} {r : Option (Word × Nat × Nat)}
    (h : CurRes M M' out e r) : CurRes M' M' out e r := by
  rcases r with _ | ⟨_, _, _⟩
  · exact ⟨fun _ _ => rfl, h.2⟩
  · exact ⟨fun _ _ => rfl, h.2⟩

theorem SliceRes.self {M M' : Word → BitVec 8} {out : Word} {e : BitVec 8} {r : Option (Word × Nat)}
    (h : SliceRes M M' out e r) : SliceRes M' M' out e r := by
  rcases r with _ | ⟨_, _⟩
  · exact ⟨fun _ _ => rfl, h.2⟩
  · exact ⟨fun _ _ => rfl, h.2⟩

/-- The call of `Value::field` at `off` with the result at `F + c`. -/
theorem RcCtx.callField (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {off c : Nat} {hi lo q kq : Word} {l kl : Nat} {d key : Bytes}
    (h1 : fetchRel trustedRootReadChainCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootReadChainCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TRC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = TJF)
    (hev : (TRC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = TRC + BitVec.ofNat 32 (off + 8))
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (hc : 0x60 ≤ c) (hc8 : c + 8 ≤ 0x14C) (hca : c % 4 = 0)
    (ha0 : f a0 = F + BitVec.ofNat 32 c) (ha1 : f a1 = q) (ha2 : f a2 = BitVec.ofNat 32 l) (ha3 : f a3 = kq)
    (ha4 : f a4 = BitVec.ofNat 32 kl) (hq0 : q.toNat ≠ 0) (hqw : q.toNat + l < 2 ^ 32) (hkw : kl < 2 ^ 32)
    (hqG : Sep q l G 0x740) (hkG : Sep kq kl G 0x740) (hd : memBytes M q l = d) (hk : memBytes M kq kl = key)
    (k : ∀ m2 : Machine, RcKeep G M m2.mem → RcMemInv M0 G F fr fp fl g0 m2.mem →
      FieldRes m2.mem m2.mem (F + BitVec.ofNat 32 c) (fieldRes q (objField d key)) →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f := by
  have gw := X.gw
  refine X.callK (P := fun m2 => FieldRes m2.mem m2.mem (F + BitVec.ofNat 32 c) (fieldRes q (objField d key)))
    h1 h2 htgt hI (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hK hP hI' => k m2 hK hI' hP)
  have C := X.codeAt hI
  obtain ⟨m2, c2, pc2, R, fr'⟩ := jsonField_correct m1 (base := TJF) (s := G + BitVec.ofNat 32 0x4BC)
    (out := F + BitVec.ofNat 32 c) (p := q) (kq := kq) (n := l) (kl := kl)
    (retAddr := TRC + BitVec.ofNat 32 (off + 8)) (by decide)
    (by rw [hmem1]; exact C.tvf.field) hpc1 (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1)
    (by rw [hreg1]; trsimp; exact ha2) (by rw [hreg1]; trsimp; exact ha3) (by rw [hreg1]; trsimp; exact ha4)
    (by rw [hreg1]; trsimp; rw [hR.2.1]; exact X.ftop (k := 260) (by decide)) (by rw [hreg1]; trsimp) hev
    (X.ga4 (by decide) (by decide)) (X.fal hca) (by rw [X.gc (by decide)]; omega) hkw hq0 hqw
    (tvf_fieldSep (by rw [X.gc (by decide)]; omega) (X.ro.sub (by decide))) (hqG.symm.sub (by decide))
    (hkG.symm.sub (by decide)) (by rw [X.fG]; exact X.gsep (Or.inr (by omega)) (by omega) (by decide))
    (by rw [X.fG]; exact X.glo (by omega) (by decide) (by decide))
  rw [hmem1, hd, hk] at R
  obtain ⟨M1, hO1, hFR⟩ := R
  refine ⟨m2, c2, pc2, ⟨RcKeep.of2 (a := 0x4BC) (k := 260) (b := 0x5C0 + c) (l := 8) (by decide) (by omega)
    (by omega) (fun x xa xb => ?_), hFR.self⟩, by rw [fr' sp (by decide)], fun q hq => fr' q (tvf_saved_nc q hq)⟩
  exact (hFR.out x (by rw [X.fG]; exact xb.symm)).trans (hO1 x xa.symm)

/-- The call of `valid_for` at 0x5A with the result at `F + 0xE0`. -/
theorem RcCtx.callTvf (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {q : Word} {l : Nat} {d : Bytes}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (ha0 : f a0 = F + BitVec.ofNat 32 0xE0) (ha1 : f a1 = q) (ha2 : f a2 = BitVec.ofNat 32 l)
    (hqw : q.toNat + l + 4 ≤ 0x40000000) (hq0 : q.toNat ≠ 0) (hqG : Sep q (l + 4) G 0x740)
    (hd : memBytes M q l = d)
    (k : ∀ m2 : Machine, RcKeep G M m2.mem → RcMemInv M0 G F fr fp fl g0 m2.mem →
      TvfOut m2.mem (F + BitVec.ofNat 32 0xE0) (validForPos d) →
      WP trustedRootReadChainCode TRC Q m2.mem 0x62 (clob (upd f ra (TRC + BitVec.ofNat 32 0x62)) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M 0x5A f := by
  have gw := X.gw
  have eG : F + 0xFFFFFEBC = G + BitVec.ofNat 32 0x47C := X.fneg (k := 0x144) (by decide) (by decide)
  refine X.callK (off := 0x5A) (tb := TVF) (P := fun m2 => TvfOut m2.mem (F + BitVec.ofNat 32 0xE0) (validForPos d))
    trc_at_5a trc_at_5e (by decide) hI (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hK hP hI' => k m2 hK hI' hP)
  have C := X.codeAt hI
  rw [← hmem1] at C
  obtain ⟨m2, c2, pc2, hsp2, hk2, R⟩ := trustedRootValidFor_correct m1 (sp0 := F) (out := F + BitVec.ofNat 32 0xE0)
    (p := q) (n := l) (retAddr := TRC + BitVec.ofNat 32 (0x5A + 8)) C.tvf (by rw [hpc1])
    (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp; exact ha2)
    (by rw [hreg1]; trsimp) (by decide) (by rw [hreg1]; trsimp; exact hR.2.1) X.fa4 (by rw [X.fn]; omega)
    (by rw [X.fn]; omega) (X.fal (by decide)) (by rw [X.fG, X.gc (by decide)]; omega) hqw hq0
    (by rw [eG, X.fG]; exact X.gsep (Or.inr (by decide)) (by decide) (by decide))
    (by rw [eG]; exact hqG.symm.sub (by decide) |>.symm |> fun h => h)
    (by rw [eG]; exact X.ro.sub (by decide)) C.ks C.ke
  rw [hmem1, hd] at R
  refine ⟨m2, c2, pc2, ⟨RcKeep.of2 (a := 0x47C) (k := 0x144) (b := 0x6A0) (l := 0x18) (by decide) (by decide)
    (by decide) (fun x xa xb => ?_), R.1⟩, by rw [hsp2, hreg1]; trsimp; exact hR.2.1.symm, hk2⟩
  exact R.2 x (by rw [eG]; exact xa) (by rw [X.fG]; exact xb)

/-- The call of `Value::elements` at 0xB4 with the result at `F + 0xE0`. -/
theorem RcCtx.callElems (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {q : Word} {l : Nat} {d : Bytes}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (ha0 : f a0 = F + BitVec.ofNat 32 0xE0) (ha1 : f a1 = q) (ha2 : f a2 = BitVec.ofNat 32 l)
    (hl : l < 2 ^ 32) (hqG : Sep q l G 0x740) (hd : memBytes M q l = d)
    (k : ∀ m2 : Machine, RcKeep G M m2.mem → RcMemInv M0 G F fr fp fl g0 m2.mem →
      CurRes m2.mem m2.mem (F + BitVec.ofNat 32 0xE0) 0x21 (curOpen 91 q d) →
      WP trustedRootReadChainCode TRC Q m2.mem 0xBC (clob (upd f ra (TRC + BitVec.ofNat 32 0xBC)) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M 0xB4 f := by
  have gw := X.gw
  refine X.callK (off := 0xB4) (tb := RJE)
    (P := fun m2 => CurRes m2.mem m2.mem (F + BitVec.ofNat 32 0xE0) 0x21 (curOpen 91 q d))
    trc_at_b4 trc_at_b8 (by decide) hI (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hK hP hI' => k m2 hK hI' hP)
  have C := X.codeAt hI
  rw [← hmem1] at C
  obtain ⟨m2, c2, pc2, R, fr'⟩ := jsonElements_correct m1 (base := RJE) (s := G + BitVec.ofNat 32 0x5B0)
    (out := F + BitVec.ofNat 32 0xE0) (p := q) (n := l) (retAddr := TRC + BitVec.ofNat 32 (0xB4 + 8))
    (by decide) C.je (by rw [show RJE + 0xFFFFFAB2 = RSW from by decide]; exact C.sw) hpc1
    (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp; exact ha2)
    (by rw [hreg1]; trsimp; rw [hR.2.1]; exact X.ftop (k := 16) (by decide)) hl (X.ga4 (by decide) (by decide))
    (X.fal (by decide)) (by rw [hreg1]; trsimp) (by decide) (X.glo (by decide) (by decide) (by decide))
    (X.glo (by decide) (by decide) (by decide)) (hqG.symm.sub (by decide))
    (by rw [X.fG]; exact X.gsep (Or.inr (by decide)) (by decide) (by decide))
    (by rw [X.fG]; exact X.glo (by decide) (by decide) (by decide))
  rw [hmem1, hd] at R
  obtain ⟨M1, hO1, hCR⟩ := R
  refine ⟨m2, c2, pc2, ⟨RcKeep.of2 (a := 0x5B0) (k := 16) (b := 0x6A0) (l := 12) (by decide) (by decide)
    (by decide) (fun x xa xb => ?_), hCR.self⟩, by rw [fr' sp (by decide)], fun q hq => fr' q (tvf_saved_nc q hq)⟩
  exact (hCR.out x (by rw [X.fG]; exact xb.symm)).trans (hO1 x xa.symm)

/-- The call of `Value::str` at 0x12C with the result at `F + 0x60`. -/
theorem RcCtx.callStr (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {q : Word} {l : Nat} {d : Bytes}
    (hI : RcMemInv M0 G F fr fp fl g0 M)
    (ha0 : f a0 = F + BitVec.ofNat 32 0x60) (ha1 : f a1 = q) (ha2 : f a2 = BitVec.ofNat 32 l)
    (hl : l < 2 ^ 32) (hd : memBytes M q l = d)
    (k : ∀ m2 : Machine, RcKeep G M m2.mem → RcMemInv M0 G F fr fp fl g0 m2.mem →
      SliceRes m2.mem m2.mem (F + BitVec.ofNat 32 0x60) 0x21 (strRes q d) →
      WP trustedRootReadChainCode TRC Q m2.mem 0x134 (clob (upd f ra (TRC + BitVec.ofNat 32 0x134)) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M 0x12C f := by
  have gw := X.gw
  refine X.callK (off := 0x12C) (tb := TJS)
    (P := fun m2 => SliceRes m2.mem m2.mem (F + BitVec.ofNat 32 0x60) 0x21 (strRes q d))
    trc_at_12c trc_at_130 (by decide) hI (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hK hP hI' => k m2 hK hI' hP)
  have C := X.codeAt hI
  rw [← hmem1] at C
  obtain ⟨m2, c2, pc2, R, fr'⟩ := jsonStr_correct m1 (base := TJS) (out := F + BitVec.ofNat 32 0x60) (p := q)
    (n := l) (retAddr := TRC + BitVec.ofNat 32 (0x12C + 8)) (by decide) C.tvf.str hpc1
    (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp; exact ha2) hl
    (X.fal (by decide)) (by rw [X.fG]; exact X.glo (by decide) (by decide) (by decide)) (by rw [hreg1]; trsimp)
    (by decide)
  rw [hmem1, hd] at R
  refine ⟨m2, c2, pc2, ⟨RcKeep.of1 (b := 0x620) (l := 8) (by decide) (by decide) (fun x xb => ?_), R.self⟩,
    by rw [fr' sp (by decide)], fun q hq => fr' q (tvf_saved_ns q hq)⟩
  exact R.out x (by rw [X.fG]; exact xb.symm)

/-- `RiSep` for a range of the stack region. -/
theorem RcCtx.riSep (X : RcCtx M0 G F out fr fp fl p n g0) {c k : Nat} (h : c + k ≤ 0x740) :
    RiSep (G + BitVec.ofNat 32 c) k (RJN + 0xFFFFF7E0) := by
  have hw : (G + BitVec.ofNat 32 c).toNat + k ≤ 0x40000000 := by rw [X.gc (by omega)]; have := X.gw; omega
  have hro : Sep (G + BitVec.ofNat 32 c) k TVF_RO 0x1400 := X.ro.sub h
  exact ⟨lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide),
    lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide),
    lowSep hw (by decide) (by decide), rc_roSub hro (by decide), rc_roSub hro (by decide)⟩

/-- The call of `next_element` at `off` with the result at `F + 0xE0` and
the array cursor at `F + 0x24`, which moves the cursor's position at
`F + 0x2C`. -/
theorem RcCtx.callNext (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {off : Nat} {hi lo q : Word} {l pos : Nat} {d : Bytes}
    (h1 : fetchRel trustedRootReadChainCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootReadChainCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TRC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = RJN)
    (hev : (TRC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = TRC + BitVec.ofNat 32 (off + 8))
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (ha0 : f a0 = F + BitVec.ofNat 32 0xE0) (ha1 : f a1 = F + BitVec.ofNat 32 0x24)
    (hmp : memLoad32 M (F + BitVec.ofNat 32 0x24) = q) (hmn : memLoad32 M (F + BitVec.ofNat 32 0x28) = BitVec.ofNat 32 l)
    (hmq : memLoad32 M (F + BitVec.ofNat 32 0x2C) = BitVec.ofNat 32 pos) (hl : l < 2 ^ 32) (hpos : pos < 2 ^ 32)
    (hq0 : q.toNat ≠ 0) (hql : q.toNat + l ≤ 2 ^ 32) (hqG : Sep q l G 0x740) (hd : memBytes M q l = d)
    (k : ∀ m2 : Machine, RcMemInv M0 G F fr fp fl g0 m2.mem →
      (∃ M1, RcKeep G M M1 ∧ ElemRes M1 m2.mem (F + BitVec.ofNat 32 0xE0) (F + BitVec.ofNat 32 0x24)
        (elemRes q (nextElement d pos))) →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f := by
  have gw := X.gw
  have e28 : F + BitVec.ofNat 32 0x24 + 4 = F + BitVec.ofNat 32 0x28 := by
    rw [show F + BitVec.ofNat 32 0x24 + 4 = F + BitVec.ofNat 32 0x24 + BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  have e2C : F + BitVec.ofNat 32 0x24 + 8 = G + BitVec.ofNat 32 0x5EC := by
    rw [show F + BitVec.ofNat 32 0x24 + 8 = F + BitVec.ofNat 32 0x24 + BitVec.ofNat 32 8 from rfl, add_ofNat_assoc,
      X.fG]
  refine X.call (c := 0) (l := 0x70C)
    (P := fun m2 => ∃ M1, RcKeep G M M1 ∧ ElemRes M1 m2.mem (F + BitVec.ofNat 32 0xE0) (F + BitVec.ofNat 32 0x24)
      (elemRes q (nextElement d pos)))
    h1 h2 htgt hI (by decide) (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hP x hx hf hb => ?_)
    (fun m2 hP hI' => k m2 hI' hP)
  · have C := X.codeAt hI
    rw [← hmem1] at C
    obtain ⟨m2, c2, pc2, R, fr'⟩ := jsonNextElement_correct m1 (base := RJN) (s := G + BitVec.ofNat 32 0x52C)
      (out := F + BitVec.ofNat 32 0xE0) (c := F + BitVec.ofNat 32 0x24) (p := q) (n := l) (pos := pos)
      (retAddr := TRC + BitVec.ofNat 32 (off + 8)) (by decide) C.jn C.ri hpc1
      (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1)
      (by rw [hreg1]; trsimp; rw [hR.2.1]; exact X.ftop (k := 148) (by decide)) (by rw [hreg1]; trsimp) hev
      (X.ga4 (by decide) (by decide)) (X.fal (by decide)) (X.fal (by decide)) (by rw [hmem1]; exact hmp)
      (by rw [hmem1, e28]; exact hmn) (by rw [hmem1, e2C, show G + BitVec.ofNat 32 0x5EC = F + BitVec.ofNat 32 0x2C from (X.fG 0x2C).symm]; exact hmq) hl hpos hq0 hql
      (X.riSep (by decide)) (X.glo (by decide) (by decide) (by decide)) (hqG.symm.sub (by decide))
      (by rw [X.fG]; exact X.gsep (Or.inr (by decide)) (by decide) (by decide))
      (by rw [X.fG]; exact X.gsep (Or.inr (by decide)) (by decide) (by decide))
      (by rw [X.fG, X.fG]; exact X.gsep (Or.inr (by decide)) (by decide) (by decide))
      (by rw [X.fG]; exact X.glo (by decide) (by decide) (by decide))
      (by rw [X.fG]; exact X.glo (by decide) (by decide) (by decide))
    rw [hmem1, hd] at R
    obtain ⟨M1, hO1, hER⟩ := R
    refine ⟨m2, c2, pc2, ⟨M1, RcKeep.of2 (a := 0x52C) (k := 148) (b := 0x620) (l := 0) (by decide) (by decide)
      (by decide) (fun x xa _ => hO1 x xa.symm), hER⟩, by rw [fr' sp (by decide)],
      fun q hq => fr' q (tvf_saved_nc q hq)⟩
  · obtain ⟨M1, hK, hER⟩ := hP
    refine (hER.out (by rw [X.fG]; exact (rc_gin hx (by decide) (by decide)).symm)
      (by rw [e2C]; exact (rc_gin hx (by decide) (by decide)).symm)).trans (hK.foot x hx hf hb)


/-- The call of `trusted_root::decode` at 0x140 with the result at
`F + 0xD0`, when the scratch slice holds the `fl'` bytes at `fp + o`. -/
theorem RcCtx.callDec (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {t : Word} {tn o fl' : Nat} {d : Bytes}
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (ha0 : f a0 = F + BitVec.ofNat 32 0xD0) (ha1 : f a1 = t) (ha2 : f a2 = BitVec.ofNat 32 tn)
    (ha3 : f a3 = fr) (hfp : memLoad32 M fr = fp + BitVec.ofNat 32 o)
    (hfl : memLoad32 M (fr + 4) = BitVec.ofNat 32 fl') (hol : o + fl' = fl)
    (htw : t.toNat + tn ≤ 0x40000000) (htG : Sep t tn G 0x740) (htB : Sep t tn fp fl) (hd : memBytes M t tn = d)
    (k : ∀ m2 : Machine, RcMemInv M0 G F fr fp fl g0 m2.mem →
      trDecMem M (G + BitVec.ofNat 32 0x550) (F + BitVec.ofNat 32 0xD0) fr (fp + BitVec.ofNat 32 o) fl'
        (trDecodeRes (base64Decode d) fl') m2.mem →
      WP trustedRootReadChainCode TRC Q m2.mem 0x148 (clob (upd f ra (TRC + BitVec.ofNat 32 0x148)) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M 0x140 f := by
  have gw := X.gw
  have bw := X.bw
  have eG : F + 0xFFFFFF90 = G + BitVec.ofNat 32 0x550 := X.fneg (k := 0x70) (by decide) (by decide)
  have ho : (fp + BitVec.ofNat 32 o).toNat = fp.toNat + o := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine X.call (c := 0) (l := 0x70C) (off := 0x140) (tb := TRDC)
    (P := fun m2 => trDecMem M (G + BitVec.ofNat 32 0x550) (F + BitVec.ofNat 32 0xD0) fr (fp + BitVec.ofNat 32 o) fl'
      (trDecodeRes (base64Decode d) fl') m2.mem)
    trc_at_140 trc_at_144 (by decide) hI (by decide) (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hP x hx hf hb => ?_)
    (fun m2 hP hI' => k m2 hI' hP)
  · have C := X.codeAt hI
    rw [← hmem1] at C
    obtain ⟨m2, c2, pc2, hsp2, hk2, R⟩ := trustedRootDecode_correct m1 (sp0 := F) (out := F + BitVec.ofNat 32 0xD0)
      (t := t) (fr := fr) (fp := fp + BitVec.ofNat 32 o) (n := tn) (fl := fl')
      (retAddr := TRC + BitVec.ofNat 32 (0x140 + 8)) C.dec hpc1
      (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp; exact ha2)
      (by rw [hreg1]; trsimp; exact ha3) (by rw [hreg1]; trsimp) (by decide) (by rw [hreg1]; trsimp; exact hR.2.1)
      X.fa4 (by rw [X.fn]; omega) (by rw [X.fn]; omega) (X.fal (by decide))
      (by rw [X.fG, X.gc (by decide)]; omega) X.fa X.fw (by rw [hmem1]; exact hfp) (by rw [hmem1]; exact hfl)
      (by rw [ho]; omega) htw
      (by rw [eG, X.fG]; exact X.gsep (Or.inr (by decide)) (by decide) (by decide))
      (by rw [eG]; exact X.frg.subR (by decide))
      (by rw [eG]; exact (X.bg.sub (c := o) (l := fl') (by omega)).subR (by decide))
      (by rw [eG]; exact htG.subR (by decide)) (htB.subR (by omega))
      (by rw [X.fG]; exact (X.bg.symm.sub (c := 0x690) (l := 8) (by decide)).subR (by omega))
      (X.frp.subR (by omega)) (by rw [X.fG]; exact X.frg.symm.sub (by decide))
    rw [hmem1, eG, hd] at R
    exact ⟨m2, c2, pc2, R, by rw [hsp2, hreg1]; trsimp; exact hR.2.1.symm, hk2⟩
  · exact hP.2 x (rc_gin hx (by decide) (by decide)) (by rw [X.fG]; exact rc_gin hx (by decide) (by decide)) hf
      (hb.sub (by omega))

theorem rc_mc_saved : ∀ q : Fin 32, q.val ∈ trSaved → q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧
    q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧
    q ≠ sp := by decide

/-- The call of `memcpy` at `off` that copies `N` bytes from `src` to
`F + dd`. -/
theorem RcCtx.callMc (X : RcCtx M0 G F out fr fp fl p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word}
    {Q : Post} {off dd N : Nat} {hi lo src : Word}
    (h1 : fetchRel trustedRootReadChainCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootReadChainCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TRC + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = BMS)
    (hev : (TRC + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = TRC + BitVec.ofNat 32 (off + 8))
    (hR : RcRegs F out fr g0 f) (hI : RcMemInv M0 G F fr fp fl g0 M)
    (ha0 : f a0 = F + BitVec.ofNat 32 dd) (ha1 : f a1 = src) (ha2 : f a2 = BitVec.ofNat 32 N)
    (hdN : dd + N ≤ 0x14C) (hsw : src.toNat + N < 2 ^ 32) (hsF : Sep src N (G + BitVec.ofNat 32 0x5B0) 16)
    (hsd : Sep (F + BitVec.ofNat 32 dd) N src N)
    (k : ∀ m2 : Machine, RcMemInv M0 G F fr fp fl g0 m2.mem →
      (∀ x, Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 → m2.mem x = copyBytes M (F + BitVec.ofNat 32 dd) src N x) →
      WP trustedRootReadChainCode TRC Q m2.mem (off + 8) (clob (upd f ra (TRC + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP trustedRootReadChainCode TRC Q M off f := by
  have gw := X.gw
  have eG : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x5B0 := X.fneg (k := 16) (by decide) (by decide)
  refine X.call (c := 0) (l := 0x70C) (tb := BMS)
    (P := fun m2 => ∀ x, Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 → m2.mem x = copyBytes M (F + BitVec.ofNat 32 dd) src N x)
    h1 h2 htgt hI (by decide) (fun m1 hpc1 hmem1 hreg1 => ?_) (fun m2 hP x hx hf hb => ?_)
    (fun m2 hP hI' => k m2 hI' hP)
  · have C := X.codeAt hI
    have hs1 : reg m1 sp = F := by rw [hreg1]; trsimp; exact hR.2.1
    obtain ⟨m2, c2, pc2, hsp2, -, hcp, fr'⟩ := memcpy_correct m1 BMS (TRC + BitVec.ofNat 32 (off + 8))
      (F + BitVec.ofNat 32 dd) src N (fun i hi => by show m1.mem _ = _; rw [hmem1]; exact C.dec.stub i hi)
      (by decide) hpc1 (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1)
      (by rw [hreg1]; trsimp; exact ha2) (by rw [hreg1]; trsimp) hev
      (by
        rw [hs1, eG, hmem1]
        exact ⟨by rw [show BMS + 8 = BMB from by decide]; exact C.dec.body,
          by rw [X.fG]; exact X.glo (by omega) (by decide) (by decide), X.glo (by decide) (by decide) (by decide),
          by rw [X.fG]; exact X.gsep (Or.inr (by omega)) (by omega) (by decide), hsF, hsd,
          X.ga4 (by decide) (by decide), by rw [X.gc (by decide)]; omega,
          by rw [X.fG, X.gc (by omega)]; omega, hsw⟩)
    rw [hs1, eG, hmem1] at hcp
    refine ⟨m2, c2, pc2, hcp, hsp2, fun q hq => ?_⟩
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14⟩ := rc_mc_saved q hq
    exact fr' q e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
  · rw [hP x (rc_gin hx (by decide) (by decide))]
    exact copyBytes_sep (n := N) (by rw [X.fG]; exact rc_gin hx (by omega) (by omega)) (Nat.le_refl N)

/-- A copy into the frame's scratch area keeps `RcKeep`. -/
theorem RcCtx.mcKeep (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {dd N : Nat} {src : Word}
    (hdd : 0x60 ≤ dd) (hdN : dd + N ≤ 0x14C)
    (h : ∀ x, Sep (G + BitVec.ofNat 32 0x5B0) 16 x 1 → M' x = copyBytes M (F + BitVec.ofNat 32 dd) src N x) :
    RcKeep G M M' :=
  RcKeep.of2 (a := 0x5B0) (k := 16) (b := 0x5C0 + dd) (l := N) (by decide) (by omega) (by omega)
    (fun x xa xb => by rw [h x xa]; exact copyBytes_sep (n := N) (by rw [X.fG]; exact xb) (Nat.le_refl N))

end

end C3.RV32
