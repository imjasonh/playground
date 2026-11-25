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

end C3.RV32
