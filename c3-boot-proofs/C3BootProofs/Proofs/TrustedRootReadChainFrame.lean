import C3BootProofs.Proofs.TrustedRootReadChainKey

/-!
# Stores and copies in `read_chain`'s frame

The blocks of `read_chain`'s body store words and bytes in its frame and
copy parts of it with `memcpy`. These lemmas read a frame byte after such
a change, keep the facts that later blocks need, and track the registers
that a block keeps.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

/-- The registers in `L` hold their values in `w`. -/
def RcK (L : List Nat) (w f : Fin 32 → Word) : Prop := ∀ q : Fin 32, q.val ∈ L → f q = w q

theorem RcK.set {L : List Nat} {w f : Fin 32 → Word} {rd : Fin 32} {v : Word} (h : RcK L w f)
    (hr : rd.val ∉ L) (hz : 0 ∉ L) : RcK L w (upd f rd v) := fun q hq => by
  rw [upd_app]
  have hne : q ≠ rd := fun e => hr (e ▸ hq)
  have h0 : q.val ≠ 0 := fun e => hz (e ▸ hq)
  rw [ite_eq_right h0, ite_eq_right hne]; exact h q hq

theorem RcK.clob {L : List Nat} {w f : Fin 32 → Word} {m : Machine} (h : RcK L w f)
    (hL : ∀ q : Fin 32, q.val ∈ L → q ∉ jClob) : RcK L w (clob f m jClob) := fun q hq => by
  rw [clob_app, ite_eq_right (hL q hq)]; exact h q hq

theorem RcK.mono {L L' : List Nat} {w f : Fin 32 → Word} (h : RcK L w f) (hL : ∀ x, x ∈ L' → x ∈ L) :
    RcK L' w f := fun q hq => h q (hL _ hq)

/-- Proves `RcK` of a register file that `upd` and `clob` build from one
that `h` covers. -/
macro "rc_k " h:term : tactic => `(tactic| (
  repeat (first
    | refine RcK.set ?_ (by decide) (by decide)
    | refine RcK.clob ?_ (by decide))
  exact $h))

/-- Memory that changed only in the stack below `F + lo` and in the
frame's scratch area. -/
def RcKB (G : Word) (lo : Nat) (M M' : Word → BitVec 8) : Prop :=
  ∀ x, Sep G (0x5C0 + lo) x 1 → Sep (G + BitVec.ofNat 32 0x620) 0xEC x 1 → M' x = M x

theorem RcKeep.kb {G : Word} {lo : Nat} {M M' : Word → BitVec 8} (h : RcKeep G M M') : RcKB G lo M M' :=
  fun x a b => h x (sep_low a (by omega)) b

theorem RcKB.refl {G : Word} {lo : Nat} {M : Word → BitVec 8} : RcKB G lo M M := fun _ _ _ => rfl

theorem RcKB.trans {G : Word} {lo : Nat} {M M1 M2 : Word → BitVec 8} (h1 : RcKB G lo M M1)
    (h2 : RcKB G lo M1 M2) : RcKB G lo M M2 :=
  fun x a b => (h2 x a b).trans (h1 x a b)

theorem RcKB.mono {G : Word} {lo lo' : Nat} {M M' : Word → BitVec 8} (h : RcKB G lo M M') (hl : lo ≤ lo') :
    RcKB G lo' M M' :=
  fun x a b => h x (sep_low a (by omega)) b

/-- The bytes apart from the stack region stay. -/
theorem RcKB.out {G : Word} {lo : Nat} {M M' : Word → BitVec 8} (h : RcKB G lo M M') (hlo : lo ≤ 0x60)
    {x : Word} (hx : Sep G 0x740 x 1) : M' x = M x :=
  h x (sep_low hx (by omega)) (sep_in hx.symm (by decide)).symm

theorem RcL.kb {M M' : Word → BitVec 8} {G b : Word} {L : Bytes} {lo : Nat} (h : RcL M G b L)
    (hK : RcKB G lo M M') (hlo : lo ≤ 0x60) : RcL M' G b L :=
  ⟨(memBytes_congr fun j hj => hK.out hlo (h.sep.shift (by omega : j < L.length + 14)).symm).trans h.bytes,
    h.sep, h.pos, h.hw⟩

/-! ## Bytes after a store or a copy -/

theorem rcf_e (B : Word) (c j : Nat) : B + BitVec.ofNat 32 c + BitVec.ofNat 32 j = B + BitVec.ofNat 32 (c + j) :=
  add_ofNat_assoc B c j

/-- A word whose four bytes are four bytes of another memory. -/
theorem rcf_ld {M M' : Word → BitVec 8} {B B' : Word} {c c' : Nat}
    (h : ∀ j, j < 4 → M' (B + BitVec.ofNat 32 (c + j)) = M (B' + BitVec.ofNat 32 (c' + j))) :
    memLoad32 M' (B + BitVec.ofNat 32 c) = memLoad32 M (B' + BitVec.ofNat 32 c') := by
  unfold memLoad32
  have h0 := h 0 (by decide)
  simp only [Nat.add_zero] at h0
  rw [show (3 : Word) = BitVec.ofNat 32 3 from rfl, show (2 : Word) = BitVec.ofNat 32 2 from rfl,
    show (1 : Word) = BitVec.ofNat 32 1 from rfl, rcf_e, rcf_e, rcf_e, rcf_e, rcf_e, rcf_e,
    h 3 (by decide), h 2 (by decide), h 1 (by decide)]
  rw [h0]

theorem rcf_st32o (M : Word → BitVec 8) (B v : Word) {c d : Nat} (hcd : c < d ∨ d + 4 ≤ c)
    (hc : c < 2 ^ 32) (hd : d + 4 ≤ 2 ^ 32) :
    memStore32 M (B + BitVec.ofNat 32 d) v (B + BitVec.ofNat 32 c) = M (B + BitVec.ofNat 32 c) :=
  memStore32_get_sep (sep_offsets B (c := d) (n := 4) (d := c) (k := 1) (by omega) hd (by omega))

theorem rcf_st32i (M : Word → BitVec 8) (B v : Word) {d j : Nat} (hj : j < 4) :
    memStore32 M (B + BitVec.ofNat 32 d) v (B + BitVec.ofNat 32 (d + j)) = v.extractLsb' (8 * j) 8 := by
  have hb := memStore32_bytes M (B + BitVec.ofNat 32 d) v
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · exact hb.1
  · rw [← rcf_e]; exact hb.2.1
  · rw [← rcf_e]; exact hb.2.2.1
  · rw [← rcf_e]; exact hb.2.2.2

theorem rcf_st8o (M : Word → BitVec 8) (B : Word) (v : BitVec 8) {c d : Nat} (hcd : c ≠ d)
    (hc : c < 2 ^ 32) (hd : d < 2 ^ 32) :
    memStore8 M (B + BitVec.ofNat 32 d) v (B + BitVec.ofNat 32 c) = M (B + BitVec.ofNat 32 c) :=
  memStore8_ne (add_ofNat_ne B hc hd hcd)

theorem rcf_cpi (M : Word → BitVec 8) (B S : Word) {N dd c : Nat} (h : dd ≤ c ∧ c < dd + N)
    (hN : dd + N < 2 ^ 32) :
    copyBytes M (B + BitVec.ofNat 32 dd) S N (B + BitVec.ofNat 32 c) = M (S + BitVec.ofNat 32 (c - dd)) := by
  have e : B + BitVec.ofNat 32 c - (B + BitVec.ofNat 32 dd) = BitVec.ofNat 32 (c - dd) := by
    rw [show c = dd + (c - dd) by omega, ← add_ofNat_assoc, BitVec.add_comm (B + BitVec.ofNat 32 dd),
      BitVec.add_sub_cancel, show dd + (c - dd) - dd = c - dd by omega]
  unfold copyBytes
  rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ite_eq_left (by omega)]

theorem rcf_cpo (M : Word → BitVec 8) (B S : Word) {N dd c : Nat} (h : c < dd ∨ dd + N ≤ c)
    (hc : c < 2 ^ 32) (hN : dd + N ≤ 2 ^ 32) :
    copyBytes M (B + BitVec.ofNat 32 dd) S N (B + BitVec.ofNat 32 c) = M (B + BitVec.ofNat 32 c) :=
  copyBytes_sep (n := N) (sep_offsets B (c := dd) (n := N) (d := c) (k := 1) (by omega) hN (by omega))
    (Nat.le_refl N)

/-- A word of the frame after a word store apart from it. -/
theorem rcf_ld32o {M : Word → BitVec 8} {B v : Word} {c d : Nat} (h : c + 4 ≤ d ∨ d + 4 ≤ c)
    (hc : c + 4 ≤ 2 ^ 32) (hd : d + 4 ≤ 2 ^ 32) :
    memLoad32 (memStore32 M (B + BitVec.ofNat 32 d) v) (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
  memLoad32_store32_sep (sep_offsets B h.symm hd hc)

/-- A word of the frame after a byte store apart from it. -/
theorem rcf_ld8o {M : Word → BitVec 8} {B : Word} {v : BitVec 8} {c d : Nat} (h : c + 4 ≤ d ∨ d + 1 ≤ c)
    (hc : c + 4 ≤ 2 ^ 32) (hd : d + 1 ≤ 2 ^ 32) :
    memLoad32 (memStore8 M (B + BitVec.ofNat 32 d) v) (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
  memLoad32_store8_sep (sep_offsets B h.symm hd hc)

section
variable {M0 : Word → BitVec 8} {G F out fr fp p : Word} {fl n : Nat} {g0 : Fin 32 → Word}

/-- A range of the frame is apart from `read_chain`'s code. -/
theorem RcCtx.flo (X : RcCtx M0 G F out fr fp fl p n g0) {c k : Nat} (h : c + k ≤ 0x180) :
    Sep (F + BitVec.ofNat 32 c) k TRC trustedRootReadChainCode.length := by
  rw [X.fG]; exact X.glo (by omega) (by decide) (by decide)

theorem RcCtx.stK (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {c k : Nat}
    (hc : 0x60 ≤ c ∧ c + k ≤ 0x14C) (h : ∀ x, Sep (F + BitVec.ofNat 32 c) k x 1 → M' x = M x) : RcKeep G M M' :=
  fun x _ xb => h x (by rw [X.fG]; exact rc_gin xb (by omega) (by omega))

theorem RcCtx.stB (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {c k lo : Nat}
    (hc : c + k ≤ lo) (h : ∀ x, Sep (F + BitVec.ofNat 32 c) k x 1 → M' x = M x) : RcKB G lo M M' :=
  fun x xa _ => h x (by rw [X.fG]; exact rc_gin (rc_g0 xa) (by omega) (by omega))

theorem RcCtx.stI (X : RcCtx M0 G F out fr fp fl p n g0) {M M' : Word → BitVec 8} {c k : Nat}
    (I : RcMemInv M0 G F fr fp fl g0 M) (hc : c + k ≤ 0x14C)
    (h : ∀ x, Sep (F + BitVec.ofNat 32 c) k x 1 → M' x = M x) : RcMemInv M0 G F fr fp fl g0 M' :=
  RcMemInv.step X I (c := 0x5C0 + c) (l := k) (by omega) fun x a _ _ => h x (by rw [X.fG]; exact a)

theorem RcCtx.sw32 (_X : RcCtx M0 G F out fr fp fl p n g0) (M : Word → BitVec 8) (c : Nat) (v : Word) :
    ∀ x, Sep (F + BitVec.ofNat 32 c) 4 x 1 → memStore32 M (F + BitVec.ofNat 32 c) v x = M x :=
  fun _ hx => memStore32_get_sep hx

theorem RcCtx.sw8 (_X : RcCtx M0 G F out fr fp fl p n g0) (M : Word → BitVec 8) (c : Nat) (v : BitVec 8) :
    ∀ x, Sep (F + BitVec.ofNat 32 c) 1 x 1 → memStore8 M (F + BitVec.ofNat 32 c) v x = M x :=
  fun x hx => memStore8_ne fun e => hx 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e])

theorem RcCtx.cpF (_X : RcCtx M0 G F out fr fp fl p n g0) (M : Word → BitVec 8) (dd N : Nat) (S : Word) :
    ∀ x, Sep (F + BitVec.ofNat 32 dd) N x 1 → copyBytes M (F + BitVec.ofNat 32 dd) S N x = M x :=
  fun _ hx => copyBytes_sep hx (Nat.le_refl N)

end

end C3.RV32
