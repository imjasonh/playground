import C3BootProofs.Proofs.P2vLib
import C3BootProofs.Proofs.Fs256Main

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv


/-- The functions that `p256VerifyPrehash`'s steps share. -/
structure P2vCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M P2V p256VerifyPrehashCode
  K : P3Code M
  gs : C3.RV32.Gs.GsCode M

theorem P2vCode.hi {M M' : Word → BitVec 8} (C : P2vCode M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    P2vCode M' :=
  ⟨codeHi C.self (by decide) (by decide) h, C.K.hi h, C.gs.hi h⟩

/-- Bytes that `p256VerifyPrehash` reads but no step writes: outside the
stack, and not wrapping around. -/
structure P2vIn (B rp : Word) (rl : Nat) : Prop where
  sep : Sep rp rl (B + 0xFFFFFE60) 0x3730
  pos : 0 < rp.toNat
  lo : rp.toNat + rl ≤ 0x40000000

theorem P2vIn.fit {B rp : Word} {rl : Nat} (h : P2vIn B rp rl) : rp.toNat + rl < 2 ^ 32 := by
  have := h.lo; omega

theorem P2vIn.sepLo {B rp : Word} {rl : Nat} (h : P2vIn B rp rl) {c n : Nat} (hc : c + n ≤ 0x3590) :
    Sep rp rl (B + BitVec.ofNat 32 c) n := by
  have := h.sep.symm.sub (c := 0x1A0 + c) (l := n) (by omega)
  rw [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + c) = B + BitVec.ofNat 32 c by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega] at this
  exact this.symm

theorem p2v_base' (B : Word) (c : Nat) : B + BitVec.ofNat 32 (0x21A0 + c) = B + 0x21A0 + BitVec.ofNat 32 c :=
  (add_ofNat_assoc B 0x21A0 c).symm


theorem p2v_pt {B rp : Word} {rl : Nat} {M M0 : Word → BitVec 8} (fR : ∀ x, P2vR B x → M x = M0 x)
    (h : P2vIn B rp rl) : ∀ i, i < rl → M (rp + BitVec.ofNat 32 i) = M0 (rp + BitVec.ofNat 32 i) :=
  fun i hi => fR _ (h.sep.sub (c := i) (l := 1) (by omega)).symm

/-- Bytes outside the stack read the same in two memories that agree there. -/
theorem p2v_mb {B rp : Word} {rl : Nat} {M M0 : Word → BitVec 8} (fR : ∀ x, P2vR B x → M x = M0 x)
    (h : P2vIn B rp rl) : memBytes M rp rl = memBytes M0 rp rl :=
  memBytes_congr (p2v_pt fR h)

theorem mb_sub {M M' : Word → BitVec 8} {p : Word} {n : Nat}
    (h : ∀ i, i < n → M (p + BitVec.ofNat 32 i) = M' (p + BitVec.ofNat 32 i)) {c l : Nat} (hl : c + l ≤ n) :
    memBytes M (p + BitVec.ofNat 32 c) l = memBytes M' (p + BitVec.ofNat 32 c) l :=
  memBytes_congr fun i hi => by rw [add_ofNat_assoc]; exact h _ (by omega)

/-- A constant's bytes are outside the stack. -/
theorem dataR {B q : Word} {ql : Nat} (F : Fr B 0x3590) (h1 : (img% dataWindowAddress) ≤ q.toNat) (h2 : q.toNat + ql ≤ (img% dataWindowAddress + dataWindowSize))
    (i : Nat) (hi : i < ql) : P2vR B (q + BitVec.ofNat 32 i) := by
  have hs := F.dsep.subR (c := q.toNat - (img% dataWindowAddress) + i) (l := 1) (by omega)
  have e : (img% dataWindowAddress : Word) + BitVec.ofNat 32 (q.toNat - (img% dataWindowAddress) + i) = q + BitVec.ofNat 32 i := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := q.isLt
    rw [show (img% dataWindowAddress : Word).toNat = (img% dataWindowAddress) from rfl]
    omega
  rw [e] at hs
  exact hs


/-- `M'` agrees with `M` on the frame, except for the ranges in `L`. -/
def P2vKeepL (B : Word) (M M' : Word → BitVec 8) (L : List (Nat × Nat)) : Prop :=
  ∀ e, e + 1 ≤ 0x13F0 → (∀ p ∈ L, e < p.1 ∨ p.1 + p.2 ≤ e) →
    M' (B + 0x21A0 + BitVec.ofNat 32 e) = M (B + 0x21A0 + BitVec.ofNat 32 e)

theorem P2vKeepL.refl {B : Word} {M : Word → BitVec 8} : P2vKeepL B M M [] := fun _ _ _ => rfl

theorem P2vKeepL.trans {B : Word} {M0 M1 M2 : Word → BitVec 8} {L1 L2 : List (Nat × Nat)} (h1 : P2vKeepL B M0 M1 L1)
    (h2 : P2vKeepL B M1 M2 L2) : P2vKeepL B M0 M2 (L1 ++ L2) := fun e he hL =>
  (h2 e he fun p hp => hL p (List.mem_append_right _ hp)).trans (h1 e he fun p hp => hL p (List.mem_append_left _ hp))

theorem P2vKeepL.mono {B : Word} {M M' : Word → BitVec 8} {L L' : List (Nat × Nat)} (h : P2vKeepL B M M' L)
    (hs : ∀ p ∈ L, p ∈ L') : P2vKeepL B M M' L' := fun e he hL => h e he fun p hp => hL p (hs p hp)

theorem P2vKeep.toL {B : Word} {M M' : Word → BitVec 8} {c w : Nat} (h : P2vKeep B M M' c w) :
    P2vKeepL B M M' [(c, w)] := fun e he hL => h e he (hL _ (List.mem_singleton_self _))

theorem P2vKeepL.w32 {B : Word} {M M' : Word → BitVec 8} {L : List (Nat × Nat)} {e : Nat} (K : P2vKeepL B M M' L)
    (he : e + 4 ≤ 0x13F0) (h : ∀ p ∈ L, e + 4 ≤ p.1 ∨ p.1 + p.2 ≤ e) :
    memLoad32 M' (B + 0x21A0 + BitVec.ofNat 32 e) = memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 e) :=
  memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]; exact K _ (by omega) fun p hp => by have := h p hp; omega

theorem P2vKeepL.b8 {B : Word} {M M' : Word → BitVec 8} {L : List (Nat × Nat)} {e : Nat} (K : P2vKeepL B M M' L)
    (he : e + 1 ≤ 0x13F0) (h : ∀ p ∈ L, e + 1 ≤ p.1 ∨ p.1 + p.2 ≤ e) :
    M' (B + 0x21A0 + BitVec.ofNat 32 e) = M (B + 0x21A0 + BitVec.ofNat 32 e) :=
  K _ he fun p hp => by have := h p hp; omega

/-- A range of frame bytes that an `P2vKeepL` keeps. -/
theorem P2vKeepL.range {B : Word} {M M' : Word → BitVec 8} {L : List (Nat × Nat)} {s n : Nat} (K : P2vKeepL B M M' L)
    (hs : s + n ≤ 0x13F0) (h : ∀ p ∈ L, s + n ≤ p.1 ∨ p.1 + p.2 ≤ s) :
    ∀ j, j < n → M' (B + 0x21A0 + BitVec.ofNat 32 (s + j)) = M (B + 0x21A0 + BitVec.ofNat 32 (s + j)) :=
  fun j hj => K _ (by omega) fun p hp => by have := h p hp; omega

/-- The saved registers at the top of the frame. -/
def P2vSaves (B : Word) (M : Word → BitVec 8) (v : Nat → Word) : Prop :=
  ∀ k, k < 13 → memLoad32 M (B + BitVec.ofNat 32 (0x358C - 4 * k)) = v k

theorem P2vSaves.keepL {B : Word} {M M' : Word → BitVec 8} {v : Nat → Word} {L : List (Nat × Nat)}
    (V : P2vSaves B M v) (K : P2vKeepL B M M' L) (h : ∀ p ∈ L, p.1 + p.2 ≤ 0x13BC) : P2vSaves B M' v := fun k hk => by
  rw [← V k hk, show 0x358C - 4 * k = 0x21A0 + (0x13EC - 4 * k) by omega, p2v_base]
  exact K.w32 (by omega) fun p hp => by have := h p hp; omega

theorem br_beq_t {a b : Word} (h : a = b) : branchTaken .beq a b = true := by
  subst h; exact decide_eq_true rfl

theorem br_beq_f {a b : Word} (h : a ≠ b) : branchTaken .beq a b = false := by simp [branchTaken, h]

theorem br_bne_t {a b : Word} (h : a ≠ b) : branchTaken .bne a b = true := by simp [branchTaken, h]

theorem br_bne_f {a b : Word} (h : a = b) : branchTaken .bne a b = false := by simp [branchTaken, h]


/-- A callee frame `k` bytes below the frame's base. -/
theorem p2v_lo (B : Word) (k : Nat) (hk : k ≤ 0x21A0) :
    B + 0x21A0 + BitVec.ofNat 32 (2 ^ 32 - k) = B + BitVec.ofNat 32 (0x21A0 - k) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]; omega

/-- Bytes a step of `p256VerifyPrehash` doesn't write: outside the stack, or
the constants between `dataWindowAddress` and 0x3FCC4E60. -/
def P2vRo (B q : Word) (ql : Nat) : Prop :=
  P2vIn B q ql ∨ ((img% dataWindowAddress) ≤ q.toNat ∧ q.toNat + ql ≤ (img% dataWindowAddress + dataWindowSize))

theorem P2vRo.sep {B q : Word} {ql : Nat} (F : Fr B 0x3590) (h : P2vRo B q ql) {c n : Nat} (hc : c + n ≤ 0x3590) :
    Sep (B + BitVec.ofNat 32 c) n q ql := by
  rcases h with h | ⟨h1, h2⟩
  · exact (h.sepLo hc).symm
  · exact F.bufData hc h1 h2

theorem P2vRo.fit {B q : Word} {ql : Nat} (h : P2vRo B q ql) : q.toNat + ql < 2 ^ 32 := by
  rcases h with h | ⟨h1, h2⟩
  · exact h.fit
  · omega

theorem p2v_sp4 (B : Word) : B + 0x21A0 + 0xFFFFFFFC = B + BitVec.ofNat 32 0x219C := by
  rw [BitVec.add_assoc]; rfl


/-- The read-only region `ed25519_verify`'s constants live in lies outside
the frame's region. -/
def P2vRoSep (B : Word) : Prop := Sep (B + 0xFFFFFE60) 0x3730 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize)

theorem P2vKeepL.of {B : Word} {M M' : Word → BitVec 8} {c w : Nat} (K : P2vKeep B M M' c w) : P2vKeepL B M M' [(c, w)] :=
  fun e he hL => K e he (hL _ (List.mem_singleton_self _))

theorem P2vKeepL.same {B : Word} {M M' : Word → BitVec 8} (h : M' = M) : P2vKeepL B M M' [] :=
  fun _ _ _ => by rw [h]

set_option maxHeartbeats 8000000 in
/-- **A `memset` of `N` bytes** at offset `c` of the frame. -/
theorem p2v_msF {n : Machine} {B : Word} {off : Nat} {imm o v : Word} {c N : Nat}
    (F : Fr B 0x3590) (C : P2vCode n.mem) (s : St n.mem P2V n off (reg n))
    (h1 : fetchRel p256VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P2V + BitVec.ofNat 32 off + imm + o = MSET) (hev : (P2V + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 c) (ha1 : reg n a1 = v) (ha2 : reg n a2 = BitVec.ofNat 32 N)
    (hc : c + N ≤ 0x13F0) :
    ∃ n', Steps n n' ∧ St n'.mem P2V n' (off + 8) (reg n') ∧
      n'.mem = fillBytes n.mem (B + 0x21A0 + BitVec.ofNat 32 c) (v.extractLsb' 0 8) N ∧
      ∀ r, r ≠ a0 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ ra → reg n' r = reg n r := by
  have hFh := F.hi
  exact c_memset s C.self C.K h1 h2 hb hev ha0 ha1 ha2 (by rw [p2v_at F _ (by omega)]; omega)
    (by rw [← p2v_base']; exact F.sepHi (by omega) (by decide) (by decide))

theorem P2vIn.r {B p : Word} {len : Nat} (h : P2vIn B p len) {i : Nat} (hi : i < len) : P2vR B (p + BitVec.ofNat 32 i) :=
  (h.sep.sub (c := i) (l := 1) (by omega)).symm

theorem P2vIn.r0 {B p : Word} {len : Nat} (h : P2vIn B p len) (hn : 0 < len) : P2vR B p := by
  have := h.r hn; rwa [show p + BitVec.ofNat 32 0 = p from BitVec.add_zero p] at this

/-- Proves that two sums of a base address and constants are equal. -/
macro "p2v_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq
             simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]
               <;> omega))

theorem p2v_at {B : Word} (F : Fr B 0x3590) (c : Nat) (hc : c ≤ 0x13F0) :
    (B + 0x21A0 + BitVec.ofNat 32 c).toNat = B.toNat + 0x21A0 + c := by
  have := F.at (0x21A0 + c) (by omega); rw [← add_ofNat_assoc] at this; exact this.trans (by omega)

theorem p2v_al {B : Word} (F : Fr B 0x3590) {c : Nat} (hc : c ≤ 0x13F0) (ac : c % 4 = 0) :
    (B + 0x21A0 + BitVec.ofNat 32 c).toNat % 4 = 0 := by
  have := F.al; rw [p2v_at F c hc]; omega

theorem p2v_base (B : Word) (c : Nat) : B + BitVec.ofNat 32 (0x21A0 + c) = B + 0x21A0 + BitVec.ofNat 32 c :=
  (add_ofNat_assoc B 0x21A0 c).symm

/-- A byte outside the stack is outside every part of the frame. -/
theorem p2vR_hi {B x : Word} {c l : Nat} (hx : P2vR B x) (h : c + l ≤ 0x13F0) :
    Sep (B + 0x21A0 + BitVec.ofNat 32 c) l x 1 := by
  have := hx.sub (c := 0x1A0 + 0x21A0 + c) (l := l) (by omega)
  rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + 0x21A0 + c) = B + 0x21A0 + BitVec.ofNat 32 c by
    rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl, show (0x21A0 : Word).toNat = 0x21A0 from rfl]
    omega] at this

/-- A byte outside the stack is outside the `k` bytes below the frame. -/
theorem p2vR_lo {B x : Word} {k : Nat} (hx : P2vR B x) (hk : k ≤ 0x2340) (hk0 : 0 < k) :
    Sep (B + 0x21A0 + BitVec.ofNat 32 (2 ^ 32 - k)) k x 1 := by
  have := hx.sub (c := 0x1A0 + 0x21A0 - k) (l := k) (by omega)
  rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + 0x21A0 - k) = B + 0x21A0 + BitVec.ofNat 32 (2 ^ 32 - k) by
    rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl, show (0x21A0 : Word).toNat = 0x21A0 from rfl]
    omega] at this

theorem P2vSaves.keep {B : Word} {M M' : Word → BitVec 8} {v : Nat → Word} {c w : Nat} (V : P2vSaves B M v)
    (K : P2vKeep B M M' c w) (h : c + w ≤ 0x13BC) : P2vSaves B M' v := fun k hk => by
  rw [← V k hk, show 0x358C - 4 * k = 0x21A0 + (0x13EC - 4 * k) by omega, p2v_base]
  exact memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]; exact K _ (by omega) (by omega)

theorem P2vSaves.same {B : Word} {M M' : Word → BitVec 8} {v : Nat → Word} (V : P2vSaves B M v) (h : M' = M) :
    P2vSaves B M' v := by rw [h]; exact V

theorem P2vKeep.w32 {B : Word} {M M' : Word → BitVec 8} {c w e : Nat} (K : P2vKeep B M M' c w) (he : e + 4 ≤ 0x13F0)
    (h : e + 4 ≤ c ∨ c + w ≤ e) :
    memLoad32 M' (B + 0x21A0 + BitVec.ofNat 32 e) = memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 e) :=
  memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact K _ (by omega) (by omega)

theorem P2vKeep.b8 {B : Word} {M M' : Word → BitVec 8} {c w e : Nat} (K : P2vKeep B M M' c w) (he : e + 1 ≤ 0x13F0)
    (h : e + 1 ≤ c ∨ c + w ≤ e) : M' (B + 0x21A0 + BitVec.ofNat 32 e) = M (B + 0x21A0 + BitVec.ofNat 32 e) :=
  K _ he (by omega)

/-- A range of frame bytes that an `P2vKeep` keeps. -/
theorem P2vKeep.range {B : Word} {M M' : Word → BitVec 8} {c w s n : Nat} (K : P2vKeep B M M' c w)
    (hs : s + n ≤ 0x13F0) (h : s + n ≤ c ∨ c + w ≤ s) :
    ∀ j, j < n → M' (B + 0x21A0 + BitVec.ofNat 32 (s + j)) = M (B + 0x21A0 + BitVec.ofNat 32 (s + j)) :=
  fun j hj => K _ (by omega) (by omega)

theorem P2vKeep.same {B : Word} {M M' : Word → BitVec 8} (h : M' = M) : P2vKeep B M M' 0 0 :=
  fun _ _ _ => by rw [h]

theorem ld_cp {M M' : Word → BitVec 8} {S : Word} {c d : Nat}
    (h : ∀ q, q < 4 → M' (S + BitVec.ofNat 32 (c + q)) = M (S + BitVec.ofNat 32 (d + q))) :
    memLoad32 M' (S + BitVec.ofNat 32 c) = memLoad32 M (S + BitVec.ofNat 32 d) :=
  by
  rw [ld_ofNat, ld_ofNat]
  simp only [add_ofNat_assoc]
  rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

/-- The low byte of a byte read with `lbu`. -/
theorem lbu_low (b : BitVec 8) : (b.zeroExtend 32).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]; omega

/-- The machine, after a step of `p256VerifyPrehash`: what the frame and the
code are, and the saved registers. -/
structure P2vPost (B : Word) (m m' : Machine) (off' : Nat) : Prop where
  steps : Steps m m'
  st : St m'.mem P2V m' off' (reg m')
  fr : ∀ x, P2vR B x → m'.mem x = m.mem x
  regs : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q

theorem P2vCode.fr {B : Word} {M M' : Word → BitVec 8} (C : P2vCode M) (F : Fr B 0x3590)
    (h : ∀ x, P2vR B x → M' x = M x) : P2vCode M' :=
  C.hi fun x hx => h x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))

set_option maxHeartbeats 4000000 in
/-- `sw` to the word at offset `c` of the frame. -/
theorem p2v_sw {B : Word} {m : Machine} {off off' : Nat} {rs1 rs2 : Fin 32} {o len : Word} {c : Nat}
    (F : Fr B 0x3590) (E : P2vCode m.mem) (s : St m.mem P2V m off (reg m))
    (hf : fetchRel p256VerifyPrehashCode off = some (.store .sw rs1 rs2 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (ha : reg m rs1 + o = B + 0x21A0 + BitVec.ofNat 32 c)
    (hc : c + 4 ≤ 0x13F0) (ac : c % 4 = 0) :
    ∃ m', Steps m m' ∧ St m'.mem P2V m' off' (reg m') ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧
      P2vKeep B m.mem m'.mem c 4 ∧ memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 c) = reg m rs2 ∧
      ∀ q, reg m' q = reg m q := by
  obtain ⟨m1, d1, u1⟩ := s.sw E.self hf hn (by rw [ha]; exact p2v_al F (by omega) ac)
  rw [ha] at u1
  exact ⟨m1, .single d1, ⟨u1.pc, rfl, fun _ => rfl⟩, fun x hx => by rw [u1.mem]; exact memStore32_get_sep (p2vR_hi hx hc),
    fun e he1 he2 => by
      rw [u1.mem]; exact memStore32_get_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega)),
    by rw [u1.mem, memLoad32_store32_same], fun q => u1.regs q⟩

set_option maxHeartbeats 4000000 in
/-- `sb` to the byte at offset `c` of the frame. -/
theorem p2v_sb {B : Word} {m : Machine} {off off' : Nat} {rs1 rs2 : Fin 32} {o len : Word} {c : Nat}
    (_F : Fr B 0x3590) (E : P2vCode m.mem) (s : St m.mem P2V m off (reg m))
    (hf : fetchRel p256VerifyPrehashCode off = some (.store .sb rs1 rs2 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (ha : reg m rs1 + o = B + 0x21A0 + BitVec.ofNat 32 c)
    (hc : c + 1 ≤ 0x13F0) :
    ∃ m', Steps m m' ∧ St m'.mem P2V m' off' (reg m') ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧
      P2vKeep B m.mem m'.mem c 1 ∧ m'.mem (B + 0x21A0 + BitVec.ofNat 32 c) = (reg m rs2).extractLsb' 0 8 ∧
      ∀ q, reg m' q = reg m q := by
  obtain ⟨m1, d1, u1⟩ := s.sb E.self hf hn
  rw [ha] at u1
  exact ⟨m1, .single d1, ⟨u1.pc, rfl, fun _ => rfl⟩,
    fun x hx => by rw [u1.mem]; exact memStore8_ne (sep1_ne (p2vR_hi (l := 1) hx hc)),
    fun e he1 he2 => by
      rw [u1.mem]; exact memStore8_ne (sep1_ne (sepS (B + 0x21A0) (by omega) (by omega) (by omega))),
    by rw [u1.mem, memStore8_same], fun q => u1.regs q⟩

set_option maxHeartbeats 4000000 in
/-- A call to `memcpy` of `N` bytes from offset `d` of the frame to offset `c`. -/
theorem p2v_mc {B : Word} {m : Machine} {off : Nat} {imm o : Word} {c d N : Nat} (F : Fr B 0x3590)
    (E : P2vCode m.mem) (s : St m.mem P2V m off (reg m))
    (h1 : fetchRel p256VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P2V + BitVec.ofNat 32 off + imm + o = MCS) (he8 : (P2V + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x21A0) (ha0 : reg m a0 = B + 0x21A0 + BitVec.ofNat 32 c)
    (ha1 : reg m a1 = B + 0x21A0 + BitVec.ofNat 32 d) (ha2 : reg m a2 = BitVec.ofNat 32 N)
    (hc : c + N ≤ 0x13F0) (hd : d + N ≤ 0x13F0) (hs : c + N ≤ d ∨ d + N ≤ c) :
    ∃ m', P2vPost B m m' (off + 8) ∧ P2vKeep B m.mem m'.mem c N ∧
      ∀ j, j < N → m'.mem (B + 0x21A0 + BitVec.ofNat 32 (c + j)) = m.mem (B + 0x21A0 + BitVec.ofNat 32 (d + j)) := by
  have FS : Fr (B + 0x21A0) 0x13F0 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hb16 : (B + 0x21A0 + 0xFFFFFFF0).toNat = (B + 0x21A0).toNat - 16 := FS.below 16 (by decide) (by decide)
  have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨fA, fW, hFC⟩ := FS.mc
  obtain ⟨n2, c2, u2, fr2, k2⟩ := c_memcpy (dst := B + 0x21A0 + BitVec.ofNat 32 c)
    (src := B + 0x21A0 + BitVec.ofNat 32 d) (S := B + 0x21A0) (N := N) s E.self E.K h1 h2 hb he8 hsp ha0 ha1 ha2
    ⟨E.K.body, FS.sepHi (by omega) (by decide) (by decide), hFC, FS.mcN (by omega), FS.mcN (by omega),
      sepS (B + 0x21A0) hs (by omega) (by omega), fA, fW, by rw [FS.at _ (by omega)]; omega,
      by rw [FS.at _ (by omega)]; omega⟩
  have lo16 : ∀ x, P2vR B x → Sep (B + 0x21A0 + 0xFFFFFFF0) 16 x 1 := fun x hx => p2vR_lo (k := 16) hx (by decide) (by decide)
  refine ⟨n2, ⟨c2, u2, fun x hx => ?_, fun q hq => ?_⟩, fun e he1 he2 => ?_, fun j hj => ?_⟩
  · rw [fr2 x (lo16 x hx), copyBytes_sep (p2vR_hi (c := c) (l := N) hx hc) (Nat.le_refl _)]
  · exact k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  · rw [fr2 _ (FS.lowB hb16 (by decide) (by omega)),
      copyBytes_sep (sepS (B + 0x21A0) (c := c) (n := N) (d := e) (k := 1) (by omega) (by omega) (by omega))
        (Nat.le_refl _)]
  · rw [fr2 _ (FS.lowB hb16 (by decide) (by omega)), ← add_ofNat_assoc (B + 0x21A0) c j, cp_at hj (by omega),
      add_ofNat_assoc]

/-- Bytes `p256VerifyPrehash` reads outside the stack: the bundle's, or the
image's read-only constants. -/
def P2vRo2 (B q : Word) (ql : Nat) : Prop :=
  P2vIn B q ql ∨ ((img% roWindowAddress) ≤ q.toNat ∧ q.toNat + ql ≤ 0x3FCC5400)

theorem roSep {B b : Word} {len c n : Nat} (RS : P2vRoSep B) (h : c + n ≤ 0x3590) (hb : (img% roWindowAddress) ≤ b.toNat)
    (hb2 : b.toNat + len ≤ 0x3FCC5400) : Sep (B + BitVec.ofNat 32 c) n b len := by
  have h1 := RS.sub (c := 0x1A0 + c) (l := n) (by omega)
  have h2 := h1.subR (c := b.toNat - (img% roWindowAddress)) (l := len) (by omega)
  rw [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
    omega] at h2
  rwa [show BitVec.ofNat 32 (img% roWindowAddress) + BitVec.ofNat 32 (b.toNat - (img% roWindowAddress)) = b by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := b.isLt; omega] at h2

theorem P2vRo2.sepLo {B q : Word} {ql : Nat} (RS : P2vRoSep B) (h : P2vRo2 B q ql) {c n : Nat} (hc : c + n ≤ 0x3590) :
    Sep q ql (B + BitVec.ofNat 32 c) n := by
  rcases h with h | ⟨h1, h2⟩
  · exact h.sepLo hc
  · exact (roSep RS hc h1 h2).symm

theorem P2vRo2.lo {B q : Word} {ql : Nat} (h : P2vRo2 B q ql) : q.toNat + ql ≤ 0x40000000 := by
  rcases h with h | ⟨_, h2⟩
  · have := h.lo; omega
  · omega

theorem P2vRo2.r {B q : Word} {ql i : Nat} (RS : P2vRoSep B) (h : P2vRo2 B q ql) (hi : i < ql) :
    P2vR B (q + BitVec.ofNat 32 i) := by
  rcases h with h | ⟨h1, h2⟩
  · exact h.r hi
  · have := RS.subR (c := q.toNat - (img% roWindowAddress) + i) (l := 1) (by omega)
    rwa [show BitVec.ofNat 32 (img% roWindowAddress) + BitVec.ofNat 32 (q.toNat - (img% roWindowAddress) + i) = q + BitVec.ofNat 32 i by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have := q.isLt; omega] at this

theorem p2v_mcRo2 {B : Word} {m : Machine} {off : Nat} {imm o p : Word} {c N : Nat} (F : Fr B 0x3590)
    (RS : P2vRoSep B) (E : P2vCode m.mem) (s : St m.mem P2V m off (reg m))
    (h1 : fetchRel p256VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P2V + BitVec.ofNat 32 off + imm + o = MCS) (he8 : (P2V + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x21A0) (ha0 : reg m a0 = B + 0x21A0 + BitVec.ofNat 32 c)
    (ha1 : reg m a1 = p) (ha2 : reg m a2 = BitVec.ofNat 32 N) (hc : c + N ≤ 0x13F0) (hin : P2vRo2 B p N) :
    ∃ m', P2vPost B m m' (off + 8) ∧ P2vKeep B m.mem m'.mem c N ∧
      ∀ j, j < N → m'.mem (B + 0x21A0 + BitVec.ofNat 32 (c + j)) = m.mem (p + BitVec.ofNat 32 j) := by
  have FS : Fr (B + 0x21A0) 0x13F0 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hb16 : (B + 0x21A0 + 0xFFFFFFF0).toNat = (B + 0x21A0).toNat - 16 := FS.below 16 (by decide) (by decide)
  have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨fA, fW, hFC⟩ := FS.mc
  obtain ⟨n2, c2, u2, fr2, k2⟩ := c_memcpy (dst := B + 0x21A0 + BitVec.ofNat 32 c) (src := p) (S := B + 0x21A0)
    (N := N) s E.self E.K h1 h2 hb he8 hsp ha0 ha1 ha2
    ⟨E.K.body, FS.sepHi (by omega) (by decide) (by decide), hFC, FS.mcN (by omega),
      by rw [p2v_sp10]; exact hin.sepLo RS (by decide),
      by rw [← p2v_base']; exact (hin.sepLo RS (by omega)).symm, fA, fW,
      by rw [FS.at _ (by omega)]; omega, by have := hin.lo; omega⟩
  have lo16 : ∀ x, P2vR B x → Sep (B + 0x21A0 + 0xFFFFFFF0) 16 x 1 := fun x hx => p2vR_lo (k := 16) hx (by decide) (by decide)
  refine ⟨n2, ⟨c2, u2, fun x hx => ?_, fun q hq => ?_⟩, fun e he1 he2 => ?_, fun j hj => ?_⟩
  · rw [fr2 x (lo16 x hx), copyBytes_sep (p2vR_hi (c := c) (l := N) hx hc) (Nat.le_refl _)]
  · exact k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  · rw [fr2 _ (FS.lowB hb16 (by decide) (by omega)),
      copyBytes_sep (sepS (B + 0x21A0) (c := c) (n := N) (d := e) (k := 1) (by omega) (by omega) (by omega))
        (Nat.le_refl _)]
  · rw [← add_ofNat_assoc, fr2 _ (by rw [add_ofNat_assoc]; exact FS.lowB hb16 (by decide) (by omega)),
      C3.RV32.Dq.cp_at hj (by omega)]

theorem p2v_spX (B : Word) (k : Nat) (hk : k ≤ 0x21A0) :
    B + 0x21A0 + BitVec.ofNat 32 (2 ^ 32 - k) = B + BitVec.ofNat 32 (0x21A0 - k) := p2v_lo B k hk

theorem p2vR_spX {B x : Word} {k : Nat} (hx : P2vR B x) (hk : k ≤ 0x2340) (hk0 : 0 < k) (hk' : k ≤ 0x21A0) :
    Sep (B + BitVec.ofNat 32 (0x21A0 - k)) k x 1 := by
  have := p2vR_lo (k := k) hx hk hk0
  rwa [p2v_lo B k hk'] at this

/-- The first 32 bytes of `L`, each cut to a byte. -/
def b32 (L : Bytes) : Bytes := (List.range 32).map fun j => (BitVec.ofNat 8 (L.getD j 0)).toNat

/-- 32 bytes of the frame that hold the first 32 bytes of `L`. -/
theorem join32 {M : Word → BitVec 8} {B : Word} {L : Bytes} {c : Nat}
    (h0 : M (B + 0x21A0 + BitVec.ofNat 32 c) = BitVec.ofNat 8 (L.getD 0 0))
    (h1 : ∀ j, j < 31 → M (B + 0x21A0 + BitVec.ofNat 32 (c + 1 + j)) = BitVec.ofNat 8 (L.getD (1 + j) 0)) :
    memBytes M (B + 0x21A0 + BitVec.ofNat 32 c) 32 = b32 L := by
  unfold memBytes b32
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [add_ofNat_assoc]
  rcases j with _ | j
  · rw [Nat.add_zero, h0]
  · have := h1 j (by omega)
    rw [show c + 1 + j = c + (j + 1) by omega, show 1 + j = j + 1 by omega] at this
    rw [this]


theorem p2v_sp10 (B : Word) : B + 0x21A0 + 0xFFFFFFF0 = B + BitVec.ofNat 32 0x2190 := by
  rw [BitVec.add_assoc]; rfl

theorem P2vRo.lo {B q : Word} {ql : Nat} (h : P2vRo B q ql) : q.toNat + ql ≤ 0x40000000 := by
  rcases h with h | ⟨_, h2⟩
  · have := h.lo; omega
  · omega

theorem p2vR_sp4 {B x : Word} (hx : P2vR B x) : Sep (B + BitVec.ofNat 32 0x219C) 4 x 1 := by
  have := p2vR_lo (k := 4) hx (by decide) (by decide)
  rwa [p2v_lo B 4 (by decide)] at this

/-- **A failing check** that jumps to 0x142, where `a0` becomes 0. -/
theorem p2v_fail {B : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x3590) (E : P2vCode n.mem)
    (s : St n.mem P2V n 0x142 (reg n)) (t : Steps n0 n) (fR : ∀ x, P2vR B x → n.mem x = n0.mem x)
    (V : P2vSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32)) (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) :
    P2vRet B v n0 0 :=
  p2v_false F E.self s t fR V hret rsp r3 r4

/-- **A failing check** that jumps to the epilogue at 0x144 with 0 in `a0`. -/
theorem p2v_fail0 {B : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x3590) (E : P2vCode n.mem)
    (s : St n.mem P2V n 0x144 (reg n)) (t : Steps n0 n) (fR : ∀ x, P2vR B x → n.mem x = n0.mem x)
    (V : P2vSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32)) (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32))
    (ha0 : reg n a0 = 0) : P2vRet B v n0 0 := by
  have e := p2v_retR F E.self s t fR V hret rsp r3 r4
  rwa [ha0] at e

end C3.RV32.P2v
