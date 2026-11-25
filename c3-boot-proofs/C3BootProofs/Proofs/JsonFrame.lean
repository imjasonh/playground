import C3BootProofs.Proofs.JsonWp

/-!
# Stack frames for the JSON proofs

A JSON function that calls another keeps a frame below `sp`. Its theorem
names a stack region `[s, s + k)` that holds its frame and every frame its
callees push, and says the function changed no memory outside that region
and the result at `out`. `Out M M' s k` is that agreement, and `Slots`
tracks the saved registers in the frame across calls and stores.

Each function with a frame keeps every register outside `jClob`, the
caller-saved `a0`–`a7` and `t0`–`t6`, as the RISC-V calling convention
requires.
-/

namespace C3.RV32

/-- The registers a JSON function may change: `a0`–`a7` and `t0`–`t6`. -/
abbrev jClob : List (Fin 32) := [10, 11, 12, 13, 14, 15, 16, 17, 5, 6, 7, 28, 29, 30, 31]

/-- `M'` agrees with `M` outside the `k` bytes at `s`. -/
def Out (M M' : Word → BitVec 8) (s : Word) (k : Nat) : Prop := ∀ x, Sep x 1 s k → M' x = M x

section
variable {M M1 M2 M' : Word → BitVec 8} {s a p b : Word} {k l n d : Nat}

theorem Out.refl (M : Word → BitVec 8) (s : Word) (k : Nat) : Out M M s k := fun _ _ => rfl

theorem Out.trans (h1 : Out M M1 s k) (h2 : Out M1 M2 s k) : Out M M2 s k :=
  fun x hx => (h2 x hx).trans (h1 x hx)

theorem sep_pt {i : Nat} (h : Sep b k a n) (hi : i < n) : Sep (a + BitVec.ofNat 32 i) 1 b k :=
  h.symm.shift hi

theorem sep_in {x : Word} (h : Sep x n s k) (hd : d + l ≤ k) : Sep x n (s + BitVec.ofNat 32 d) l :=
  (h.symm.sub hd).symm

theorem Out.widen (h : Out M M' (s + BitVec.ofNat 32 d) l) (hd : d + l ≤ k) : Out M M' s k :=
  fun x hx => h x (sep_in hx hd)

theorem Out.codeIn {code : List Nat} (h : Out M M' s k) (hc : CodeIn M b code) (hs : Sep s k b code.length) :
    CodeIn M' b code :=
  fun i hi => by rw [h _ (sep_pt hs hi)]; exact hc i hi

theorem Out.bytes (h : Out M M' s k) (hs : Sep s k p n) : memBytes M' p n = memBytes M p n :=
  memBytes_congr fun _ hi => h _ (sep_pt hs hi)

theorem Out.byte {i : Nat} (h : Out M M' s k) (hs : Sep s k p n) (hi : i < n) :
    M' (p + BitVec.ofNat 32 i) = M (p + BitVec.ofNat 32 i) :=
  h _ (sep_pt hs hi)

theorem Out.load32 (h : Out M M' s k) (hs : Sep s k a 4) : memLoad32 M' a = memLoad32 M a :=
  memLoad32_congr fun _ hj => h _ (sep_pt hs hj)

theorem out_store32 (M : Word → BitVec 8) (a v : Word) : Out M (memStore32 M a v) a 4 :=
  fun _ hx => memStore32_get_sep hx.symm

theorem out_store8 (M : Word → BitVec 8) (a : Word) (v : BitVec 8) : Out M (memStore8 M a v) a 1 :=
  fun _ hx => memStore8_ne (sep_byte0 hx (by decide))

theorem UsizeRes.out {r : Option Nat} (h : UsizeRes M M' a r) : Out M M' a 8 := by
  cases r
  · exact h.1
  · exact h.1

/-- The words at offsets `cs` from `s` read the same in `M` as in `M1`. -/
def Slots (cs : List Nat) (s : Word) (M1 M : Word → BitVec 8) : Prop :=
  ∀ c, c ∈ cs → memLoad32 M (s + BitVec.ofNat 32 c) = memLoad32 M1 (s + BitVec.ofNat 32 c)

theorem Slots.refl (cs : List Nat) (s : Word) (M : Word → BitVec 8) : Slots cs s M M := fun _ _ => rfl

theorem Slots.out {cs : List Nat} (h : Slots cs s M1 M) (ho : Out M M' a l)
    (hs : ∀ c, c ∈ cs → Sep a l (s + BitVec.ofNat 32 c) 4) : Slots cs s M1 M' :=
  fun c hc => (ho.load32 (hs c hc)).trans (h c hc)

/-- Ranges at offsets from `s` that avoid each slot. -/
theorem slots_sep {cs : List Nat} (s : Word) (h : ∀ c, c ∈ cs → (c + 4 ≤ d ∨ d + l ≤ c) ∧ c + 4 ≤ 2 ^ 32)
    (hd : d + l ≤ 2 ^ 32) : ∀ c, c ∈ cs → Sep (s + BitVec.ofNat 32 d) l (s + BitVec.ofNat 32 c) 4 :=
  fun c hc => sep_offsets s (h c hc).1.symm hd (h c hc).2

/-- A range apart from the region is apart from each slot in it. -/
theorem slots_sep_out {cs : List Nat} (hs : Sep a l s k) (h : ∀ c, c ∈ cs → c + 4 ≤ k) :
    ∀ c, c ∈ cs → Sep a l (s + BitVec.ofNat 32 c) 4 :=
  fun c hc => sep_in hs (h c hc)

/-- `out` holds `r` as a `Result<usize, TufError>`, and no memory changed
outside `out` and the `k` bytes at `s`. -/
def UsizeResF (M M' : Word → BitVec 8) (out s : Word) (k : Nat) (r : Option Nat) : Prop :=
  ∃ M1, Out M M1 s k ∧ UsizeRes M1 M' out r

theorem UsizeResF.get {out x : Word} {r : Option Nat} (h : UsizeResF M M' out s k r) (hx : Sep x 1 s k)
    (ho : Sep x 1 out 8) : M' x = M x := by
  obtain ⟨M1, h1, h2⟩ := h
  rw [h2.out x ho, h1 x hx]

/-- A function with stack region `[s, s + k)` returned to `ret` with `r` at
`out`, and kept every register outside `jClob`. -/
def FPost (ret : Word) (M : Word → BitVec 8) (out s : Word) (k : Nat) (r : Option Nat)
    (g0 : Fin 32 → Word) : Post :=
  fun pc M' g => pc = ret ∧ UsizeResF M M' out s k r ∧ ∀ x, x ∉ jClob → g x = g0 x

end

theorem keepUpd0 {f g0 : Fin 32 → Word} {cl : List (Fin 32)} {rd : Fin 32} {v : Word} (hz : g0 0 = 0)
    (hrd : rd ∈ cl) (hfr : ∀ x, x ∉ cl → f x = g0 x) : ∀ x, x ∉ cl → upd f rd v x = g0 x := by
  intro x hx
  have hne : x ≠ rd := fun e => hx (by rw [e]; exact hrd)
  by_cases h0 : x.val = 0
  · rw [show x = 0 from Fin.ext h0, hz]; rfl
  · simp only [upd_app, h0, hne, ↓reduceIte]; exact hfr x hx

theorem keepClob {G g0 : Fin 32 → Word} {m : Machine} {cl L : List (Fin 32)} (hsub : ∀ x, x ∈ cl → x ∈ L)
    (hG : ∀ x, x ∉ L → G x = g0 x) : ∀ x, x ∉ L → clob G m cl x = g0 x := by
  intro x hx
  have hn : x ∉ cl := fun h => hx (hsub x h)
  simp only [clob_app, hn, ↓reduceIte]; exact hG x hx

/-- Proves `∀ x, x ∉ L → g x = g0 x` for `g` a chain of `upd`s and `clob`s
over registers that keep `g0` outside `L`, given `hz : g0 0 = 0`. -/
syntax "keepz" term : tactic

macro_rules
  | `(tactic| keepz $hz) =>
    `(tactic| ((repeat (first | refine keepUpd0 $hz (by decide) ?_ | refine keepClob (by decide) ?_)); try first | assumption | exact fun _ _ => rfl))

theorem ev_mv {f : Fin 32 → Word} (hz : f 0 = 0) (x : Word) : aluEval .add (f 0) x = x := by
  rw [hz, ev_add]; exact BitVec.zero_add x

theorem ev0 (x : Word) : aluEval .add 0 x = x := BitVec.zero_add x

theorem nbeq_true {a b : Nat} (h : (!(a == b)) = true) : a ≠ b := fun e => by
  subst e; have : (a == a) = true := decide_eq_true rfl
  rw [this] at h; exact absurd h (by decide)

theorem nbeq_false {a b : Nat} (h : (!(a == b)) = false) : a = b := by
  cases hb : a == b
  · rw [hb] at h; exact absurd h (by decide)
  · exact beq_iff_eq.mp hb

theorem ld_skip {M : Word → BitVec 8} {s v w : Word} (c d : Nat) (h : c + 4 ≤ d ∨ d + 4 ≤ c)
    (hc : c + 4 ≤ 2 ^ 32) (hd : d + 4 ≤ 2 ^ 32) (k : memLoad32 M (s + BitVec.ofNat 32 c) = w) :
    memLoad32 (memStore32 M (s + BitVec.ofNat 32 d) v) (s + BitVec.ofNat 32 c) = w :=
  (memLoad32_store32_sep (sep_offsets s h.symm hd hc)).trans k

/-- Every register in `L2` keeps its value, and every register outside
`L1 ++ L2` does. -/
theorem frame_of {g g0 : Fin 32 → Word} {L1 L2 : List (Fin 32)} (hK : ∀ x, x ∉ L1 ++ L2 → g x = g0 x)
    (hL2 : ∀ x, x ∈ L2 → g x = g0 x) : ∀ x, x ∉ L1 → g x = g0 x := by
  intro x hx
  by_cases h : x ∈ L2
  · exact hL2 x h
  · exact hK x fun hm => (List.mem_append.mp hm).elim hx h

theorem add_lit_assoc (s : Word) (a b : Nat) :
    s + BitVec.ofNat 32 a + BitVec.ofNat 32 b = s + BitVec.ofNat 32 (a + b) := add_ofNat_assoc s a b

theorem lit_ofNat (n : Nat) : (OfNat.ofNat n : Word) = BitVec.ofNat 32 n := rfl

end C3.RV32
