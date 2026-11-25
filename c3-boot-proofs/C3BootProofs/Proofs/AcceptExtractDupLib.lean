import C3BootProofs.Proofs.AcceptExtractHead
import C3BootProofs.Proofs.TufRoleKeysMetDup
import C3BootProofs.Proofs.SmallFns

/-!
# Tools for the extract stage's no-duplicates checks

From 0x1434 to 0x1778 the closure checks six lists for duplicates. Each
check is two nested loops over one of the fixed arrays: an enumerator at
`sp + 0x244` walks the entries, and for entry `i` an iterator at
`sp + 0x1320` walks the entries after it and compares each with entry `i`.

`acedp_distinct_iff` says that such a loop finding no pair of equal entries
is `distinct` of the list. The checks write only the enumerator, the
iterator, and their callees' frames below `sp` (`AcedpW`), and keep the
registers of `AcedpR`. `acedp_callEnum` and `acedp_callNth` are the calls of the
enumerator's `next` and the iterator's `nth`, and `acedp_f1774` is the way
into the exit at 0x7D6 when a check finds a duplicate.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

/-! ## `distinct` as a nested loop -/

theorem acedp_distinct : ∀ xs : List Bytes,
    (∀ i k, i < k → k < xs.length → xs[k]? ≠ xs[i]?) → distinct xs = true
  | [], _ => rfl
  | x :: xs, h => by
    show (!xs.contains x && distinct xs) = true
    rw [Bool.and_eq_true]
    refine ⟨?_, acedp_distinct xs fun i k hik hk => h (i + 1) (k + 1) (by omega)
      (by rw [List.length_cons]; omega)⟩
    cases hc : xs.contains x
    · rfl
    · exfalso
      obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp (List.contains_iff_mem.mp hc)
      have hl : n < xs.length := (List.getElem?_eq_some_iff.mp hn).1
      exact h 0 (n + 1) (by omega) (by rw [List.length_cons]; omega)
        (by rw [List.getElem?_cons_succ, hn, List.getElem?_cons_zero])

theorem acedp_pairwise : ∀ xs : List Bytes, distinct xs = true →
    ∀ i k, i < k → k < xs.length → xs[k]? ≠ xs[i]?
  | [], _, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | x :: xs, h, i, k, hik, hk => by
    have h' : (!xs.contains x && distinct xs) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨hx, hd⟩ := h'
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [List.getElem?_cons_succ]
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero]
      intro e
      have hm : x ∈ xs := List.mem_iff_getElem?.mpr ⟨k', e⟩
      rw [List.contains_iff_mem.mpr hm] at hx
      exact absurd hx (by decide)
    | succ i =>
      rw [List.getElem?_cons_succ]
      exact acedp_pairwise xs hd i k' (by omega) (by rw [List.length_cons] at hk; omega)

/-- A list is `distinct` exactly when no entry equals an earlier one: what
a loop over `i` with an inner loop over the `k > i` checks. -/
theorem acedp_distinct_iff (xs : List Bytes) :
    distinct xs = true ↔ ∀ i k, i < k → k < xs.length → xs[k]? ≠ xs[i]? :=
  ⟨acedp_pairwise xs, acedp_distinct xs⟩

/-! ## The arrays -/

/-- Entry `i` of the array at `sp + a`. -/
def acedpE (B : Word) (a i : Nat) : Word := acSlot B (a + 0x20 * i)

theorem acedpE_succ (B : Word) (a i : Nat) : acedpE B a i + 0x20 = acedpE B a (i + 1) := by
  unfold acedpE acSlot
  rw [show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, add_ofNat_assoc,
    show 0x3A50 + (a + 0x20 * i) + 0x20 = 0x3A50 + (a + 0x20 * (i + 1)) by omega]

theorem acedpE_add (B : Word) (a i k : Nat) :
    acedpE B a i + BitVec.ofNat 32 k = acSlot B (a + 0x20 * i + k) := by
  unfold acedpE acSlot
  rw [add_ofNat_assoc, Nat.add_assoc 0x3A50]

theorem acedpE_zero (B : Word) (a : Nat) : acedpE B a 0 = acSlot B a := rfl

theorem acedpE_cap (B : Word) (a cap : Nat) : acedpE B a cap = acedpE B a 0 + BitVec.ofNat 32 (32 * cap) := by
  rw [acedpE_add]; unfold acedpE; rw [Nat.mul_zero, Nat.add_zero, Nat.mul_comm 32 cap]

section
variable {B : Word} (F : Fr B 0x5A70)
include F

theorem acedpE_toNat {a i : Nat} (h : a + 0x20 * i ≤ 0x2020) :
    (acedpE B a i).toNat = B.toNat + 0x3A50 + a + 0x20 * i := by
  unfold acedpE; rw [ace_slotN F (by omega)]; omega

omit F in
theorem acedpE_ne {a i j : Nat} (hi : a + 0x20 * i ≤ 0x2020) (hj : a + 0x20 * j ≤ 0x2020) (h : i ≠ j) :
    acedpE B a i ≠ acedpE B a j :=
  add_ofNat_ne B (by omega) (by omega) (by omega)

theorem acedpE_nz {a i : Nat} (h : a + 0x20 * i ≤ 0x2020) : acedpE B a i ≠ 0 := by
  intro e
  have h1 := acedpE_toNat F h
  rw [e] at h1
  have h0 : (0 : Word).toNat = 0 := rfl
  have := F.lo
  omega

theorem acedpE_al {a i : Nat} (ha : a % 4 = 0) (h : a + 0x20 * i ≤ 0x2020) : (acedpE B a i).toNat % 4 = 0 := by
  rw [acedpE_toNat F h]; have := F.al; omega

end

/-- The array of `cap` entries at `sp + a`, `len` of them listed: each listed
entry's first word is not zero, and each later one's is. The array lies
between the enumerator and the iterator, or above the iterator. -/
structure AcedpArr (X : AceCtx) (N : Word → BitVec 8) (a cap len : Nat) : Prop where
  al : a % 4 = 0
  pos : (0x250 ≤ a ∧ a + 0x20 * cap + 4 ≤ 0x1320) ∨ (0x132C ≤ a ∧ a + 0x20 * cap + 4 ≤ 0x2020)
  hcap : cap ≤ 16
  hlen : len ≤ cap
  tag : ∀ i, i < len → memLoad32 N (acedpE X.B a i) ≠ 0
  zero : ∀ i, len ≤ i → i < cap → memLoad32 N (acedpE X.B a i) = 0

theorem AcedpArr.hi {X : AceCtx} {N : Word → BitVec 8} {a cap len : Nat} (A : AcedpArr X N a cap len)
    {i : Nat} (hi : i ≤ cap) : a + 0x20 * i ≤ 0x2020 := by
  rcases A.pos with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

theorem AcedpArr.hi4 {X : AceCtx} {N : Word → BitVec 8} {a cap len : Nat} (A : AcedpArr X N a cap len)
    {i : Nat} (hi : i ≤ cap) : a + 0x20 * i + 4 ≤ 0x2020 := by
  rcases A.pos with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

/-! ## What the checks write -/

/-- `x` lies outside what the checks write: their callees' frames below
`sp`, the enumerator at `sp + 0x244`, and the iterator at `sp + 0x1320`. -/
def AcedpW (B x : Word) : Prop :=
  (x.toNat < B.toNat + 0x3A40 ∨ B.toNat + 0x3A50 ≤ x.toNat) ∧
  (x.toNat < B.toNat + 0x3C94 ∨ B.toNat + 0x3CA0 ≤ x.toNat) ∧
  (x.toNat < B.toNat + 0x4D70 ∨ B.toNat + 0x4D7C ≤ x.toNat)

theorem acedp_W_out {B x : Word} (h : x.toNat < B.toNat ∨ B.toNat + 0x5A70 ≤ x.toNat) : AcedpW B x := by
  rcases h with h | h
  · exact ⟨.inl (by omega), .inl (by omega), .inl (by omega)⟩
  · exact ⟨.inr (by omega), .inr (by omega), .inr (by omega)⟩

theorem acedp_W_sep {B x : Word} (h : Sep x 1 B 0x5A70) : AcedpW B x :=
  acedp_W_out (ace_ofSep h)

theorem acedp_W_at {B x : Word} {k : Nat} (hx : x.toNat = B.toNat + 0x3A50 + k)
    (hk : k < 0x244 ∨ (0x250 ≤ k ∧ k < 0x1320) ∨ 0x132C ≤ k) : AcedpW B x := by
  rcases hk with h | ⟨h1, h2⟩ | h
  · exact ⟨.inr (by omega), .inl (by omega), .inl (by omega)⟩
  · exact ⟨.inr (by omega), .inr (by omega), .inl (by omega)⟩
  · exact ⟨.inr (by omega), .inr (by omega), .inr (by omega)⟩

section
variable {B x : Word} (F : Fr B 0x5A70)
include F

theorem AcedpW.frame (h : AcedpW B x) : Sep x 1 (B + BitVec.ofNat 32 0x3A40) 16 := by
  refine ace_sepX F (by decide) ?_
  rcases h.1 with h | h
  · exact .inl h
  · exact .inr (by omega)

theorem AcedpW.sE (h : AcedpW B x) : Sep x 1 (acSlot B 0x244) 12 := by
  refine ace_sepX F (c := 0x3C94) (by decide) ?_
  rcases h.2.1 with h | h
  · exact .inl h
  · exact .inr (by omega)

theorem AcedpW.sI (h : AcedpW B x) : Sep x 1 (acSlot B 0x1320) 12 := by
  refine ace_sepX F (c := 0x4D70) (by decide) ?_
  rcases h.2.2 with h | h
  · exact .inl h
  · exact .inr (by omega)

end

/-- Memory `M` holds what `N` holds outside what the checks write. -/
def AcedpM (X : AceCtx) (N M : Word → BitVec 8) : Prop := ∀ x, AcedpW X.B x → M x = N x

/-- What the checks need of the machine at 0x1434, whose memory is `N`. -/
structure AcedpS (X : AceCtx) (N : Word → BitVec 8) (fp : Word) : Prop where
  ok : X.Ok
  code : CodeIn N AC bootMainClosure0Code
  saves : ∀ k, k < 13 → memLoad32 N (X.B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = X.v k
  out : ∀ x, Sep x 1 X.B 0x5A70 → Sep x 1 X.Bf acBufLen → N x = X.M0 x
  res : memLoad32 N (acSlot X.B 0x40) = X.r
  fhi : fp.toNat ≤ X.Bf.toNat + 0xB840

/-- The registers the checks keep: `sp`, `gp`, `tp`, `s5`, `s9`, and `s11`. -/
structure AcedpR (X : AceCtx) (f : Fin 32 → Word) : Prop where
  rz : f 0 = 0
  rsp : f (2 : Fin 32) = X.B + 0x3A50
  rgp : f (3 : Fin 32) = X.g
  rtp : f (4 : Fin 32) = X.t
  r21 : f (21 : Fin 32) = reg X.K 21
  r25 : f (25 : Fin 32) = reg X.K 25
  r27 : f (27 : Fin 32) = reg X.K 27

theorem AcedpR.up {X : AceCtx} {f : Fin 32 → Word} (h : AcedpR X f) {rd : Fin 32} {v : Word}
    (hr : rd.val ∉ [0, 2, 3, 4, 21, 25, 27]) : AcedpR X (upd f rd v) := by
  have k : ∀ q : Fin 32, q.val ∈ [0, 2, 3, 4, 21, 25, 27] → upd f rd v q = f q := fun q hq => by
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp only [upd_app, h0, ↓reduceIte]; exact h.rz.symm
    · have : q ≠ rd := fun e => hr (e ▸ hq)
      simp only [upd_app, h0, this, ↓reduceIte]
  exact ⟨by simp only [upd_app, ↓reduceIte, Fin.val_zero], (k 2 (by decide)).trans h.rsp,
    (k 3 (by decide)).trans h.rgp, (k 4 (by decide)).trans h.rtp, (k 21 (by decide)).trans h.r21,
    (k 25 (by decide)).trans h.r25, (k 27 (by decide)).trans h.r27⟩

theorem AcedpR.cl {X : AceCtx} {f : Fin 32 → Word} (h : AcedpR X f) {m : Machine} {cl : List (Fin 32)}
    (hc : ∀ q : Fin 32, q.val ∈ [0, 2, 3, 4, 21, 25, 27] → q ∉ cl) : AcedpR X (clob f m cl) := by
  have k : ∀ q : Fin 32, q.val ∈ [0, 2, 3, 4, 21, 25, 27] → clob f m cl q = f q := fun q hq => by
    simp only [clob_app, hc q hq, ↓reduceIte]
  exact ⟨(k 0 (by decide)).trans h.rz, (k 2 (by decide)).trans h.rsp, (k 3 (by decide)).trans h.rgp,
    (k 4 (by decide)).trans h.rtp, (k 21 (by decide)).trans h.r21,
    (k 25 (by decide)).trans h.r25, (k 27 (by decide)).trans h.r27⟩

/-- Registers that a call keeps. -/
theorem AcedpR.keep {X : AceCtx} {f g : Fin 32 → Word} (h : AcedpR X f)
    (hg : ∀ x, x ∉ jClob → x ≠ ra → g x = f x) : AcedpR X g :=
  ⟨(hg 0 (by decide) (by decide)).trans h.rz, (hg 2 (by decide) (by decide)).trans h.rsp,
    (hg 3 (by decide) (by decide)).trans h.rgp, (hg 4 (by decide) (by decide)).trans h.rtp,
    (hg 21 (by decide) (by decide)).trans h.r21, (hg 25 (by decide) (by decide)).trans h.r25,
    (hg 27 (by decide) (by decide)).trans h.r27⟩

/-- Rebuilds `AcedpR` through a chain of `upd`s and `clob`s. -/
macro "acedp_hr" : tactic => `(tactic| first
  | assumption
  | (repeat (first | refine AcedpR.up ?_ (by decide) | refine AcedpR.cl ?_ (by decide))); assumption)

/-- After a call: the registers outside `jClob` and `ra`. -/
theorem acedp_clob {f : Fin 32 → Word} {m : Machine} {ret : Word} (hz : f 0 = 0) :
    ∀ x, x ∉ jClob → x ≠ ra → clob (upd f ra ret) m jClob x = f x := fun x h1 h2 => by
  rw [clob_app, if_neg h1, upd_app]
  by_cases h0 : x.val = 0
  · rw [if_pos h0, ← hz]; exact congrArg f (Fin.ext h0).symm
  · rw [if_neg h0, if_neg h2]

/-! ## What memory outside the writes gives -/

section
variable {X : AceCtx} {N M : Word → BitVec 8} {fp : Word} (S : AcedpS X N fp) (hM : AcedpM X N M)
include S hM

theorem acedp_code : CodeIn M AC bootMainClosure0Code := fun i hi => by
  have hAC := ace_AC.1
  have hACl := ace_AC.2
  have hi32 : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  have h : (AC + BitVec.ofNat 32 i).toNat = AC.toNat + i := by
    rw [BitVec.toNat_add, hi32]; omega
  have := S.ok.lay.fr.hi
  rw [hM _ (acedp_W_out (.inr (by rw [h]; omega)))]
  exact S.code i hi

theorem acedp_out : ∀ x, Sep x 1 X.B 0x5A70 → Sep x 1 X.Bf acBufLen → M x = X.M0 x := fun x h1 h2 =>
  (hM x (acedp_W_sep h1)).trans (S.out x h1 h2)

theorem acedp_env : AcExtractEnv M := S.ok.env M (acedp_out S hM)

theorem acedp_slotW {k : Nat} (hk : k < 0x244 ∨ (0x250 ≤ k ∧ k < 0x1320) ∨ 0x132C ≤ k) (h : 0x3A50 + k ≤ 0x5A70) :
    M (acSlot X.B k) = N (acSlot X.B k) :=
  hM _ (acedp_W_at (k := k) (by rw [ace_slotN S.ok.lay.fr h]; omega) hk)

theorem acedp_ldS {k : Nat} (hk : k + 4 ≤ 0x244 ∨ (0x250 ≤ k ∧ k + 4 ≤ 0x1320) ∨ (0x132C ≤ k ∧ k + 4 ≤ 0x2020)) :
    memLoad32 M (acSlot X.B k) = memLoad32 N (acSlot X.B k) := by
  refine ace_load_eq fun j hj => ?_
  have hk' : 0x3A50 + k + j ≤ 0x5A70 := by rcases hk with h | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  refine hM _ (acedp_W_at (k := k + j) (by rw [ace_slotAdd S.ok.lay.fr hk']; omega) ?_)
  rcases hk with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl (by omega)
  · exact .inr (.inl ⟨by omega, by omega⟩)
  · exact .inr (.inr (by omega))

theorem acedp_inv {n : Machine} (hn : n.mem = M) (h2 : reg n (2 : Fin 32) = X.B + 0x3A50)
    (h3 : reg n (3 : Fin 32) = X.g) (h4 : reg n (4 : Fin 32) = X.t) : AcInv X.B X.Bf X.g X.t X.v X.M0 n := by
  refine ⟨h2, h3, h4, fun k hk => ?_, by rw [hn]; exact acedp_out S hM⟩
  rw [hn, ← S.saves k hk]
  refine ace_load_eq fun j hj => hM _ (acedp_W_at (k := 0x201C - 4 * k + j) ?_ (.inr (.inr (by omega))))
  have := S.ok.lay.fr.hi
  rw [add_ofNat_assoc, S.ok.lay.fr.at _ (by omega)]
  omega

theorem acedp_res : memLoad32 M (acSlot X.B 0x40) = X.r := by
  rw [acedp_ldS S hM (k := 0x40) (.inl (by decide))]; exact S.res

/-- A listed entry's word at `k` holds what it holds in `N`. -/
theorem acedp_ldE {a cap len : Nat} (A : AcedpArr X N a cap len) {i k : Nat} (hi : i < cap) (hk : k + 4 ≤ 0x20) :
    memLoad32 M (acedpE X.B a i + BitVec.ofNat 32 k) = memLoad32 N (acedpE X.B a i + BitVec.ofNat 32 k) := by
  rw [acedpE_add]
  refine acedp_ldS S hM ?_
  rcases A.pos with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inr (.inl ⟨by omega, by omega⟩)
  · exact .inr (.inr ⟨by omega, by omega⟩)

theorem acedp_ldE0 {a cap len : Nat} (A : AcedpArr X N a cap len) {i : Nat} (hi : i < cap) :
    memLoad32 M (acedpE X.B a i) = memLoad32 N (acedpE X.B a i) := by
  have := acedp_ldE S hM A hi (k := 0) (by decide)
  rwa [add_ofNat_zero] at this

/-- Bytes in `Buffers` below `fp` hold what they hold in `N`. -/
theorem acedp_bytes {p : Word} {l : Nat} {bs : Bytes} (hb : AceBytesIn X.Bf fp N p l bs) :
    memBytes M p l = bs := by
  obtain ⟨h1, h2, h3⟩ := hb
  rw [← h3]
  refine ace_memBytes_ext fun c hc => hM _ (acedp_W_sep (ace_bufOut S.ok.lay ?_ ?_))
  · have := S.fhi; have := S.ok.lay.hi
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · have := S.fhi; have := S.ok.lay.hi
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold acBufLen at *; omega

end

theorem acedp_bSep {X : AceCtx} {N : Word → BitVec 8} {fp : Word} (S : AcedpS X N fp) {p : Word} {l : Nat}
    {bs : Bytes} (hb : AceBytesIn X.Bf fp N p l bs) {c n : Nat} (hc : c + n ≤ 0x5A70) :
    Sep (X.B + BitVec.ofNat 32 c) n p l := by
  obtain ⟨h1, h2, -⟩ := hb
  have hw := S.ok.lay.hi
  have hf := S.fhi
  have e : p = X.Bf + BitVec.ofNat 32 (p.toNat - X.Bf.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    unfold acBufLen at hw
    omega
  rw [e]
  exact (S.ok.lay.sep.sub (c := c) (l := n) hc).subR (c := p.toNat - X.Bf.toNat) (l := l)
    (by unfold acBufLen; omega)

/-! ## Addresses in the frame -/

theorem acedp_fr16 (B : Word) : B + 0x3A50 + 0xFFFFFFF0 = B + BitVec.ofNat 32 0x3A40 := by
  rw [BitVec.add_assoc]; rfl

theorem acedp_fr4 (B : Word) : B + 0x3A50 + 0xFFFFFFFC = B + BitVec.ofNat 32 0x3A4C := by
  rw [BitVec.add_assoc]; rfl

theorem acedp_out4 {M M2 : Word → BitVec 8} {B : Word} (h : Out M M2 (B + BitVec.ofNat 32 0x3A4C) 4) :
    Out M M2 (B + BitVec.ofNat 32 0x3A40) 16 := fun x hx => h x (by
  have := sep_in hx (d := 12) (l := 4) (by decide)
  rwa [add_ofNat_assoc] at this)

theorem acedp_spE (B : Word) : aluEval .add (B + 0x3A50) 0x244 = acSlot B 0x244 := by
  rw [ev_add, BitVec.add_assoc]; rfl

theorem acedp_spI (B : Word) : aluEval .add (aluEval .add 0x1000 0x310) (B + 0x3A50) + 0x10 = acSlot B 0x1320 := by
  unfold acSlot; rw [ev_add, ev_add, BitVec.add_comm (_ + _) (B + _)]; simp only [BitVec.add_assoc]; try rfl

theorem acedp_spI4 (B : Word) :
    aluEval .add (aluEval .add 0x1000 0x310) (B + 0x3A50) + 0x14 = acSlot B 0x1320 + 4 := by
  unfold acSlot; rw [ev_add, ev_add, BitVec.add_comm (_ + _) (B + _)]; simp only [BitVec.add_assoc]; try rfl

theorem acedp_spI8 (B : Word) :
    aluEval .add (aluEval .add 0x1000 0x310) (B + 0x3A50) + 0x18 = acSlot B 0x1320 + 8 := by
  unfold acSlot; rw [ev_add, ev_add, BitVec.add_comm (_ + _) (B + _)]; simp only [BitVec.add_assoc]; try rfl

theorem acedp_spN (B : Word) : aluEval .add (aluEval .add 0x1000 0x320) (B + 0x3A50) = acSlot B 0x1320 := by
  rw [ev_add, ev_add, BitVec.add_comm, BitVec.add_assoc]; rfl

theorem acedp_spE0 (B : Word) : aluEval .add (B + 0x3A50) 0x200 + 0x44 = acSlot B 0x244 := by
  rw [ev_add, BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem acedp_spE4 (B : Word) : aluEval .add (B + 0x3A50) 0x200 + 0x48 = acSlot B 0x244 + 4 := by
  rw [ev_add, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem acedp_spE8 (B : Word) : aluEval .add (B + 0x3A50) 0x200 + 0x4C = acSlot B 0x244 + 8 := by
  rw [ev_add, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; rfl

/-- The count after `next`, less one: `(n | ((n ≠ 0) - 1)) - 1` with `n = i + 1`. -/
theorem acedp_cnt : ∀ i < 16, aluEval .add (aluEval .or (aluEval .add (BitVec.ofNat 32 i) 1)
    (aluEval .add (aluEval .sltu 0 (aluEval .add (BitVec.ofNat 32 i) 1)) 0xFFFFFFFF)) 0xFFFFFFFF =
    BitVec.ofNat 32 i := by decide

/-! ## Memory stores -/

theorem acedp_codeStore {M : Word → BitVec 8} {base it v : Word} {code : List Nat} (hc : CodeIn M base code)
    (hs : Sep it 4 base code.length) : CodeIn (memStore32 M it v) base code := fun i hi => by
  rw [memStore32_get_sep (sep_pt hs hi).symm]; exact hc i hi

theorem acedp_sep12 {it x : Word} (h : Sep it 12 x 1) {c : Nat} (hc : c + 4 ≤ 12) : Sep (it + BitVec.ofNat 32 c) 4 x 1 :=
  h.sub hc

theorem acedp_sep12_0 {it x : Word} (h : Sep it 12 x 1) : Sep it 4 x 1 := by
  have := acedp_sep12 h (c := 0) (by decide); rwa [add_ofNat_zero] at this

/-- The three words of an enumerator or iterator, past the first store. -/
theorem acedp_ld3 {M : Word → BitVec 8} {it : Word} {v : Word} (hl : it.toNat + 12 ≤ 2 ^ 32) :
    memLoad32 (memStore32 M it v) (it + 4) = memLoad32 M (it + 4) ∧
    memLoad32 (memStore32 M it v) (it + 8) = memLoad32 M (it + 8) := by
  have h4 : Sep it 4 (it + BitVec.ofNat 32 4) 4 := sep_of_le (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have h8 : Sep it 4 (it + BitVec.ofNat 32 8) 4 := sep_of_le (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  exact ⟨memLoad32_store32_sep h4, memLoad32_store32_sep h8⟩

/-! ## The exits -/

/-- At the checks' exits: `AcInv`, and the exit at 0x7D6 or `P` at 0x1778. -/
def acedpQ (X : AceCtx) (P : Machine → Prop) : Post := fun pc M f =>
  ∀ n : Machine, n.pc = pc → n.mem = M → (∀ q, reg n q = f q) →
    AcInv X.B X.Bf X.g X.t X.v X.M0 n ∧ (AcFail X.B X.r n ∨ (n.pc = AC + BitVec.ofNat 32 0x1778 ∧ P n))

theorem acedp_stage {X : AceCtx} {P : Machine → Prop} {n0 : Machine} (hc : CodeIn n0.mem AC bootMainClosure0Code)
    (hs : St n0.mem AC n0 0x1434 (reg n0))
    (k : WP bootMainClosure0Code AC (acedpQ X P) n0.mem 0x1434 (reg n0)) : X.stage n0 0x1778 P := by
  obtain ⟨m', c, q⟩ := k (by decide) hc n0 hs
  exact ⟨m', c, .inr (q m' rfl rfl fun _ => rfl)⟩

/-- At 0x1778, `P` of a machine in the state `M`, `f`. -/
theorem acedp_f1778 {X : AceCtx} {P : Machine → Prop} {N M : Word → BitVec 8} {fp : Word} {f : Fin 32 → Word}
    (S : AcedpS X N fp) (hM : AcedpM X N M) (R : AcedpR X f)
    (hP : ∀ n : Machine, n.pc = AC + BitVec.ofNat 32 0x1778 → n.mem = M → (∀ q, reg n q = f q) → P n) :
    WP bootMainClosure0Code AC (acedpQ X P) M 0x1778 f :=
  WP.here fun n hpc hn hr => ⟨acedp_inv S hM hn (by rw [hr]; exact R.rsp) (by rw [hr]; exact R.rgp)
    (by rw [hr]; exact R.rtp), .inr ⟨hpc, hP n hpc hn hr⟩⟩

/-- From 0x1774, a duplicate found, to the exit at 0x7D6 with code 0xD. -/
theorem acedp_f1774 {X : AceCtx} {P : Machine → Prop} {N M : Word → BitVec 8} {fp : Word} {f : Fin 32 → Word}
    (S : AcedpS X N fp) (hM : AcedpM X N M) (R : AcedpR X f) :
    WP bootMainClosure0Code AC (acedpQ X P) M 0x1774 f := by
  refine WP.aluImm ac_at_1774 ?_
  refine WP.jal ac_at_1776 (by decide) ?_
  refine WP.alu ac_at_1a6a ?_
  refine WP.jal ac_at_1a6c (by decide) ?_
  refine WP.here fun n hpc hn hr => ?_
  refine ⟨acedp_inv S hM hn (by rw [hr]; rsimp; exact R.rsp) (by rw [hr]; rsimp; exact R.rgp)
    (by rw [hr]; rsimp; exact R.rtp), .inl (.inr (.inr (.inl ⟨by rw [hpc]; rfl, by rw [hn]; exact acedp_res S hM, ?_⟩)))⟩
  rw [hr]; rsimp; rw [R.rz]; decide

/-- A jump to 0x1774. -/
theorem acedp_j1774 {X : AceCtx} {P : Machine → Prop} {N M : Word → BitVec 8} {fp : Word} {f : Fin 32 → Word}
    {off : Nat} {o : Word} (S : AcedpS X N fp) (hM : AcedpM X N M) (R : AcedpR X f)
    (h : fetchRel bootMainClosure0Code off = some (.jal 0 o, 2)) (ht : (off + o.toNat) % 2 ^ 32 = 0x1774) :
    WP bootMainClosure0Code AC (acedpQ X P) M off f :=
  WP.jal h (by rw [ht]) (by rw [ht]; exact acedp_f1774 S hM R)

/-! ## The calls -/

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

theorem acedp_tOut {M : Word → BitVec 8} {it x : Word} (h : Sep it 12 x 1) :
    (if fnRes M it = 0 then fnMem M it
      else memStore32 (fnMem M it) (it + 8) (memLoad32 M (it + 8) + 1)) x = M x := by
  have h0 := acedp_sep12_0 h
  have h8 : Sep (it + 8) 4 x 1 := acedp_sep12 h (c := 8) (by decide)
  have hf : fnMem M it x = M x := by
    unfold fnMem
    split
    · rfl
    · exact memStore32_get_sep h0
  split
  · exact hf
  · rw [memStore32_get_sep h8]; exact hf

/-- A call to the enumerator's `next(it)`. -/
theorem acedp_callEnum {hi lo it : Word}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 fulcioEnumNextAddress) (hev : (off + 8) % 2 = 0)
    (hc : CodeIn M (BitVec.ofNat 32 fulcioEnumNextAddress) fulcioEnumNextCode)
    (hn : CodeIn M (BitVec.ofNat 32 fulcioIterNextAddress) fulcioIterNextCode)
    (h0 : f a0 = it) (hal : (f sp).toNat % 4 = 0) (hit : it.toNat % 4 = 0)
    (hptr : (memLoad32 M it).toNat % 4 = 0)
    (hS : Sep (f sp + 0xFFFFFFF0) 16 (BitVec.ofNat 32 fulcioEnumNextAddress) fulcioEnumNextCode.length)
    (hSn : Sep (f sp + 0xFFFFFFF0) 16 (BitVec.ofNat 32 fulcioIterNextAddress) fulcioIterNextCode.length)
    (hI : Sep it 12 (f sp + 0xFFFFFFF0) 16)
    (hIc : Sep it 12 (BitVec.ofNat 32 fulcioEnumNextAddress) fulcioEnumNextCode.length)
    (hIn : Sep it 12 (BitVec.ofNat 32 fulcioIterNextAddress) fulcioIterNextCode.length)
    (hP : Sep (memLoad32 M it) 4 (f sp + 0xFFFFFFF0) 16)
    (hSb : Sep (f sp + 0xFFFFFFF0) 16 base code.length) (hIb : Sep it 12 base code.length)
    (k : ∀ m2 : Machine, reg m2 a1 = fnRes M it →
      reg m2 a0 = (if fnRes M it = 0 then 0 else memLoad32 M (it + 8)) →
      (∀ x, Sep (f sp + 0xFFFFFFF0) 16 x 1 → m2.mem x = (if fnRes M it = 0 then fnMem M it
        else memStore32 (fnMem M it) (it + 8) (memLoad32 M (it + 8) + 1)) x) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  have hn' : CodeIn M (BitVec.ofNat 32 fulcioEnumNextAddress + 0x52) fulcioIterNextCode := by
    rw [show BitVec.ofNat 32 fulcioEnumNextAddress + 0x52 = BitVec.ofNat 32 fulcioIterNextAddress by decide]
    exact hn
  have e52 : BitVec.ofNat 32 fulcioEnumNextAddress + 0x52 = BitVec.ofNat 32 fulcioIterNextAddress := by decide
  refine WP.callGen (tb := BitVec.ofNat 32 fulcioEnumNextAddress) (cl := jClob)
    (P := fun m2 => reg m2 a1 = fnRes M it ∧ reg m2 a0 = (if fnRes M it = 0 then 0 else memLoad32 M (it + 8)) ∧
      ∀ x, Sep (f sp + 0xFFFFFFF0) 16 x 1 → m2.mem x = (if fnRes M it = 0 then fnMem M it
        else memStore32 (fnMem M it) (it + 8) (memLoad32 M (it + 8) + 1)) x)
    h1 h2 (by rw [htgt]; decide) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc i hi => ?_) (fun m2 hP => k m2 hP.1 hP.2.1 hP.2.2)
  · have hr := tmc_regs hreg1
    have hs1 : reg m1 sp = f sp := hr sp (by decide)
    obtain ⟨m2, c2, pc2, sp2, a12, a02, rs2, mem2⟩ := fulcioEnumNext_correct m1 (by rw [hmem1]; exact hc)
      (by rw [hmem1]; exact hn') (by decide) hpc1 (by rw [hr a0 (by decide), h0]) (by rw [hreg1]; rsimp)
      (even_clear _ (even_at base hb _ hev)) (by rw [hs1]; exact hal) hit (by rw [hmem1]; exact hptr)
      (by rw [hs1]; exact hS) (by rw [hs1, e52]; exact hSn) (by rw [hs1]; exact hI) hIc (by rw [e52]; exact hIn)
      (by rw [hs1, hmem1]; exact hP)
    rw [hmem1] at a12 a02 mem2
    refine ⟨m2, c2, pc2, ⟨a12, a02, fun x hx => by rw [mem2 x (by rw [hs1]; exact hx)]⟩, fun x hx => ?_⟩
    exact rs2 x (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide))
      (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide))
  · have hx := sep_pt hSb hi
    rw [hP.2.2 _ hx.symm, acedp_tOut (sep_pt hIb hi).symm]
    exact hc i hi

/-- A call to the iterator's `nth(it, n)`. -/
theorem acedp_callNth {hi lo it : Word} {n L : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 fulcioIterNthAddress) (hev : (off + 8) % 2 = 0)
    (hc : CodeIn M (BitVec.ofNat 32 fulcioIterNthAddress) fulcioIterNthCode)
    (hn : CodeIn M (BitVec.ofNat 32 fulcioIterNextAddress) fulcioIterNextCode)
    (h0 : f a0 = it) (ha1 : f a1 = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32) (hit : it.toNat % 4 = 0)
    (hp0 : (memLoad32 M it).toNat % 4 = 0)
    (hend : memLoad32 M (it + 4) = memLoad32 M it + BitVec.ofNat 32 (32 * L)) (hL : 32 * L < 2 ^ 32)
    (hS : Sep it 4 (BitVec.ofNat 32 fulcioIterNthAddress) fulcioIterNthCode.length)
    (hSn : Sep it 4 (BitVec.ofNat 32 fulcioIterNextAddress) fulcioIterNextCode.length)
    (hE : Sep it 4 (memLoad32 M it) (32 * L)) (hSb : Sep it 4 base code.length)
    (k : ∀ m2 : Machine,
      reg m2 a0 = (if (fnStop M (memLoad32 M (it + 4)) n (memLoad32 M it)).2 then
        fnRes (memStore32 M it (fnStop M (memLoad32 M (it + 4)) n (memLoad32 M it)).1) it else 0) →
      m2.mem = (if (fnStop M (memLoad32 M (it + 4)) n (memLoad32 M it)).2 then
        fnMem (memStore32 M it (fnStop M (memLoad32 M (it + 4)) n (memLoad32 M it)).1) it
        else memStore32 M it (fnStop M (memLoad32 M (it + 4)) n (memLoad32 M it)).1) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  have e2c : BitVec.ofNat 32 fulcioIterNthAddress + 0x2C = BitVec.ofNat 32 fulcioIterNextAddress := by decide
  refine WP.callGen (tb := BitVec.ofNat 32 fulcioIterNthAddress) (cl := jClob)
    (P := fun m2 => reg m2 a0 = (if (fnStop M (memLoad32 M (it + 4)) n (memLoad32 M it)).2 then
        fnRes (memStore32 M it (fnStop M (memLoad32 M (it + 4)) n (memLoad32 M it)).1) it else 0) ∧
      m2.mem = (if (fnStop M (memLoad32 M (it + 4)) n (memLoad32 M it)).2 then
        fnMem (memStore32 M it (fnStop M (memLoad32 M (it + 4)) n (memLoad32 M it)).1) it
        else memStore32 M it (fnStop M (memLoad32 M (it + 4)) n (memLoad32 M it)).1))
    h1 h2 (by rw [htgt]; decide) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => ?_) (fun m2 hP => k m2 hP.1 hP.2)
  · have hr := tmc_regs hreg1
    obtain ⟨m2, c2, pc2, a02, rs2, mem2⟩ := fulcioIterNth_correct m1 (L := L) (by rw [hmem1]; exact hc)
      (by rw [hmem1, e2c]; exact hn) (by decide) hpc1 (by rw [hr a0 (by decide), h0])
      (by rw [hr a1 (by decide), ha1]) hn32 (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev)) hit
      (by rw [hmem1]; exact hp0) (by rw [hmem1]; exact hend) hL hS (by rw [e2c]; exact hSn)
      (by rw [hmem1]; exact hE)
    rw [hmem1] at a02 mem2
    refine ⟨m2, c2, pc2, ⟨a02, mem2⟩, fun x hx => ?_⟩
    exact rs2 x (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide))
      (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide))
      (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide))
  · rw [hP.2]
    have hs1 : CodeIn (memStore32 M it (fnStop M (memLoad32 M (it + 4)) n (memLoad32 M it)).1) base code :=
      acedp_codeStore hc hSb
    split
    · unfold fnMem
      split
      · exact hs1
      · exact acedp_codeStore hs1 hSb
    · exact hs1

end

/-! ## `nth` on an array -/

/-- `nth` stepping over the listed entries `j` to `j + k`. -/
theorem acedp_stop {M : Word → BitVec 8} {B : Word} (F : Fr B 0x5A70) {a cap len : Nat}
    (hc : a + 0x20 * cap ≤ 0x2020) (hl : len ≤ cap)
    (htag : ∀ j, j < len → memLoad32 M (acedpE B a j) ≠ 0) :
    ∀ k j, j + k ≤ len → fnStop M (acedpE B a cap) k (acedpE B a j) = (acedpE B a (j + k), true)
  | 0, j, _ => rfl
  | k + 1, j, h => by
    have hne : acedpE B a j ≠ acedpE B a cap := acedpE_ne (by omega) hc (by omega)
    show (if acedpE B a j = acedpE B a cap then _ else _) = _
    rw [if_neg hne, if_neg (htag j (by omega)), acedpE_succ, acedp_stop F hc hl htag k (j + 1) (by omega),
      Nat.add_assoc, Nat.add_comm 1 k]

/-! ## Branches -/

theorem acedp_beqT {a : Word} (h : branchTaken .beq a 0 = true) : a = 0 := rm_beqT h

theorem acedp_beqF {a : Word} (h : branchTaken .beq a 0 = false) : a ≠ 0 := rm_beqF h

theorem acedp_beq {a b : Word} (h : branchTaken .beq a b = true) : a = b := beq_iff_eq.mp h

theorem acedp_bne {a b : Word} (h : branchTaken .beq a b = false) : a ≠ b := fun e =>
  Bool.false_ne_true (h.symm.trans (beq_iff_eq.mpr e))

theorem acedp_zadd (x : Word) : (0 : Word) + x = x := BitVec.zero_add x

theorem acedp_wpOff {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {o o' : Nat}
    {f : Fin 32 → Word} (h : o = o') (k : WP code base Q M o' f) : WP code base Q M o f := h ▸ k

/-- Offsets: reduce `o + c + d` to `o + (c + d)`. -/
macro "acedp_wo" : tactic => `(tactic| (wn; try simp only [Nat.add_assoc, Nat.reduceAdd]))

/-! ## Registers and memory through the loops -/

theorem acedp_updK {f g : Fin 32 → Word} {rd : Fin 32} {v : Word} (hz : f 0 = 0) (hrd : rd ∈ jClob)
    (hg : ∀ x, x ∉ jClob → x ≠ ra → g x = f x) : ∀ x, x ∉ jClob → x ≠ ra → upd g rd v x = f x :=
  fun x h1 h2 => by
    rw [upd_app]
    by_cases h0 : x.val = 0
    · rw [if_pos h0, ← hz]; exact congrArg f (Fin.ext h0).symm
    · rw [if_neg h0, if_neg (show x ≠ rd from fun e => h1 (e ▸ hrd)), hg x h1 h2]

theorem acedp_clobK {f g : Fin 32 → Word} {m : Machine} {ret : Word} (hz : f 0 = 0)
    (hg : ∀ x, x ∉ jClob → x ≠ ra → g x = f x) :
    ∀ x, x ∉ jClob → x ≠ ra → clob (upd g ra ret) m jClob x = f x :=
  fun x h1 h2 => (acedp_clob ((hg 0 (by decide) (by decide)).trans hz) x h1 h2).trans (hg x h1 h2)

/-- Registers outside `jClob` and `ra` through `upd`s of registers in
`jClob` and calls; needs `f 0 = 0` in the context. -/
macro "acedp_keep" : tactic => `(tactic| repeat (first
  | with_reducible refine acedp_clobK (by assumption) ?_
  | with_reducible refine acedp_updK (by assumption) (by decide) ?_
  | with_reducible exact fun _ _ _ => rfl))

theorem acedp_lw {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat}
    {f : Fin 32 → Word} {rd rs1 : Fin 32} {o l a : Word} (h : fetchRel code off = some (.load .lw rd rs1 o, l))
    (hv : f rs1 + o = a) (ha : a.toNat % 4 = 0)
    (k : WP code base Q M (off + l.toNat) (upd f rd (memLoad32 M a))) : WP code base Q M off f :=
  WP.lw h (by rw [hv]; exact ha) (by rw [hv]; exact k)

theorem acedp_sw {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat}
    {f : Fin 32 → Word} {rs1 rs2 : Fin 32} {o l a w : Word} (h : fetchRel code off = some (.store .sw rs1 rs2 o, l))
    (hv : f rs1 + o = a) (hw : f rs2 = w) (ha : a.toNat % 4 = 0) (hs : Sep a 4 base code.length)
    (k : WP code base Q (memStore32 M a w) (off + l.toNat) f) : WP code base Q M off f :=
  WP.sw h (by rw [hv]; exact ha) (by rw [hv]; exact hs) (by rw [hv, hw]; exact k)

theorem acedp_E4 (B : Word) : acSlot B 0x244 + 4 = acSlot B 0x248 := by
  unfold acSlot; rw [BitVec.add_assoc]; rfl

theorem acedp_E8 (B : Word) : acSlot B 0x244 + 8 = acSlot B 0x24C := by
  unfold acSlot; rw [BitVec.add_assoc]; rfl

theorem acedp_I4 (B : Word) : acSlot B 0x1320 + 4 = acSlot B 0x1324 := by
  unfold acSlot; rw [BitVec.add_assoc]; rfl

theorem acedp_I8 (B : Word) : acSlot B 0x1320 + 8 = acSlot B 0x1328 := by
  unfold acSlot; rw [BitVec.add_assoc]; rfl

theorem acedp_sepS {B : Word} (F : Fr B 0x5A70) {c n d l : Nat} (h : c + n ≤ d ∨ d + l ≤ c)
    (hc : c + n ≤ 0x2020) (hd : d + l ≤ 0x2020) : Sep (acSlot B c) n (acSlot B d) l :=
  ace_sepB' F (c := 0x3A50 + c) (k := 0x3A50 + d) (by omega) (by omega) (by omega)

theorem acedp_sepF {B : Word} (F : Fr B 0x5A70) {d l : Nat} (hd : d + l ≤ 0x2020) :
    Sep (B + BitVec.ofNat 32 0x3A40) 16 (acSlot B d) l :=
  ace_sepB' F (c := 0x3A40) (k := 0x3A50 + d) (.inl (by omega)) (by decide) (by omega)

/-- Three words stored at `sp + c`. -/
theorem acedp_st3 {M : Word → BitVec 8} {B : Word} (F : Fr B 0x5A70) {c c4 c8 : Nat} (hc : c + 12 ≤ 0x2020)
    (h4 : c4 = c + 4) (h8 : c8 = c + 8) (u v w : Word) :
    memLoad32 (memStore32 (memStore32 (memStore32 M (acSlot B c) u) (acSlot B c4) v) (acSlot B c8) w)
        (acSlot B c) = u ∧
      memLoad32 (memStore32 (memStore32 (memStore32 M (acSlot B c) u) (acSlot B c4) v) (acSlot B c8) w)
        (acSlot B c4) = v ∧
      memLoad32 (memStore32 (memStore32 (memStore32 M (acSlot B c) u) (acSlot B c4) v) (acSlot B c8) w)
        (acSlot B c8) = w ∧
      Out M (memStore32 (memStore32 (memStore32 M (acSlot B c) u) (acSlot B c4) v) (acSlot B c8) w)
        (acSlot B c) 12 := by
  subst h4 h8
  have s04 : Sep (acSlot B c) 4 (acSlot B (c + 4)) 4 := acedp_sepS F (.inl (by omega)) (by omega) (by omega)
  have s08 : Sep (acSlot B c) 4 (acSlot B (c + 8)) 4 := acedp_sepS F (.inl (by omega)) (by omega) (by omega)
  have s48 : Sep (acSlot B (c + 4)) 4 (acSlot B (c + 8)) 4 := acedp_sepS F (.inl (by omega)) (by omega) (by omega)
  refine ⟨?_, ?_, memLoad32_store32_same _ _ _, fun x hx => ?_⟩
  · rw [memLoad32_store32_sep s08.symm, memLoad32_store32_sep s04.symm, memLoad32_store32_same]
  · rw [memLoad32_store32_sep s48.symm, memLoad32_store32_same]
  · have e : ∀ d, d + 4 ≤ 12 → Sep (acSlot B (c + d)) 4 x 1 := fun d hd => by
      have := hx.symm.sub (c := d) (l := 4) hd
      rwa [ace_slot, Nat.add_assoc] at this
    have e0 : Sep (acSlot B c) 4 x 1 := e 0 (by decide)
    rw [memStore32_get_sep (e 8 (by decide)), memStore32_get_sep (e 4 (by decide)), memStore32_get_sep e0]

/-- The state at an outer loop's head: `s2` and `s4` bound the array at
`sp + a`, and the enumerator is at entry `i`. -/
structure AcedpOut (X : AceCtx) (N M : Word → BitVec 8) (f : Fin 32 → Word) (a cap i : Nat) : Prop where
  mem : AcedpM X N M
  regs : AcedpR X f
  s2 : f 18 = acedpE X.B a 0
  s4 : f 20 = acedpE X.B a cap
  e0 : memLoad32 M (acSlot X.B 0x244) = acedpE X.B a i
  e4 : memLoad32 M (acSlot X.B 0x248) = acedpE X.B a cap
  e8 : memLoad32 M (acSlot X.B 0x24C) = BitVec.ofNat 32 i

theorem AcedpOut.mv {X : AceCtx} {N M M2 : Word → BitVec 8} {f g : Fin 32 → Word} {a cap i : Nat}
    (H : AcedpOut X N M f a cap i) (F : Fr X.B 0x5A70) (hO : Out M M2 (X.B + BitVec.ofNat 32 0x3A40) 16)
    (R : AcedpR X g) (h18 : g 18 = f 18) (h20 : g 20 = f 20) : AcedpOut X N M2 g a cap i :=
  ⟨fun x hx => (hO x (AcedpW.frame F hx)).trans (H.mem x hx), R, h18.trans H.s2, h20.trans H.s4,
    (hO.load32 (acedp_sepF F (by decide))).trans H.e0, (hO.load32 (acedp_sepF F (by decide))).trans H.e4,
    (hO.load32 (acedp_sepF F (by decide))).trans H.e8⟩

theorem acedp_outId {M : Word → BitVec 8} {s : Word} {k : Nat} : Out M M s k := fun _ _ => rfl

/-- The outer loop has compared each entry before `i` with every later one. -/
def AcedpProg (xs : List Bytes) (len i : Nat) : Prop :=
  ∀ i' k, i' < i → i' < k → k < len → xs[k]? ≠ xs[i']?

theorem acedp_prog_distinct {xs : List Bytes} {len : Nat} (hl : xs.length = len) (h : AcedpProg xs len len) :
    distinct xs = true :=
  acedp_distinct xs fun i k hik hk => h i k (by omega) hik (by omega)

theorem acedp_prog_succ {xs : List Bytes} {len i : Nat} (h : AcedpProg xs len i)
    (hk : ∀ k, i < k → k < len → xs[k]? ≠ xs[i]?) : AcedpProg xs len (i + 1) := fun i' k h1 h2 h3 => by
  by_cases e : i' = i
  · subst e; exact hk k h2 h3
  · exact h i' k (by omega) h2 h3

/-- From an outer loop's head through the enumerator's `next`. -/
theorem acedp_enumStep {X : AceCtx} {N : Word → BitVec 8} {fp : Word} {Q : Post} (S : AcedpS X N fp)
    {a cap len : Nat} (A : AcedpArr X N a cap len) {o : Nat} {hE lE : Word}
    (c0 : fetchRel bootMainClosure0Code o = some (.aluImm .add a0 sp 0x244, 2))
    (c2 : fetchRel bootMainClosure0Code (o + 2) = some (.auipc ra hE, 4))
    (c6 : fetchRel bootMainClosure0Code (o + 2 + 4) = some (.jalr ra ra lE, 4))
    (tE : AC + BitVec.ofNat 32 (o + 2) + hE + lE = BitVec.ofNat 32 fulcioEnumNextAddress) (hev : o % 2 = 0)
    {i : Nat} (hi : i ≤ len) {M : Word → BitVec 8} {f : Fin 32 → Word} (H : AcedpOut X N M f a cap i)
    (k : ∀ (M2 : Word → BitVec 8) (g : Fin 32 → Word), AcedpM X N M2 →
      (∀ x, x ∉ jClob → x ≠ ra → g x = f x) →
      g a1 = (if i < len then acedpE X.B a i else 0) →
      (i < len → g a0 = BitVec.ofNat 32 i ∧ memLoad32 M2 (acSlot X.B 0x244) = acedpE X.B a (i + 1) ∧
        memLoad32 M2 (acSlot X.B 0x248) = acedpE X.B a cap ∧
        memLoad32 M2 (acSlot X.B 0x24C) = BitVec.ofNat 32 (i + 1)) →
      WP bootMainClosure0Code AC Q M2 (o + 10) g) :
    WP bootMainClosure0Code AC Q M o f := by
  have F := S.ok.lay.fr
  have env := acedp_env S H.mem
  have R := H.regs
  have hz := R.rz
  have hcap : a + 0x20 * cap ≤ 0x2020 := A.hi (Nat.le_refl _)
  have hlc := A.hlen
  have hR : fnRes M (acSlot X.B 0x244) = if i < len then acedpE X.B a i else 0 := by
    unfold fnRes
    rw [acedp_E4, H.e0, H.e4]
    by_cases hl : i < len
    · rw [if_neg (acedpE_ne (A.hi (by omega)) hcap (by omega)), acedp_ldE0 S H.mem A (by omega),
        if_neg (A.tag i hl), if_pos hl]
    · rw [if_neg hl]
      by_cases hc : i = cap
      · rw [hc, if_pos rfl]
      · rw [if_neg (acedpE_ne (A.hi (by omega)) hcap hc), acedp_ldE0 S H.mem A (by omega),
          A.zero i (by omega) (by omega), if_pos rfl]
  have sE := acedp_sepF F (d := 0x244) (l := 12) (by decide)
  refine WP.aluImm c0 ?_
  simp only [BitVec.reduceToNat]
  refine acedp_callEnum (it := acSlot X.B 0x244) c2 c6 tE (by omega) env.enumNext env.iterNext
    (by rsimp; rw [R.rsp]; exact acedp_spE X.B)
    (by rsimp; rw [R.rsp]; exact ace_al4 F (c := 0x3A50) (by decide) (by decide))
    (ace_al4 F (c := 0x3C94) (by decide) (by decide))
    (by rw [H.e0]; exact acedpE_al F A.al (A.hi (by omega)))
    (by rsimp; rw [R.rsp, acedp_fr16]; exact ace_hs F (by decide) (by decide) (by decide))
    (by rsimp; rw [R.rsp, acedp_fr16]; exact ace_hs F (by decide) (by decide) (by decide))
    (by rsimp; rw [R.rsp, acedp_fr16]; exact sE.symm)
    (ace_hs F (c := 0x3C94) (by decide) (by decide) (by decide))
    (ace_hs F (c := 0x3C94) (by decide) (by decide) (by decide))
    (by
      rw [H.e0]; rsimp; rw [R.rsp, acedp_fr16]
      have := A.hi4 (i := i) (by omega)
      exact (acedp_sepF F (d := a + 0x20 * i) (l := 4) (by omega)).symm)
    (by rsimp; rw [R.rsp, acedp_fr16]; exact ace_cs F (by decide))
    (ace_cs F (c := 0x3C94) (by decide)) fun m2 ha1 ha0 hmem => ?_
  rsimp at hmem
  rw [R.rsp, acedp_fr16] at hmem
  have hO : Out _ m2.mem (X.B + BitVec.ofNat 32 0x3A40) 16 := fun x hx => hmem x hx.symm
  have hW : AcedpM X N m2.mem := fun x hx => by
    rw [hmem x (AcedpW.frame F hx).symm, acedp_tOut (AcedpW.sE F hx).symm]; exact H.mem x hx
  have hK : ∀ x, x ∉ jClob → x ≠ ra →
      clob (upd (upd f a0 (aluEval .add (f sp) 0x244)) ra (AC + BitVec.ofNat 32 (o + 2 + 8))) m2 jClob x = f x := by
    acedp_keep
  refine acedp_wpOff (by omega) (k m2.mem _ hW hK ?_ fun hl => ?_)
  · rsimp; rw [ha1, hR]
  have hl' : i < cap := by omega
  have hne : acedpE X.B a i ≠ acedpE X.B a cap := acedpE_ne (A.hi (by omega)) hcap (by omega)
  have hR' : fnRes M (acSlot X.B 0x244) ≠ 0 := by rw [hR, if_pos hl]; exact acedpE_nz F (A.hi (by omega))
  have hT : ∀ y, Sep (X.B + BitVec.ofNat 32 0x3A40) 16 y 4 → memLoad32 m2.mem y =
      memLoad32 (memStore32 (memStore32 M (acSlot X.B 0x244) (acedpE X.B a i + 0x20)) (acSlot X.B 0x24C)
        (BitVec.ofNat 32 i + 1)) y := fun y hy => by
    rw [hO.load32 hy, if_neg hR', acedp_E8, H.e8]
    unfold fnMem
    rw [acedp_E4, H.e0, H.e4, if_neg hne]
  have s04 : Sep (acSlot X.B 0x244) 4 (acSlot X.B 0x248) 4 := acedp_sepS F (.inl (by decide)) (by decide) (by decide)
  have s08 : Sep (acSlot X.B 0x244) 4 (acSlot X.B 0x24C) 4 := acedp_sepS F (.inl (by decide)) (by decide) (by decide)
  have s48 : Sep (acSlot X.B 0x248) 4 (acSlot X.B 0x24C) 4 := acedp_sepS F (.inl (by decide)) (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rsimp; rw [ha0, if_neg hR', acedp_E8, H.e8]
  · rw [hT _ (acedp_sepF F (by decide)), memLoad32_store32_sep s08.symm, memLoad32_store32_same, acedpE_succ]
  · rw [hT _ (acedp_sepF F (by decide)), memLoad32_store32_sep s48.symm, memLoad32_store32_sep s04, H.e4]
  · rw [hT _ (acedp_sepF F (by decide)), memLoad32_store32_same]
    exact ofNat_add_ofNat i 1

/-- From `lui a1, 0x1000` through the iterator's `nth(sp + 0x1320, i)` to
`a0 = sp + 0x1310`: the iterator then stands at entry `i + 1`. -/
theorem acedp_nthBlock {X : AceCtx} {N : Word → BitVec 8} {fp : Word} {Q : Post} (S : AcedpS X N fp)
    {a cap len : Nat} (A : AcedpArr X N a cap len) {p : Nat} {hT lT bo : Word}
    (c0 : fetchRel bootMainClosure0Code p = some (.lui a1 0x1000, 2))
    (c2 : fetchRel bootMainClosure0Code (p + 2) = some (.aluImm .add a1 a1 0x310, 4))
    (c6 : fetchRel bootMainClosure0Code (p + 6) = some (.alu .add a1 a1 sp, 2))
    (c8 : fetchRel bootMainClosure0Code (p + 8) = some (.store .sw a1 (18 : Fin 32) 0x10, 4))
    (cC : fetchRel bootMainClosure0Code (p + 0xC) = some (.store .sw a1 (20 : Fin 32) 0x14, 4))
    (c10 : fetchRel bootMainClosure0Code (p + 0x10) = some (.store .sw a1 x0 0x18, 4))
    (c14 : fetchRel bootMainClosure0Code (p + 0x14) = some (.aluImm .add a1 a0 0xFFFFFFFF, 4))
    (c18 : fetchRel bootMainClosure0Code (p + 0x18) = some (.lui a0 0x1000, 2))
    (c1A : fetchRel bootMainClosure0Code (p + 0x1A) = some (.aluImm .add a0 a0 0x320, 4))
    (c1E : fetchRel bootMainClosure0Code (p + 0x1E) = some (.alu .add a0 a0 sp, 2))
    (c20 : fetchRel bootMainClosure0Code (p + 0x20) = some (.auipc ra hT, 4))
    (c24 : fetchRel bootMainClosure0Code (p + 0x20 + 4) = some (.jalr ra ra lT, 4))
    (c28 : fetchRel bootMainClosure0Code (p + 0x28) = some (.branch .beq a0 x0 bo, 2))
    (c2A : fetchRel bootMainClosure0Code (p + 0x2A) = some (.lui a0 0x1000, 2))
    (c2C : fetchRel bootMainClosure0Code (p + 0x2C) = some (.aluImm .add a0 a0 0x310, 4))
    (c30 : fetchRel bootMainClosure0Code (p + 0x30) = some (.alu .add a0 a0 sp, 2))
    (tT : AC + BitVec.ofNat 32 (p + 0x20) + hT + lT = BitVec.ofNat 32 fulcioIterNthAddress) (hev : p % 2 = 0)
    {i : Nat} (hi : i < len) {M : Word → BitVec 8} {f : Fin 32 → Word} (hM : AcedpM X N M) (R : AcedpR X f)
    (h18 : f 18 = acedpE X.B a 0) (h20 : f 20 = acedpE X.B a cap)
    (ha0 : aluEval .add (f a0) 0xFFFFFFFF = BitVec.ofNat 32 i)
    (k : ∀ (M3 : Word → BitVec 8) (g : Fin 32 → Word), Out M M3 (acSlot X.B 0x1320) 12 → AcedpM X N M3 →
      (∀ x, x ∉ jClob → x ≠ ra → g x = f x) →
      g a0 + 0x10 = acSlot X.B 0x1320 → g a0 + 0x14 = acSlot X.B 0x1324 →
      memLoad32 M3 (acSlot X.B 0x1320) = acedpE X.B a (i + 1) →
      memLoad32 M3 (acSlot X.B 0x1324) = acedpE X.B a cap →
      WP bootMainClosure0Code AC Q M3 (p + 0x32) g) :
    WP bootMainClosure0Code AC Q M p f := by
  have F := S.ok.lay.fr
  have env := acedp_env S hM
  have hz := R.rz
  have hcap : a + 0x20 * cap ≤ 0x2020 := A.hi (Nat.le_refl _)
  have hlc := A.hlen
  have hc16 := A.hcap
  have hpos := A.pos
  refine WP.lui c0 ?_; acedp_wo
  refine WP.aluImm c2 ?_; acedp_wo
  refine WP.alu c6 ?_; acedp_wo
  refine acedp_sw c8 (a := acSlot X.B 0x1320) (w := acedpE X.B a 0)
    (by rsimp; rw [R.rsp]; exact acedp_spI X.B) (by rsimp; exact h18)
    (ace_al4 F (c := 0x4D70) (by decide) (by decide)) (ace_cs F (c := 0x4D70) (by decide)) ?_
  acedp_wo
  refine acedp_sw cC (a := acSlot X.B 0x1324) (w := acedpE X.B a cap)
    (by rsimp; rw [R.rsp, acedp_spI4, acedp_I4]) (by rsimp; exact h20)
    (ace_al4 F (c := 0x4D74) (by decide) (by decide)) (ace_cs F (c := 0x4D74) (by decide)) ?_
  acedp_wo
  refine acedp_sw c10 (a := acSlot X.B 0x1328) (w := 0)
    (by rsimp; rw [R.rsp, acedp_spI8, acedp_I8]) (by rsimp)
    (ace_al4 F (c := 0x4D78) (by decide) (by decide)) (ace_cs F (c := 0x4D78) (by decide)) ?_
  acedp_wo
  obtain ⟨l0, l4, -, hO2⟩ := acedp_st3 (M := M) F (c := 0x1320) (c4 := 0x1324) (c8 := 0x1328) (by decide) rfl rfl
    (acedpE X.B a 0) (acedpE X.B a cap) 0
  generalize memStore32 (memStore32 (memStore32 M (acSlot X.B 0x1320) (acedpE X.B a 0)) (acSlot X.B 0x1324)
    (acedpE X.B a cap)) (acSlot X.B 0x1328) 0 = M2 at l0 l4 hO2 ⊢
  have hent : ∀ j, j < cap → memLoad32 M2 (acedpE X.B a j) = memLoad32 N (acedpE X.B a j) := fun j hj => by
    unfold acedpE
    rw [hO2.load32 (acedp_sepS F (by omega) (by decide) (by omega))]
    exact acedp_ldE0 S hM A hj
  refine WP.aluImm c14 ?_; acedp_wo
  refine WP.lui c18 ?_; acedp_wo
  refine WP.aluImm c1A ?_; acedp_wo
  refine WP.alu c1E ?_; acedp_wo
  have env2 : AcExtractEnv M2 := S.ok.env M2 fun x h1 h2 => by
    rw [hO2 x (AcedpW.sI F (acedp_W_sep h1))]; exact acedp_out S hM x h1 h2
  refine acedp_callNth (it := acSlot X.B 0x1320) (n := i) (L := cap) c20 c24 tT (by omega)
    env2.iterNth env2.iterNext
    (by rsimp; rw [R.rsp]; exact acedp_spN X.B) (by rsimp; exact ha0) (by omega)
    (ace_al4 F (c := 0x4D70) (by decide) (by decide))
    (by rw [l0]; exact acedpE_al F A.al (A.hi (by omega)))
    (by rw [acedp_I4, l0, l4]; exact acedpE_cap X.B a cap) (by omega)
    (ace_hs F (c := 0x4D70) (by decide) (by decide) (by decide))
    (ace_hs F (c := 0x4D70) (by decide) (by decide) (by decide))
    (by rw [l0]; unfold acedpE; exact acedp_sepS F (by omega) (by decide) (by omega))
    (ace_cs F (c := 0x4D70) (by decide)) fun m2 hr0 hm2 => ?_
  have hst := acedp_stop (M := M2) F hcap hlc (fun j hj => by rw [hent j (by omega)]; exact A.tag j hj) i 0
    (by omega)
  rw [acedp_I4, l0, l4, hst, Nat.zero_add] at hr0 hm2
  dsimp only at hr0 hm2
  rw [if_pos rfl] at hr0 hm2
  have hne : acedpE X.B a i ≠ acedpE X.B a cap := acedpE_ne (A.hi (by omega)) hcap (by omega)
  have sI4 : Sep (acSlot X.B 0x1320) 4 (acSlot X.B 0x1324) 4 := acedp_sepS F (.inl (by decide)) (by decide) (by decide)
  have sIe : Sep (acSlot X.B 0x1320) 4 (acedpE X.B a i) 4 := by
    have := A.hi (i := i) (by omega)
    unfold acedpE; exact acedp_sepS F (by omega) (by decide) (by omega)
  have l4' : memLoad32 (memStore32 M2 (acSlot X.B 0x1320) (acedpE X.B a i)) (acSlot X.B 0x1324) =
      acedpE X.B a cap := by rw [memLoad32_store32_sep sI4, l4]
  have hres : fnRes (memStore32 M2 (acSlot X.B 0x1320) (acedpE X.B a i)) (acSlot X.B 0x1320) = acedpE X.B a i := by
    unfold fnRes
    rw [acedp_I4, memLoad32_store32_same, l4', if_neg hne, memLoad32_store32_sep sIe, hent i (by omega),
      if_neg (A.tag i hi)]
  have hmem : fnMem (memStore32 M2 (acSlot X.B 0x1320) (acedpE X.B a i)) (acSlot X.B 0x1320) =
      memStore32 (memStore32 M2 (acSlot X.B 0x1320) (acedpE X.B a i)) (acSlot X.B 0x1320)
        (acedpE X.B a i + 0x20) := by
    unfold fnMem
    rw [acedp_I4, memLoad32_store32_same, l4', if_neg hne]
  rw [hres] at hr0
  rw [hmem] at hm2
  have hO3 : Out M m2.mem (acSlot X.B 0x1320) 12 := fun x hx => by
    rw [hm2, memStore32_get_sep (acedp_sep12_0 hx.symm), memStore32_get_sep (acedp_sep12_0 hx.symm)]
    exact hO2 x hx
  have hW3 : AcedpM X N m2.mem := fun x hx => by rw [hO3 x (AcedpW.sI F hx)]; exact hM x hx
  acedp_wo
  refine WP.branch c28 (fun ht => ?_) fun _ => ?_
  · exfalso
    rsimp at ht
    have := acedp_beqT ht
    rw [hr0] at this
    exact acedpE_nz F (A.hi (by omega)) this
  acedp_wo
  refine WP.lui c2A ?_; acedp_wo
  refine WP.aluImm c2C ?_; acedp_wo
  refine WP.alu c30 ?_; acedp_wo
  refine k m2.mem _ hO3 hW3 (by acedp_keep) ?_ ?_ ?_ ?_
  · rsimp; rw [R.rsp]; exact acedp_spI X.B
  · rsimp; rw [R.rsp, acedp_spI4]; exact acedp_I4 X.B
  · rw [hm2, memLoad32_store32_same, acedpE_succ]
  · rw [hm2, memLoad32_store32_sep sI4, l4']

end C3.RV32.Ac
