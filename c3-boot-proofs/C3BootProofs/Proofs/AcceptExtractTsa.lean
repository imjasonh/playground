import C3BootProofs.Proofs.AcceptExtractHead
import C3BootProofs.Proofs.AcceptExtractSeq
import C3BootProofs.Proofs.TufMetaCalls
import C3BootProofs.Proofs.TufRoleKeysCalls
import C3BootProofs.Proofs.TrustedRootLiftChain

/-!
# The timestamp authorities' loop, from 0x123A to 0x1434

Each pass of the loop takes the next item of `timestampAuthorities` with
`next_element`, reads its chain with `read_chain`, and, when the first
certificate has a P-384 key, builds its `SignerIdentifier` (a DER
`SEQUENCE` header, then the issuer and the serial number) in `keys`'s free
part and appends an entry to the array of 8 at `sp + 0x890`.

The invariant is `AceTsaInv`: the items left, the keys so far as
`aceKeys aceTsa` (`mapM`, then `filterMap`) of the items done, the cursor,
and the three arrays. `acets_pass` proves one pass from its end back to its
start, and `acets_stage` proves `AceTsaStage` by induction on the items
left.

`read_chain`'s theorem leaves the error byte unconstrained when the model's
error carries no code (a decoded chain that overflows the buffer, or a
`validFor` time that doesn't parse), so `acets_stage` takes that byte's
bound as the hypothesis `AcetsRcErr`.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

set_option maxRecDepth 100000

/-! ## Arithmetic and separation -/

theorem acets_tn {a : Word} {c : Nat} (h : a.toNat + c < 2 ^ 32) :
    (a + BitVec.ofNat 32 c).toNat = a.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem acets_sep {a b : Word} {n k : Nat} (h : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat)
    (ha : a.toNat + n ≤ 2 ^ 32) (hb : b.toNat + k ≤ 2 ^ 32) : Sep a n b k := by
  rcases h with h | h
  · exact sep_of_le h hb
  · exact (sep_of_le h ha).symm

theorem acets_ld {B : Word} (F : Fr B 0x5A70) {M M' : Word → BitVec 8} {c : Nat} (hc : c + 4 ≤ 0x5A70)
    (h : ∀ y : Word, B.toNat + c ≤ y.toNat → y.toNat < B.toNat + c + 4 → M y = M' y) :
    memLoad32 M (B + BitVec.ofNat 32 c) = memLoad32 M' (B + BitVec.ofNat 32 c) :=
  ace_load_eq fun j hj => by
    have e := F.at (c + j) (by omega)
    rw [add_ofNat_assoc]; exact h _ (by omega) (by omega)

theorem acets_bytes {M M' : Word → BitVec 8} {p : Word} {n : Nat} (hp : p.toNat + n < 2 ^ 32)
    (h : ∀ y : Word, p.toNat ≤ y.toNat → y.toNat < p.toNat + n → M y = M' y) :
    memBytes M p n = memBytes M' p n :=
  ace_memBytes_ext fun i hi => by
    have e := acets_tn (a := p) (c := i) (by omega)
    exact h _ (by omega) (by omega)

/-- What `X.Ok` says of the addresses, as numbers. -/
structure AcetsN (X : AceCtx) : Prop where
  blo : 0x3FC801A0 ≤ X.B.toNat
  bhi : X.B.toNat + 0x5A70 ≤ 0x3FCE0000
  bal : X.B.toNat % 16 = 0
  fhi : X.Bf.toNat + 0xB954 ≤ 0x40000000
  fal : X.Bf.toNat % 4 = 0
  lay : X.B.toNat + 0x5A70 ≤ X.Bf.toNat ∨ X.Bf.toNat + 0xB954 ≤ X.B.toNat
  dlo : X.Bf.toNat + 0x4000 ≤ X.D.toNat
  dhi : X.D.toNat + X.json.length ≤ X.Bf.toNat + 0x6800

theorem acets_n {X : AceCtx} (O : X.Ok) : AcetsN X := by
  have F := O.lay.fr
  have hh := O.lay.hi
  have t1 := O.lay.sep.sub (c := 0) (l := 1) (by decide)
  rw [add_ofNat_zero] at t1
  have t2 := O.lay.sep.symm.sub (c := 0) (l := 1) (by decide)
  rw [add_ofNat_zero] at t2
  have s1 := ace_ofSep t1
  have s2 := ace_ofSep t2
  unfold acBufLen at hh s1 s2
  refine ⟨F.lo, F.hi, F.al, by omega, O.lay.al, ?_, O.pre.docLo, O.pre.docHi⟩
  rcases s1 with s1 | s1
  · rcases s2 with s2 | s2
    · exact absurd s1 (by omega)
    · exact .inl s2
  · exact .inr s1

/-- `y` lies outside every range one pass writes: the 0x760 bytes below
`sp + 0x20` (`read_chain`'s frame, `next_element`'s, `copy_from_slice`'s,
and the slots at `sp + 0x10`), the slots at `sp + 0x28`, `read_chain`'s
result at `sp + 0x1320`, the cursor's position, the slice of `keys`,
`keys`'s free part from `fp`, and the entry `[lo, hi)`. -/
def AcetsO (b f fp lo hi y : Nat) : Prop :=
  (y < b + 0x3310 ∨ b + 0x3A70 ≤ y) ∧ (y < b + 0x3A78 ∨ b + 0x3A84 ≤ y) ∧
    (y < b + 0x4D70 ∨ b + 0x4DB0 ≤ y) ∧ (y < b + 0x5820 ∨ b + 0x5824 ≤ y) ∧
    (y < b + 0x5A2C ∨ b + 0x5A34 ≤ y) ∧ (y < fp ∨ f + 0xB840 ≤ y) ∧ (y < lo ∨ hi ≤ y)

macro "acets_o" : tactic => `(tactic| (unfold AcetsO; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega))

theorem AcetsO.wk {b f fp lo hi y : Nat} (h : AcetsO b f fp lo hi y) : AcetsO b f fp 0 0 y :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, .inr (Nat.zero_le _)⟩

/-! ## Loads and stores on the stack -/

section Wp
variable {B : Word} (F : Fr B 0x5A70) {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}
include F

theorem acets_lw {rd rs1 : Fin 32} {o l : Word}
    (h : fetchRel bootMainClosure0Code off = some (.load .lw rd rs1 o, l))
    {c : Nat} (hx : f rs1 + o = B + BitVec.ofNat 32 c) (hc : c % 4 = 0) (hcb : c + 4 ≤ 0x5A70)
    (k : WP bootMainClosure0Code AC Q M (off + l.toNat) (upd f rd (memLoad32 M (B + BitVec.ofNat 32 c)))) :
    WP bootMainClosure0Code AC Q M off f :=
  WP.lw h (by rw [hx]; exact ace_al4 F hc (by omega)) (by rw [hx]; exact k)

theorem acets_lbu {rd rs1 : Fin 32} {o l : Word}
    (h : fetchRel bootMainClosure0Code off = some (.load .lbu rd rs1 o, l))
    {c : Nat} (hx : f rs1 + o = B + BitVec.ofNat 32 c)
    (k : WP bootMainClosure0Code AC Q M (off + l.toNat) (upd f rd ((M (B + BitVec.ofNat 32 c)).zeroExtend 32))) :
    WP bootMainClosure0Code AC Q M off f :=
  WP.lbu h (by rw [hx]; exact k)

theorem acets_sw {rs1 rs2 : Fin 32} {o l : Word}
    (h : fetchRel bootMainClosure0Code off = some (.store .sw rs1 rs2 o, l))
    {c : Nat} (hx : f rs1 + o = B + BitVec.ofNat 32 c) (hc : c % 4 = 0) (hcb : c + 4 ≤ 0x5A70)
    (k : WP bootMainClosure0Code AC Q (memStore32 M (B + BitVec.ofNat 32 c) (f rs2)) (off + l.toNat) f) :
    WP bootMainClosure0Code AC Q M off f :=
  WP.sw h (by rw [hx]; exact ace_al4 F hc (by omega)) (by rw [hx]; exact ace_cs F hcb) (by rw [hx]; exact k)

theorem acets_sb {rs1 rs2 : Fin 32} {o l : Word}
    (h : fetchRel bootMainClosure0Code off = some (.store .sb rs1 rs2 o, l))
    {c : Nat} (hx : f rs1 + o = B + BitVec.ofNat 32 c) (hcb : c + 1 ≤ 0x5A70)
    (k : WP bootMainClosure0Code AC Q (memStore8 M (B + BitVec.ofNat 32 c) ((f rs2).extractLsb' 0 8)) (off + l.toNat) f) :
    WP bootMainClosure0Code AC Q M off f :=
  WP.sb h (by rw [hx]; exact ace_cs F hcb) (by rw [hx]; exact k)

end Wp

/-! ## The registers a pass keeps -/

structure AcetsR (X : AceCtx) (k : Nat) (f : Fin 32 → Word) : Prop where
  rz : f 0 = 0
  rsp : f (2 : Fin 32) = X.B + 0x3A50
  rgp : f (3 : Fin 32) = X.g
  rtp : f (4 : Fin 32) = X.t
  r21 : f (21 : Fin 32) = reg X.K 21
  r25 : f (25 : Fin 32) = reg X.K 25
  r26 : f (26 : Fin 32) = BitVec.ofNat 32 k
  r27 : f (27 : Fin 32) = reg X.K 27

theorem AcetsR.up {X : AceCtx} {k : Nat} {f : Fin 32 → Word} (h : AcetsR X k f) {rd : Fin 32} {v : Word}
    (hr : rd.val ∉ [0, 2, 3, 4, 21, 25, 26, 27]) : AcetsR X k (upd f rd v) := by
  have q : ∀ q : Fin 32, q.val ∈ [0, 2, 3, 4, 21, 25, 26, 27] → upd f rd v q = f q := fun q hq => by
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp only [upd_app, h0, ↓reduceIte]; exact h.rz.symm
    · have : q ≠ rd := fun e => hr (e ▸ hq)
      simp only [upd_app, h0, this, ↓reduceIte]
  exact ⟨by simp only [upd_app, ↓reduceIte, Fin.val_zero], (q 2 (by decide)).trans h.rsp,
    (q 3 (by decide)).trans h.rgp, (q 4 (by decide)).trans h.rtp, (q 21 (by decide)).trans h.r21,
    (q 25 (by decide)).trans h.r25, (q 26 (by decide)).trans h.r26, (q 27 (by decide)).trans h.r27⟩

theorem AcetsR.cl {X : AceCtx} {k : Nat} {f : Fin 32 → Word} (h : AcetsR X k f) {m : Machine} {cl : List (Fin 32)}
    (hc : ∀ q : Fin 32, q.val ∈ [0, 2, 3, 4, 21, 25, 26, 27] → q ∉ cl) : AcetsR X k (clob f m cl) := by
  have q : ∀ q : Fin 32, q.val ∈ [0, 2, 3, 4, 21, 25, 26, 27] → clob f m cl q = f q := fun q hq => by
    simp only [clob_app, hc q hq, ↓reduceIte]
  exact ⟨(q 0 (by decide)).trans h.rz, (q 2 (by decide)).trans h.rsp, (q 3 (by decide)).trans h.rgp,
    (q 4 (by decide)).trans h.rtp, (q 21 (by decide)).trans h.r21, (q 25 (by decide)).trans h.r25,
    (q 26 (by decide)).trans h.r26, (q 27 (by decide)).trans h.r27⟩

/-- Rebuilds `AcetsR` through a chain of `upd`s and `clob`s. -/
macro "acets_hr" : tactic => `(tactic| first
  | assumption
  | (repeat (first | refine AcetsR.up ?_ (by decide) | refine AcetsR.cl ?_ (by decide))); assumption)

theorem acets_0add (x : Word) : (0 : Word) + x = x := BitVec.zero_add x

/-- `rsimp`, then `0 + x` to `x`. -/
macro "acets_z" : tactic => `(tactic| (rsimp <;> try simp only [ev_add, acets_0add]))

/-! ## The state at the end of a pass -/

/-- At `pc`, `P` of the machine, after the closure's invariant. -/
def acetsQ (X : AceCtx) (P : Machine → Prop) : Post := fun pc M f =>
  ∀ n : Machine, n.pc = pc → n.mem = M → (∀ q, reg n q = f q) →
    AcInv X.B X.Bf X.g X.t X.v X.M0 n ∧ (AcFail X.B X.r n ∨ P n)

/-- Where a pass over `rest` ends: at 0x1434 with no items left, or back at
0x123A with one item fewer. -/
def AcetsNext (X : AceCtx) (jr : Json) (fs : List FulcioKey) (ls : List LogKey) (rest : List Json)
    (n : Machine) : Prop :=
  (n.pc = AC + BitVec.ofNat 32 0x1434 ∧ ∃ fp' ts', AceAt X n 0x1434 fp' ∧ AceKeysRead X n fp' fs ls ts') ∨
    (n.pc = AC + BitVec.ofNat 32 0x123A ∧ ∃ j rest', rest = j :: rest' ∧
      ∃ fp' ts', AceAt X n 0x123A fp' ∧ AceTsaInv X n fp' jr fs ls rest' ts')

/-- An equation of words, as one of numbers mod `2 ^ 32`. -/
macro "acets_bv" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
  omega))

/-- `acets_n`'s facts and `keys`'s free part's bounds, for `omega`. -/
macro "acets_nf " o:term:max a:term:max : tactic => `(tactic| (
  have N := acets_n $o; obtain ⟨_, _, _, _, _, _, _, _⟩ := N; have := ($a).fr.lo; have := ($a).fr.hi))

section Mem
variable {X : AceCtx} (O : X.Ok) {n0 : Machine} {off : Nat} {fp : Word} (A : AceAt X n0 off fp)
  {M : Word → BitVec 8} {lo hi : Nat}
  (hm : ∀ x : Word, AcetsO X.B.toNat X.Bf.toNat fp.toNat lo hi x.toNat → M x = n0.mem x)
  (hx1 : hi ≤ lo ∨ X.B.toNat + 0x42E0 ≤ lo) (hx2 : hi ≤ lo ∨ hi ≤ X.B.toNat + 0x43E0)
include O A hm hx1 hx2

theorem acets_out' {x : Word} (h1 : x.toNat < X.B.toNat ∨ X.B.toNat + 0x5A70 ≤ x.toNat)
    (h2 : x.toNat < X.Bf.toNat + 0x6800 ∨ X.Bf.toNat + 0xB840 ≤ x.toNat) : M x = n0.mem x := by
  have := A.fr.lo
  exact hm x (by acets_o)

theorem acets_mout : ∀ x, Sep x 1 X.B 0x5A70 → Sep x 1 X.Bf acBufLen → M x = X.M0 x := fun x h1 h2 => by
  have s2 := ace_ofSep h2
  unfold acBufLen at s2
  exact (acets_out' O A hm hx1 hx2 (ace_ofSep h1) (by omega)).trans (A.inv.out x h1 h2)

theorem acets_saves : ∀ k, k < 13 → memLoad32 M (X.B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = X.v k := by
  acets_nf O A
  intro k hk
  rw [← A.inv.saves k hk]
  exact ace_load_eq fun j hj => by
    have e := O.lay.fr.at (0x5A6C - 4 * k + j) (by omega)
    rw [add_ofNat_assoc]
    exact hm _ (by rw [e]; acets_o)

theorem acets_inv {n : Machine} (hn : n.mem = M) (h2 : reg n (2 : Fin 32) = X.B + 0x3A50)
    (h3 : reg n (3 : Fin 32) = X.g) (h4 : reg n (4 : Fin 32) = X.t) : AcInv X.B X.Bf X.g X.t X.v X.M0 n :=
  ⟨h2, h3, h4, by rw [hn]; exact acets_saves O A hm hx1 hx2, by rw [hn]; exact acets_mout O A hm hx1 hx2⟩

theorem acets_code : CodeIn M AC bootMainClosure0Code := fun i hi => by
  have hAC := ace_AC
  acets_nf O A
  have e : (AC + BitVec.ofNat 32 i).toNat = AC.toNat + i := acets_tn (by omega)
  rw [acets_out' O A hm hx1 hx2 (.inr (by rw [e]; omega)) (.inr (by rw [e]; omega))]
  exact A.code i hi

theorem acets_kept : ∀ x, AceKept X.B X.Bf x → M x = X.K.mem x := by
  acets_nf O A
  intro x hx
  rw [← A.keep.mem x hx]
  have N := acets_n O
  have ⟨_, _, _, _, _, _, _, _⟩ := N
  rcases hx with ⟨h1, h2⟩ | ⟨k, hk, rfl⟩
  · have e : (X.Bf + 0x6800 : Word).toNat = X.Bf.toNat + 0x6800 := acets_tn (c := 0x6800) (by omega)
    have s2 := ace_ofSep h2
    rw [e] at s2
    exact acets_out' O A hm hx1 hx2 (ace_ofSep h1) (by omega)
  · have e : (acSlot X.B k).toNat = X.B.toNat + (0x3A50 + k) := O.lay.fr.at _ (by omega)
    have := A.fr.lo
    exact hm _ (by rw [e]; acets_o)

theorem acets_exp {n : Machine} (hn : n.mem = M) : AceExpiry X.B X.K n := by
  acets_nf O A
  have F := O.lay.fr
  have := A.exp
  have e : acSlot X.B 0x20 + 4 = X.B + BitVec.ofNat 32 0x3A74 := by simp only [acSlot]; bv_omega
  have l1 : memLoad32 M (X.B + BitVec.ofNat 32 0x3A70) = memLoad32 n0.mem (X.B + BitVec.ofNat 32 0x3A70) :=
    acets_ld F (by decide) fun y h1 h2 => hm y (by acets_o)
  have l2 : memLoad32 M (X.B + BitVec.ofNat 32 0x3A74) = memLoad32 n0.mem (X.B + BitVec.ofNat 32 0x3A74) :=
    acets_ld F (by decide) fun y h1 h2 => hm y (by acets_o)
  unfold AceExpiry aceU64 at this ⊢
  rw [hn, e, l2, ← e, show acSlot X.B 0x20 = X.B + BitVec.ofNat 32 0x3A70 from rfl, l1]
  exact this

theorem acets_res : memLoad32 M (acSlot X.B 0x40) = X.r := by
  rw [← O.pre.res]
  exact ace_load_eq fun j hj => acets_kept O A hm hx1 hx2 _
    (.inr ⟨0x40 + j, .inl ⟨by omega, by omega⟩, by
      rw [ace_slot]; show _ = X.B + BitVec.ofNat 32 (0x3A50 + (0x40 + j)); rw [Nat.add_assoc]⟩)

theorem acets_env : AcExtractEnv M := O.env M (acets_mout O A hm hx1 hx2)

theorem acets_doc : memBytes M X.D X.json.length = X.json := by
  acets_nf O A
  have N := acets_n O
  have ⟨_, _, _, _, _, _, _, _⟩ := N
  refine (ace_memBytes_ext (M := X.K.mem) fun i hi => acets_kept O A hm hx1 hx2 _ (.inl ⟨?_, ?_⟩)).trans O.pre.doc
  · have e := acets_tn (a := X.D) (c := i) (by omega)
    exact acets_sep (by omega) (by omega) (by omega)
  · have e := acets_tn (a := X.D) (c := i) (by omega)
    have e2 : (X.Bf + 0x6800 : Word).toNat = X.Bf.toNat + 0x6800 := acets_tn (c := 0x6800) (by omega)
    exact acets_sep (by rw [e, e2]; omega) (by omega) (by rw [e2]; omega)

theorem acets_at {n : Machine} {off' : Nat} {fp' : Word} (hn : n.mem = M) (hpc : n.pc = AC + BitVec.ofNat 32 off')
    (h2 : reg n (2 : Fin 32) = X.B + 0x3A50) (h3 : reg n (3 : Fin 32) = X.g) (h4 : reg n (4 : Fin 32) = X.t)
    (h21 : reg n (21 : Fin 32) = reg X.K 21) (h25 : reg n (25 : Fin 32) = reg X.K 25)
    (h27 : reg n (27 : Fin 32) = reg X.K 27) (hf1 : fp.toNat ≤ fp'.toNat) (hf2 : fp'.toNat ≤ X.Bf.toNat + 0xB840)
    (hptr : memLoad32 M (X.B + BitVec.ofNat 32 0x5A2C) = fp')
    (hlen : memLoad32 M (X.B + BitVec.ofNat 32 0x5A30) = BitVec.ofNat 32 (X.Bf.toNat + 0xB840 - fp'.toNat)) :
    AceAt X n off' fp' := by
  have := A.fr.lo
  refine ⟨by rw [hn]; exact acets_code O A hm hx1 hx2, ⟨hpc, rfl, fun _ => rfl⟩, acets_inv O A hm hx1 hx2 hn h2 h3 h4,
    ⟨by rw [hn]; exact hptr, by rw [hn]; exact hlen, by omega, hf2⟩,
    ⟨fun x hx => by rw [hn]; exact acets_kept O A hm hx1 hx2 x hx, fun q hq => ?_⟩, acets_exp O A hm hx1 hx2 hn⟩
  have : q = 21 ∨ q = 25 ∨ q = 27 := by revert hq; revert q; decide
  rcases this with rfl | rfl | rfl
  · exact h21
  · exact h25
  · exact h27

/-- From 0x1A6A, with the code to log in `s0`, to the exit at 0x7D6. -/
theorem acets_f1A6A {f : Fin 32 → Word} {P : Machine → Prop} (hz : f 0 = 0) (h2 : f 2 = X.B + 0x3A50)
    (h3 : f 3 = X.g) (h4 : f 4 = X.t) (he : (f 8 &&& 0xFF).toNat < 0x27) :
    WP bootMainClosure0Code AC (acetsQ X P) M 0x1A6A f := by
  refine WP.alu ac_at_1a6a ?_
  refine WP.jal ac_at_1a6c (by decide) ?_
  refine WP.here fun n hpc hn hr => ?_
  refine ⟨acets_inv O A hm hx1 hx2 hn (by rw [hr]; rsimp; exact h2) (by rw [hr]; rsimp; exact h3)
    (by rw [hr]; rsimp; exact h4), .inl (.inr (.inr (.inl ⟨by rw [hpc]; rfl, by rw [hn]; exact acets_res O A hm hx1 hx2, ?_⟩)))⟩
  rw [hr]; rsimp; rw [hz, ev_add, show (0 : Word) + f 8 = f 8 from BitVec.zero_add _]; exact he

/-- 0xC3A logs `0x13`: `keys` has no room. -/
theorem acets_fC3A {f : Fin 32 → Word} {P : Machine → Prop} (hz : f 0 = 0) (h2 : f 2 = X.B + 0x3A50)
    (h3 : f 3 = X.g) (h4 : f 4 = X.t) : WP bootMainClosure0Code AC (acetsQ X P) M 0xC3A f := by
  refine WP.aluImm ac_at_c3a ?_; wn
  refine WP.jal ac_at_c3c (by decide) ?_; wn
  exact acets_f1A6A O A hm hx1 hx2 (by rsimp) (by rsimp; exact h2) (by rsimp; exact h3)
    (by rsimp; exact h4) (by rsimp <;> first | decide | (rw [hz]; decide))

end Mem

/-! ## Values the pass computes -/

theorem acets_bltu (a b : Word) : branchTaken .bltu a b = decide (a.toNat < b.toNat) := rfl
theorem acets_beq (a b : Word) : branchTaken .beq a b = (a == b) := rfl
theorem acets_bne (a b : Word) : branchTaken .bne a b = (a != b) := rfl
theorem acets_ev_sll (a b : Word) : aluEval .sll a b = a <<< (b.toNat % 32) := rfl
theorem acets_ev_srl (a b : Word) : aluEval .srl a b = a >>> (b.toNat % 32) := rfl
theorem acets_ev_sub (a b : Word) : aluEval .sub a b = a - b := rfl
theorem acets_ev_or (a b : Word) : aluEval .or a b = a ||| b := rfl
theorem acets_ev_and (a b : Word) : aluEval .and a b = a &&& b := rfl

theorem acets_om (x : Nat) : BitVec.ofNat 32 (x % 2 ^ 32) = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

theorem acets_addN (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem acets_subN {a b : Nat} (ha : a < 2 ^ 32) (hb : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem acets_ltN {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    branchTaken .bltu (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = decide (a < b) := by
  rw [acets_bltu, Sv.ofNat_toNat_lt ha, Sv.ofNat_toNat_lt hb]

theorem acets_bneT {n : Nat} (h : branchTaken .bne (BitVec.ofNat 32 n) 0 = true) : n % 2 ^ 32 ≠ 0 := by
  intro e
  rw [acets_bne, show BitVec.ofNat 32 n = 0 from BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact e)] at h
  exact absurd h (by decide)

theorem acets_bneF {n : Nat} (h : branchTaken .bne (BitVec.ofNat 32 n) 0 = false) : n % 2 ^ 32 = 0 := by
  rw [acets_bne, bne] at h
  have h' : (BitVec.ofNat 32 n == 0) = true := by
    revert h; cases (BitVec.ofNat 32 n == 0) <;> decide
  have := congrArg BitVec.toNat (eq_of_beq h')
  rwa [BitVec.toNat_ofNat] at this

theorem acets_beqT {a : Word} (h : branchTaken .beq a 0 = true) : a = 0 := by
  rw [acets_beq] at h; exact eq_of_beq h

theorem acets_beqF {a : Word} (h : branchTaken .beq a 0 = false) : a ≠ 0 := by
  intro e; rw [e] at h; exact absurd h (by decide)

theorem acets_beqTN {n : Nat} (h : branchTaken .beq (BitVec.ofNat 32 n) 0 = true) : n % 2 ^ 32 = 0 := by
  have := congrArg BitVec.toNat (acets_beqT h)
  rwa [BitVec.toNat_ofNat] at this

/-- The byte that `sb` stores. -/
theorem acets_byte (x : Word) : (x.extractLsb' 0 8).toNat = x.toNat % 256 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

theorem acets_and8 (x : Word) : (x &&& 0xFF).extractLsb' 0 8 = x.extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hi, decide_true, Bool.true_and]
  have : (0xFF : Word).getLsbD (0 + i) = true := by
    have : i < 8 := hi
    revert i; decide
  rw [this, Bool.and_true]

theorem acets_bLow {L : Nat} : ((BitVec.ofNat 32 L).extractLsb' 0 8).toNat = L % 256 := by
  rw [acets_byte, BitVec.toNat_ofNat]; omega

theorem acets_bAnd {L : Nat} : ((aluEval .and (BitVec.ofNat 32 L) 0xFF).extractLsb' 0 8).toNat = L % 256 := by
  rw [acets_ev_and, acets_and8, acets_bLow]

theorem acets_bOr {L : Nat} (hL : L < 2 ^ 16) :
    ((aluEval .or (BitVec.ofNat 32 (L / 256)) (BitVec.ofNat 32 (L * 256))).extractLsb' 0 8).toNat = L / 256 := by
  rw [acets_ev_or, acets_byte, BitVec.toNat_or]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show L / 256 < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show L * 256 < 2 ^ 32 by omega)]
  rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.or_mod_two_pow, Nat.mul_mod_left]
  simp only [Nat.or_zero]; omega

/-- `L` and 0x500 in one word, as 0x12C4 and 0x12C8 build it. -/
theorem acets_vA16 {L : Nat} (hL : L < 2 ^ 16) :
    aluEval .srl (aluEval .add (aluEval .sll (BitVec.ofNat 32 L) 0x10) 0x500) 0x10 = BitVec.ofNat 32 L := by
  show (BitVec.ofNat 32 L <<< 16 + 0x500) >>> 16 = _; bv_omega

theorem acets_vA23 {L : Nat} (hL : L < 2 ^ 16) :
    aluEval .srl (aluEval .add (aluEval .sll (BitVec.ofNat 32 L) 0x10) 0x500) 0x17 =
      BitVec.ofNat 32 (L / 128) := by
  show (BitVec.ofNat 32 L <<< 16 + 0x500) >>> 23 = _; bv_omega

theorem acets_vA24 {L : Nat} (hL : L < 2 ^ 16) :
    aluEval .srl (aluEval .add (aluEval .sll (BitVec.ofNat 32 L) 0x10) 0x500) 0x18 =
      BitVec.ofNat 32 (L / 256) := by
  show (BitVec.ofNat 32 L <<< 16 + 0x500) >>> 24 = _; bv_omega

theorem acets_vA1 {L : Nat} (hL : L < 2 ^ 16) :
    aluEval .and (aluEval .add (aluEval .sll (BitVec.ofNat 32 L) 0x10) 0x500) 1 = 0 := by
  show (BitVec.ofNat 32 L <<< 16 + 0x500) &&& 1 = 0
  have e : (BitVec.ofNat 32 L <<< 16) + 0x500 = BitVec.ofNat 32 (L * 65536 + 0x500) := by bv_omega
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show BitVec.toNat (1 : Word) = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
  show _ = 0
  omega

theorem acets_vS16 {L : Nat} (hL : L < 2 ^ 32) :
    aluEval .srl (BitVec.ofNat 32 L) 0x10 = BitVec.ofNat 32 (L / 2 ^ 16) := by
  show BitVec.ofNat 32 L >>> 16 = _; bv_omega

theorem acets_vS8 {L : Nat} (hL : L < 2 ^ 16) :
    aluEval .sll (BitVec.ofNat 32 L) 0x8 = BitVec.ofNat 32 (L * 256) := by
  show BitVec.ofNat 32 L <<< 8 = _; bv_omega

/-- The bytes at `p` are `l` when each one is. -/
theorem acets_mbl {M : Word → BitVec 8} {p : Word} {l : Bytes}
    (h : ∀ i, i < l.length → (M (p + BitVec.ofNat 32 i)).toNat = l[i]!) : memBytes M p l.length = l := by
  apply List.ext_getElem (memBytes_length _ _ _)
  intro i h1 h2
  simp only [memBytes, List.getElem_map, List.getElem_range]
  rw [h i h2, getElem!_pos l i h2]

/-! ## `copy_from_slice` -/

theorem acets_cpo {M M' : Word → BitVec 8} {F dst src y : Word} {N : Nat}
    (W : Out (copyBytes M dst src N) M' F 16) (h1 : y.toNat < F.toNat ∨ F.toNat + 16 ≤ y.toNat)
    (h2 : y.toNat < dst.toNat ∨ dst.toNat + N ≤ y.toNat) (hF : F.toNat + 16 ≤ 2 ^ 32)
    (hd : dst.toNat + N ≤ 2 ^ 32) : M' y = M y := by
  have := y.isLt
  rw [W y (acets_sep (by omega) (by omega) hF), copyBytes_sep (acets_sep (by omega) hd (by omega)) (Nat.le_refl _)]

theorem acets_cpi {M M' : Word → BitVec 8} {F dst src : Word} {N i : Nat}
    (W : Out (copyBytes M dst src N) M' F 16) (hi : i < N) (hN : N < 2 ^ 32)
    (h1 : (dst + BitVec.ofNat 32 i).toNat < F.toNat ∨ F.toNat + 16 ≤ (dst + BitVec.ofNat 32 i).toNat)
    (hF : F.toNat + 16 ≤ 2 ^ 32) : M' (dst + BitVec.ofNat 32 i) = M (src + BitVec.ofNat 32 i) := by
  have := (dst + BitVec.ofNat 32 i).isLt
  rw [W _ (acets_sep (by omega) (by omega) hF), copyBytes_at hi hN]

theorem acets_cfs {X : AceCtx} (O : X.Ok) {M : Word → BitVec 8} (E : AcExtractEnv M) {Q : Post} {off : Nat}
    {f : Fin 32 → Word} {hi lo dst src : Word} {N : Nat}
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra hi, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : AC + BitVec.ofNat 32 off + hi + lo = BCW) (hev : (off + 8) % 2 = 0)
    (h0 : f a0 = dst) (ha1 : f a1 = BitVec.ofNat 32 N) (ha2 : f a2 = src) (ha3 : f a3 = BitVec.ofNat 32 N)
    (hsp : f (2 : Fin 32) = X.B + 0x3A50)
    (hd : dst.toNat + N ≤ 0x40000000) (hs : src.toNat + N ≤ 0x40000000)
    (hdF : dst.toNat + N ≤ X.B.toNat + 0x3A40 ∨ X.B.toNat + 0x3A50 ≤ dst.toNat)
    (hsF : src.toNat + N ≤ X.B.toNat + 0x3A40 ∨ X.B.toNat + 0x3A50 ≤ src.toNat)
    (hds : dst.toNat + N ≤ src.toNat ∨ src.toNat + N ≤ dst.toNat)
    (k : ∀ m2 : Machine, Out (copyBytes M dst src N) m2.mem (X.B + BitVec.ofNat 32 0x3A40) 16 →
      WP bootMainClosure0Code AC Q m2.mem (off + 8)
        (clob (upd f ra (AC + BitVec.ofNat 32 (off + 8))) m2 rkCfsClob)) :
    WP bootMainClosure0Code AC Q M off f := by
  have F := O.lay.fr
  have eF := F.at 0x3A40 (by decide)
  have := F.hi
  refine WP.callCfs h1 h2 htgt hev E.copy E.stub ⟨E.body, lowSep hd (by decide) (by decide),
    ace_hs F (by decide) (by decide) (by decide), acets_sep (by rw [eF]; omega) (by omega) (by rw [eF]; omega),
    acets_sep (by rw [eF]; omega) (by omega) (by rw [eF]; omega), acets_sep hds (by omega) (by omega),
    ace_al4 F (by decide) (by decide), by rw [eF]; omega, by omega, by omega⟩ h0 ha1 ha2 ha3
    (by rw [hsp]; bv_omega) (ace_cs F (by decide)) (lowSep hd ace_AC.1 ace_AC.2) k

/-! ## Stores on the stack, for `simp` -/

section St
variable {B : Word} (F : Fr B 0x5A70) {M : Word → BitVec 8}
include F

theorem acets_ls {c d : Nat} {v : Word} (h : c + 4 ≤ d ∨ d + 4 ≤ c) (hc : c + 4 ≤ 0x5A70) (hd : d + 4 ≤ 0x5A70) :
    memLoad32 (memStore32 M (B + BitVec.ofNat 32 c) v) (B + BitVec.ofNat 32 d) =
      memLoad32 M (B + BitVec.ofNat 32 d) :=
  memLoad32_store32_sep (ace_sepB' F h hc hd)

theorem acets_l8 {c d : Nat} {v : BitVec 8} (h : c + 1 ≤ d ∨ d + 4 ≤ c) (hc : c + 1 ≤ 0x5A70)
    (hd : d + 4 ≤ 0x5A70) :
    memLoad32 (memStore8 M (B + BitVec.ofNat 32 c) v) (B + BitVec.ofNat 32 d) =
      memLoad32 M (B + BitVec.ofNat 32 d) :=
  memLoad32_store8_sep (ace_sepB' F h hc hd)

theorem acets_g32 {c : Nat} {v y : Word} (hc : c + 4 ≤ 0x5A70)
    (h : y.toNat < B.toNat + c ∨ B.toNat + c + 4 ≤ y.toNat) : memStore32 M (B + BitVec.ofNat 32 c) v y = M y := by
  have := F.hi
  have := y.isLt
  have e := F.at c (by omega)
  exact memStore32_get_sep (acets_sep (by rw [e]; omega) (by rw [e]; omega) (by omega))

theorem acets_g8 {c : Nat} {v : BitVec 8} {y : Word} (hc : c + 1 ≤ 0x5A70)
    (h : y.toNat < B.toNat + c ∨ B.toNat + c + 1 ≤ y.toNat) : memStore8 M (B + BitVec.ofNat 32 c) v y = M y :=
  memStore8_ne fun e => by rw [e, F.at c (by omega)] at h; omega

theorem acets_subFr {c n : Nat} (hc : c % 16 = 0) (h1 : 0x1A0 ≤ c) (h2 : c + n ≤ 0x5A70) :
    Fr (B + BitVec.ofNat 32 c) n := by
  have e := F.at c (by omega)
  refine ⟨by rw [e]; have := F.al; omega, by rw [e]; have := F.lo; omega, by rw [e]; have := F.hi; omega, ?_⟩
  have h := F.dsep.sub (c := c) (l := n + 0x1A0) (by omega)
  have e2 : B + 0xFFFFFE60 + BitVec.ofNat 32 c = B + BitVec.ofNat 32 c + 0xFFFFFE60 := by
    rw [BitVec.add_assoc, BitVec.add_comm 0xFFFFFE60, ← BitVec.add_assoc]
  rwa [e2] at h

/-- A range of the stack and one outside it lie apart. -/
theorem acets_sepO {c n : Nat} {y : Word} {k : Nat} (hc : c + n ≤ 0x5A70)
    (h : y.toNat + k ≤ B.toNat + c ∨ B.toNat + c + n ≤ y.toNat) (hy : y.toNat + k ≤ 2 ^ 32) :
    Sep (B + BitVec.ofNat 32 c) n y k := by
  have := F.hi
  have e := F.at c (by omega)
  exact acets_sep (by rw [e]; omega) (by rw [e]; omega) hy

theorem acets_s8 {c d : Nat} {v : BitVec 8} (h : c ≠ d) (hc : c < 0x5A70) (hd : d < 0x5A70) :
    memStore8 M (B + BitVec.ofNat 32 c) v (B + BitVec.ofNat 32 d) = M (B + BitVec.ofNat 32 d) :=
  memStore8_ne fun e => h (by
    have := congrArg BitVec.toNat e
    rw [F.at d (by omega), F.at c (by omega)] at this
    omega)

/-- The entry that the seven stores from 0x13E6 write at `sp + c`. -/
theorem acets_entry {Bf fp p kp : Word} {c : Nat} {name key : Bytes} {w : Window}
    (hc : c + 0x1C ≤ 0x5A70)
    (hbuf : ∀ y : Word, Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp.toNat →
      y.toNat < B.toNat ∨ B.toNat + 0x5A70 ≤ y.toNat)
    (hp0 : Bf.toNat + 0x4000 ≤ p.toNat) (hp1 : p.toNat + name.length ≤ fp.toNat)
    (hname : memBytes M p name.length = name) (hk0 : Bf.toNat + 0x4000 ≤ kp.toNat)
    (hk1 : kp.toNat + 0x61 ≤ fp.toNat) (hkey : memBytes M kp 0x61 = key)
    (hnb : w.notBefore < 2 ^ 64) (hna : w.notAfter < 2 ^ 64) :
    AceEntryIn Bf fp (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M
      (B + BitVec.ofNat 32 c) p) (B + BitVec.ofNat 32 (c + 4)) (BitVec.ofNat 32 name.length))
      (B + BitVec.ofNat 32 (c + 8)) (BitVec.ofNat 32 (w.notBefore % 2 ^ 32)))
      (B + BitVec.ofNat 32 (c + 0xC)) (BitVec.ofNat 32 (w.notBefore / 2 ^ 32)))
      (B + BitVec.ofNat 32 (c + 0x10)) (BitVec.ofNat 32 (w.notAfter % 2 ^ 32)))
      (B + BitVec.ofNat 32 (c + 0x14)) (BitVec.ofNat 32 (w.notAfter / 2 ^ 32)))
      (B + BitVec.ofNat 32 (c + 0x18)) kp) (B + BitVec.ofNat 32 c) name key 0x61 w := by
  have := F.hi
  have := fp.isLt
  have hl : name.length < 2 ^ 32 := by omega
  have e4 : B + BitVec.ofNat 32 c + 4 = B + BitVec.ofNat 32 (c + 4) := add_ofNat_assoc B c 4
  have e8 : B + BitVec.ofNat 32 c + 8 = B + BitVec.ofNat 32 (c + 8) := add_ofNat_assoc B c 8
  have eC : B + BitVec.ofNat 32 (c + 8) + 4 = B + BitVec.ofNat 32 (c + 0xC) := by
    rw [show c + 0xC = c + 8 + 4 by omega]; exact add_ofNat_assoc B (c + 8) 4
  have e10 : B + BitVec.ofNat 32 c + 0x10 = B + BitVec.ofNat 32 (c + 0x10) := add_ofNat_assoc B c 0x10
  have e14 : B + BitVec.ofNat 32 (c + 0x10) + 4 = B + BitVec.ofNat 32 (c + 0x14) := by
    rw [show c + 0x14 = c + 0x10 + 4 by omega]; exact add_ofNat_assoc B (c + 0x10) 4
  have e18 : B + BitVec.ofNat 32 c + 0x18 = B + BitVec.ofNat 32 (c + 0x18) := add_ofNat_assoc B c 0x18
  have hb : ∀ {q : Word} {n : Nat}, Bf.toNat + 0x4000 ≤ q.toNat → q.toNat + n ≤ fp.toNat →
      memBytes (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M
        (B + BitVec.ofNat 32 c) p) (B + BitVec.ofNat 32 (c + 4)) (BitVec.ofNat 32 name.length))
        (B + BitVec.ofNat 32 (c + 8)) (BitVec.ofNat 32 (w.notBefore % 2 ^ 32)))
        (B + BitVec.ofNat 32 (c + 0xC)) (BitVec.ofNat 32 (w.notBefore / 2 ^ 32)))
        (B + BitVec.ofNat 32 (c + 0x10)) (BitVec.ofNat 32 (w.notAfter % 2 ^ 32)))
        (B + BitVec.ofNat 32 (c + 0x14)) (BitVec.ofNat 32 (w.notAfter / 2 ^ 32)))
        (B + BitVec.ofNat 32 (c + 0x18)) kp) q n = memBytes M q n := fun h1 h2 =>
    acets_bytes (by omega) fun y h3 h4 => by
      have := hbuf y (by omega) (by omega)
      simp (disch := omega) only [acets_g32 F]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨hnb, ?_, ?_⟩, ⟨hna, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · simp (disch := omega) only [acets_ls F, memLoad32_store32_same]; exact hp0
  · rw [e4]; simp (disch := omega) only [acets_ls F, memLoad32_store32_same]
    rw [Sv.ofNat_toNat_lt hl]; exact hp1
  · rw [e4]; simp (disch := omega) only [acets_ls F, memLoad32_store32_same]
    rw [Sv.ofNat_toNat_lt hl, hb hp0 hp1, hname]
  · rw [e8]; simp (disch := omega) only [acets_ls F, memLoad32_store32_same]; exact acets_om _
  · rw [e8, eC]; simp (disch := omega) only [acets_ls F, memLoad32_store32_same]
  · rw [e10]; simp (disch := omega) only [acets_ls F, memLoad32_store32_same]; exact acets_om _
  · rw [e10, e14]; simp (disch := omega) only [acets_ls F, memLoad32_store32_same]
  · rw [e18]; simp (disch := omega) only [acets_ls F, memLoad32_store32_same]; exact hk0
  · rw [e18]; simp (disch := omega) only [acets_ls F, memLoad32_store32_same]; exact hk1
  · rw [e18]; simp (disch := omega) only [acets_ls F, memLoad32_store32_same]
    rw [hb hk0 hk1, hkey]

end St

/-! ## The arrays -/

theorem acets_entryMono {Bf fp fp' : Word} {M : Word → BitVec 8} {e : Word} {name key : Bytes} {n : Nat}
    {w : Window} (h : AceEntryIn Bf fp M e name key n w) (hf : fp.toNat ≤ fp'.toNat) :
    AceEntryIn Bf fp' M e name key n w :=
  ⟨⟨h.name.1, by have := h.name.2.1; omega, h.name.2.2⟩, h.notBefore, h.notAfter,
    ⟨h.key.1, by have := h.key.2.1; omega, h.key.2.2⟩⟩

theorem acets_arrMv {α : Type} {Bf fp fp' : Word} {M M' : Word → BitVec 8} {a : Word} {cap : Nat}
    {l : List α} {nm ky : α → Bytes} {n : Nat} {win : α → Window}
    (h : SvArrayAt M a cap l fun e k => AceEntryIn Bf fp M e (nm k) (ky k) n (win k))
    (hs : ∀ c, c < 0x20 * cap → M' (a + BitVec.ofNat 32 c) = M (a + BitVec.ofNat 32 c))
    (hb : ∀ y : Word, Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp.toNat → M' y = M y)
    (hf : fp.toNat ≤ fp'.toNat) :
    SvArrayAt M' a cap l fun e k => AceEntryIn Bf fp' M' e (nm k) (ky k) n (win k) := by
  obtain ⟨h1, h2, h3⟩ := ace_array_move (M' := M') (a' := a) h hs hb
  exact ⟨h1, fun i hi => acets_entryMono (h2 i hi) hf, h3⟩

/-- The array with one more key, written at its end. -/
theorem acets_snoc {Bf fp fp' : Word} {M M' : Word → BitVec 8} {a : Word} {ts : List TsaKey} {tk : TsaKey}
    (h : AceTsasAt Bf fp M a ts) (hk : ts.length < 8) (hf : fp.toNat ≤ fp'.toNat)
    (hs : ∀ c, c < 0x100 → c < 0x20 * ts.length ∨ 0x20 * ts.length + 0x20 ≤ c →
      M' (a + BitVec.ofNat 32 c) = M (a + BitVec.ofNat 32 c))
    (hb : ∀ y : Word, Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp.toNat → M' y = M y)
    (he : AceEntryIn Bf fp' M' (a + BitVec.ofNat 32 (0x20 * ts.length)) tk.signerId tk.publicKey 0x61
      tk.window) :
    AceTsasAt Bf fp' M' a (ts ++ [tk]) := by
  obtain ⟨hl, hi, hz⟩ := h
  refine ⟨by rw [List.length_append, List.length_singleton]; omega, fun i hi' => ?_, fun i hi1 hi2 => ?_⟩
  · have hi'' := hi'
    rw [List.length_append, List.length_singleton] at hi''
    rcases Nat.lt_or_ge i ts.length with hlt | hge
    · rw [List.getElem_append_left hlt]
      refine acets_entryMono ((hi i hlt).move (fun c hc => ?_) hb) hf
      rw [add_ofNat_assoc]
      exact hs _ (by omega) (.inl (by omega))
    · have e : i = ts.length := by omega
      subst e
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
      exact he
  · rw [List.length_append, List.length_singleton] at hi1
    refine (ace_load_eq fun j hj => ?_).trans (hz i (by omega) hi2)
    rw [add_ofNat_assoc]
    exact hs _ (by omega) (.inr (by omega))

/-! ## One pass -/

/-- The pass over the item `j`, before `rest`: `n0` is the machine at
0x123A, `AceTsaInv` holds there, and `next_element` gave the `l` bytes at
`q` and moved the cursor to `a`. -/
structure AcetsC (X : AceCtx) (n0 : Machine) (fp : Word) (jr : Json) (fs : List FulcioKey) (ls : List LogKey)
    (j : Json) (rest : List Json) (ts : List TsaKey) (q : Word) (l a : Nat) : Prop where
  at0 : AceAt X n0 0x123A fp
  inv : AceTsaInv X n0 fp jr fs ls (j :: rest) ts
  cur : ∃ p l', memLoad32 n0.mem (acSlot X.B 0x1DC8) = p ∧
    memLoad32 n0.mem (acSlot X.B 0x1DC8 + 4) = BitVec.ofNat 32 l' ∧ a < 2 ^ 32 ∧ X.D.toNat ≤ p.toNat ∧
    p.toNat - X.D.toNat + l' ≤ X.json.length ∧
    ElementsFrom false ((X.json.drop (p.toNat - X.D.toNat)).take l') a rest
  qlo : X.D.toNat ≤ q.toNat
  qhi : q.toNat + l ≤ X.D.toNat + X.json.length
  jv : JVal false (memBytes n0.mem q l) j

/-- The memory after `read_chain`, from 0x12F4 to 0x13A8: `read_chain`'s
copy of `keys`'s free part ends at `fp1`, and holds the issuer at `ip`,
the serial number at `sq`, and the key at `kp`; the window and the key's
address are in the slots at `sp + 0x18` to `sp + 0x30`. -/
structure AcetsM (X : AceCtx) (n0 : Machine) (fp : Word) (M : Word → BitVec 8) (a : Nat) (fp1 ip sq kp : Word)
    (iss ser key : Bytes) (w : Window) : Prop where
  lo : X.Bf.toNat + 0x6800 ≤ fp.toNat
  f0 : fp.toNat ≤ fp1.toNat
  f1 : fp1.toNat ≤ X.Bf.toNat + 0xB840
  i0 : fp.toNat ≤ ip.toNat
  i1 : ip.toNat + iss.length ≤ fp1.toNat
  s0 : fp.toNat ≤ sq.toNat
  s1 : sq.toNat + ser.length ≤ fp1.toNat
  k0 : fp.toNat ≤ kp.toNat
  k1 : kp.toNat + 0x61 ≤ fp1.toNat
  nb : w.notBefore < 2 ^ 64
  na : w.notAfter < 2 ^ 64
  hm : ∀ x : Word, AcetsO X.B.toNat X.Bf.toNat fp.toNat 0 0 x.toNat → M x = n0.mem x
  s14 : memLoad32 M (X.B + BitVec.ofNat 32 0x3A64) = ip
  pos : memLoad32 M (X.B + BitVec.ofNat 32 0x5820) = BitVec.ofNat 32 a
  hiss : memBytes M ip iss.length = iss
  hser : memBytes M sq ser.length = ser
  hkey : memBytes M kp 0x61 = key
  w18 : memLoad32 M (X.B + BitVec.ofNat 32 0x3A68) = BitVec.ofNat 32 (w.notBefore / 2 ^ 32)
  w1C : memLoad32 M (X.B + BitVec.ofNat 32 0x3A6C) = BitVec.ofNat 32 (w.notBefore % 2 ^ 32)
  w28 : memLoad32 M (X.B + BitVec.ofNat 32 0x3A78) = BitVec.ofNat 32 (w.notAfter % 2 ^ 32)
  w2C : memLoad32 M (X.B + BitVec.ofNat 32 0x3A7C) = BitVec.ofNat 32 (w.notAfter / 2 ^ 32)
  w30 : memLoad32 M (X.B + BitVec.ofNat 32 0x3A80) = kp

/-- At 0x12A0: `AcetsM` before the slots at `sp + 0x14` to `sp + 0x2C` are
written, with `read_chain`'s result at `sp + 0x1320` instead, and `keys`'s
slice at `fp1`. -/
structure AcetsK (X : AceCtx) (n0 : Machine) (fp : Word) (M : Word → BitVec 8) (a : Nat) (fp1 ip sq kp : Word)
    (iss ser key : Bytes) (w : Window) : Prop where
  lo : X.Bf.toNat + 0x6800 ≤ fp.toNat
  f0 : fp.toNat ≤ fp1.toNat
  f1 : fp1.toNat ≤ X.Bf.toNat + 0xB840
  i0 : fp.toNat ≤ ip.toNat
  i1 : ip.toNat + iss.length ≤ fp1.toNat
  s0 : fp.toNat ≤ sq.toNat
  s1 : sq.toNat + ser.length ≤ fp1.toNat
  k0 : fp.toNat ≤ kp.toNat
  k1 : kp.toNat + 0x61 ≤ fp1.toNat
  nb : w.notBefore < 2 ^ 64
  na : w.notAfter < 2 ^ 64
  hm : ∀ x : Word, AcetsO X.B.toNat X.Bf.toNat fp.toNat 0 0 x.toNat → M x = n0.mem x
  pos : memLoad32 M (X.B + BitVec.ofNat 32 0x5820) = BitVec.ofNat 32 a
  hiss : memBytes M ip iss.length = iss
  hser : memBytes M sq ser.length = ser
  hkey : memBytes M kp 0x61 = key
  o4 : memLoad32 M (X.B + BitVec.ofNat 32 0x4D74) = BitVec.ofNat 32 ser.length
  o8 : memLoad32 M (X.B + BitVec.ofNat 32 0x4D78) = ip
  oC : memLoad32 M (X.B + BitVec.ofNat 32 0x4D7C) = BitVec.ofNat 32 iss.length
  o30 : memLoad32 M (X.B + BitVec.ofNat 32 0x4DA0) = BitVec.ofNat 32 (w.notBefore % 2 ^ 32)
  o34 : memLoad32 M (X.B + BitVec.ofNat 32 0x4DA4) = BitVec.ofNat 32 (w.notBefore / 2 ^ 32)
  o38 : memLoad32 M (X.B + BitVec.ofNat 32 0x4DA8) = BitVec.ofNat 32 (w.notAfter % 2 ^ 32)
  o3C : memLoad32 M (X.B + BitVec.ofNat 32 0x4DAC) = BitVec.ofNat 32 (w.notAfter / 2 ^ 32)
  w30 : memLoad32 M (X.B + BitVec.ofNat 32 0x3A80) = kp
  ptr : memLoad32 M (X.B + BitVec.ofNat 32 0x5A2C) = fp1
  len : memLoad32 M (X.B + BitVec.ofNat 32 0x5A30) = BitVec.ofNat 32 (X.Bf.toNat + 0xB840 - fp1.toNat)

/-- `AcetsM` after writes to `copy_from_slice`'s frame and the slot at
`sp + 0x10`, `sp + 0x1320`, the slice of `keys`, and `keys` from `fp1`. -/
theorem AcetsM.mv {X : AceCtx} (O : X.Ok) {n0 : Machine} {fp : Word} {M M' : Word → BitVec 8} {a : Nat}
    {fp1 ip sq kp : Word} {iss ser key : Bytes} {w : Window} (H : AcetsM X n0 fp M a fp1 ip sq kp iss ser key w)
    (hM : ∀ y : Word, (y.toNat < X.B.toNat + 0x3A40 ∨ X.B.toNat + 0x3A64 ≤ y.toNat) →
      (y.toNat < X.B.toNat + 0x4D70 ∨ X.B.toNat + 0x4D74 ≤ y.toNat) →
      (y.toNat < X.B.toNat + 0x5A2C ∨ X.B.toNat + 0x5A34 ≤ y.toNat) →
      (y.toNat < fp1.toNat ∨ X.Bf.toNat + 0xB840 ≤ y.toNat) → M' y = M y) :
    AcetsM X n0 fp M' a fp1 ip sq kp iss ser key w := by
  have N := acets_n O
  have ⟨_, _, _, _, _, _, _, _⟩ := N
  have F := O.lay.fr
  have := F.hi
  have := H.lo
  have := H.f0
  have := H.f1
  have lay := N.lay
  have hs : ∀ c, 0x3A64 ≤ c → (c + 4 ≤ 0x4D70 ∨ 0x5820 ≤ c ∧ c + 4 ≤ 0x5A2C) →
      memLoad32 M' (X.B + BitVec.ofNat 32 c) = memLoad32 M (X.B + BitVec.ofNat 32 c) := fun c h1 h2 =>
    acets_ld F (by omega) fun y h3 h4 => hM y (by omega) (by omega) (by omega) (by omega)
  have hb : ∀ {p : Word} {n : Nat}, fp.toNat ≤ p.toNat → p.toNat + n ≤ fp1.toNat →
      memBytes M' p n = memBytes M p n := fun h1 h2 =>
    acets_bytes (by omega) fun y h3 h4 => hM y (by omega) (by omega) (by omega) (.inl (by omega))
  exact { H with
    hm := fun x hx => by
      have hx' := hx
      unfold AcetsO at hx'
      obtain ⟨c1, -, c3, -, c5, c6, -⟩ := hx'
      exact (hM x (by omega) (by omega) (by omega) (by omega)).trans (H.hm x hx)
    s14 := (hs 0x3A64 (by decide) (.inl (by decide))).trans H.s14
    pos := (hs 0x5820 (by decide) (.inr ⟨by decide, by decide⟩)).trans H.pos
    hiss := (hb H.i0 H.i1).trans H.hiss
    hser := (hb H.s0 H.s1).trans H.hser
    hkey := (hb H.k0 H.k1).trans H.hkey
    w18 := (hs 0x3A68 (by decide) (.inl (by decide))).trans H.w18
    w1C := (hs 0x3A6C (by decide) (.inl (by decide))).trans H.w1C
    w28 := (hs 0x3A78 (by decide) (.inl (by decide))).trans H.w28
    w2C := (hs 0x3A7C (by decide) (.inl (by decide))).trans H.w2C
    w30 := (hs 0x3A80 (by decide) (.inl (by decide))).trans H.w30 }

section Pass
variable {X : AceCtx} (O : X.Ok) {n0 : Machine} {fp : Word} {jr : Json} {fs : List FulcioKey}
  {ls : List LogKey} {j : Json} {rest : List Json} {ts : List TsaKey} {q : Word} {l a : Nat}
  (C : AcetsC X n0 fp jr fs ls j rest ts q l a)
include O C

set_option maxHeartbeats 4000000 in
/-- Back at 0x123A after the pass, with the key `k` appended. -/
theorem acets_back {M : Word → BitVec 8} {lo hi : Nat}
    (hm : ∀ x : Word, AcetsO X.B.toNat X.Bf.toNat fp.toNat lo hi x.toNat → M x = n0.mem x)
    (hx1 : hi ≤ lo ∨ X.B.toNat + 0x42E0 ≤ lo) (hx2 : hi ≤ lo ∨ hi ≤ X.B.toNat + 0x43E0)
    {f : Fin 32 → Word} {k : Option TsaKey} {fp' : Word} (hk : aceTsa j = some k)
    (R : AcetsR X (ts ++ k.toList).length f) (h19 : f 19 = acSlot X.B 0x1310)
    (hpos : memLoad32 M (X.B + BitVec.ofNat 32 0x5820) = BitVec.ofNat 32 a)
    (hf1 : fp.toNat ≤ fp'.toNat) (hf2 : fp'.toNat ≤ X.Bf.toNat + 0xB840)
    (hptr : memLoad32 M (X.B + BitVec.ofNat 32 0x5A2C) = fp')
    (hlen : memLoad32 M (X.B + BitVec.ofNat 32 0x5A30) = BitVec.ofNat 32 (X.Bf.toNat + 0xB840 - fp'.toNat))
    (htk : AceTsasAt X.Bf fp' M (acSlot X.B 0x890) (ts ++ k.toList)) :
    WP bootMainClosure0Code AC (acetsQ X (AcetsNext X jr fs ls (j :: rest))) M 0x123A f := by
  have A := C.at0
  have I := C.inv
  have F := O.lay.fr
  have N := acets_n O
  have ⟨_, _, _, _, _, _, _, _⟩ := N
  have := A.fr.lo
  have := A.fr.hi
  refine WP.here fun n hpc hn hr => ?_
  have h2 : reg n (2 : Fin 32) = X.B + 0x3A50 := by rw [hr]; exact R.rsp
  refine ⟨acets_inv O A hm hx1 hx2 hn h2 (by rw [hr]; exact R.rgp) (by rw [hr]; exact R.rtp),
    .inr (.inr ⟨hpc, j, rest, rfl, fp', ts ++ k.toList,
      acets_at O A hm hx1 hx2 hn hpc h2 (by rw [hr]; exact R.rgp) (by rw [hr]; exact R.rtp)
        (by rw [hr]; exact R.r21) (by rw [hr]; exact R.r25) (by rw [hr]; exact R.r27) hf1 hf2 hptr hlen, ?_⟩)⟩
  obtain ⟨p, l', c0, c4, hpa, hD, hpl, hE⟩ := C.cur
  have e4 : acSlot X.B 0x1DC8 + 4 = X.B + BitVec.ofNat 32 0x581C := by simp only [acSlot]; bv_omega
  have e8 : acSlot X.B 0x1DC8 + 8 = X.B + BitVec.ofNat 32 0x5820 := by simp only [acSlot]; bv_omega
  have buf : ∀ y : Word, X.Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp.toNat → M y = n0.mem y :=
    fun y h1 h2 => hm y (by acets_o)
  refine ⟨I.root, I.cas, I.tlogs, I.tsas.step hk, ⟨p, l', a, ?_, ?_, ?_, hpa, hD, hpl, hE⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn, ← c0]
    exact acets_ld F (c := 0x5818) (by decide) fun y h1 h2 => hm y (by acets_o)
  · rw [hn, e4, ← c4, e4]
    exact acets_ld F (c := 0x581C) (by decide) fun y h1 h2 => hm y (by acets_o)
  · rw [hn, e8]; exact hpos
  · rw [hn]
    exact acets_arrMv I.fulcio (fun c hc => hm _ (by
      have e := F.at (0x3A50 + 0x1ED0 + c) (by omega)
      rw [ace_slot, e]; acets_o)) buf hf1
  · rw [hn]
    exact acets_arrMv I.logs (fun c hc => hm _ (by
      have e := F.at (0x3A50 + 0x350 + c) (by omega)
      rw [ace_slot, e]; acets_o)) buf hf1
  · rw [hn]; exact htk
  · rw [hr]; exact h19
  · rw [hr]; exact R.r26

set_option maxHeartbeats 4000000 in
/-- From 0x13D0, with the key's `SignerIdentifier` at `fp1` and its key
at `kp`: the count check, then the entry at `sp + 0x890 + 0x20 * k`. -/
theorem acets_p5 {M : Word → BitVec 8}
    (hm : ∀ x : Word, AcetsO X.B.toNat X.Bf.toNat fp.toNat 0 0 x.toNat → M x = n0.mem x)
    {f : Fin 32 → Word} {tk : TsaKey} {fp1 fp2 kp : Word}
    (hk : aceTsa j = some (some tk)) (R : AcetsR X ts.length f) (h9 : f 9 = fp1)
    (h18 : f 18 = BitVec.ofNat 32 tk.signerId.length) (h8 : f 8 = 5) (h19 : f 19 = acSlot X.B 0x1310)
    (hpos : memLoad32 M (X.B + BitVec.ofNat 32 0x5820) = BitVec.ofNat 32 a)
    (hptr : memLoad32 M (X.B + BitVec.ofNat 32 0x5A2C) = fp2)
    (hlen : memLoad32 M (X.B + BitVec.ofNat 32 0x5A30) = BitVec.ofNat 32 (X.Bf.toNat + 0xB840 - fp2.toNat))
    (hk0 : fp.toNat ≤ kp.toNat) (hk1 : kp.toNat + 0x61 ≤ fp1.toNat)
    (hf1 : fp1.toNat + tk.signerId.length = fp2.toNat) (hf2 : fp2.toNat ≤ X.Bf.toNat + 0xB840)
    (hname : memBytes M fp1 tk.signerId.length = tk.signerId) (hkey : memBytes M kp 0x61 = tk.publicKey)
    (s1C : memLoad32 M (X.B + BitVec.ofNat 32 0x3A6C) = BitVec.ofNat 32 (tk.window.notBefore % 2 ^ 32))
    (s18 : memLoad32 M (X.B + BitVec.ofNat 32 0x3A68) = BitVec.ofNat 32 (tk.window.notBefore / 2 ^ 32))
    (s28 : memLoad32 M (X.B + BitVec.ofNat 32 0x3A78) = BitVec.ofNat 32 (tk.window.notAfter % 2 ^ 32))
    (s2C : memLoad32 M (X.B + BitVec.ofNat 32 0x3A7C) = BitVec.ofNat 32 (tk.window.notAfter / 2 ^ 32))
    (s30 : memLoad32 M (X.B + BitVec.ofNat 32 0x3A80) = kp)
    (hnb : tk.window.notBefore < 2 ^ 64) (hna : tk.window.notAfter < 2 ^ 64) :
    WP bootMainClosure0Code AC (acetsQ X (AcetsNext X jr fs ls (j :: rest))) M 0x13D0 f := by
  have A := C.at0
  have I := C.inv
  have F := O.lay.fr
  have N := acets_n O
  have ⟨_, _, _, _, _, _, _, _⟩ := N
  have := A.fr.lo
  have := A.fr.hi
  have hT := I.tsaKeys.1
  refine WP.aluImm ac_at_13d0 ?_; wn
  refine WP.branch ac_at_13d2 (fun eb => ?_) (fun eb => ?_) <;> wn
  · exact acets_f1A6A O A hm (.inl (Nat.le_refl _)) (.inl (Nat.le_refl _)) (by rsimp) (by rsimp; exact R.rsp)
      (by rsimp; exact R.rgp) (by rsimp; exact R.rtp) (by rsimp; rw [h8]; decide)
  rsimp at eb
  have hk7 : ts.length ≤ 7 := by
    rw [acets_bltu, R.rz, R.r26] at eb
    have e1 := of_decide_eq_false eb
    rw [show (aluEval .add (0 : Word) 7).toNat = 7 from rfl, Sv.ofNat_toNat_lt (by omega)] at e1
    omega
  refine WP.aluImm ac_at_13d6 ?_; wn
  refine WP.aluImm ac_at_13da ?_; wn
  refine WP.aluImm ac_at_13dc ?_; wn
  refine WP.aluImm ac_at_13e0 ?_; wn
  refine WP.alu ac_at_13e4 ?_; wn
  have he : aluEval .add (aluEval .sll (f 26) 5) (aluEval .add (aluEval .add (f 2) 0x7FF) 0x91) =
      X.B + BitVec.ofNat 32 (0x42E0 + 0x20 * ts.length) := by
    rw [R.r26, R.rsp, ev_add, ev_add, ev_add, acets_ev_sll]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, BitVec.toNat_shiftLeft, Nat.reduceMod,
      Nat.shiftLeft_eq]
    have := X.B.isLt
    omega
  have r26 : aluEval .add (f 26) 1 = BitVec.ofNat 32 (ts ++ (some tk).toList).length := by
    rw [R.r26, ev_add, Option.toList_some, List.length_append, List.length_singleton]
    bv_omega
  rw [he, r26]
  refine acets_sw F ac_at_13e6 (c := 0x42E0 + 0x20 * ts.length) (by rsimp; bv_omega) (by omega) (by omega) ?_
  wn
  refine acets_sw F ac_at_13e8 (c := 0x42E0 + 0x20 * ts.length + 4) (by rsimp; bv_omega) (by omega) (by omega) ?_
  wn
  refine acets_lw F ac_at_13ec (c := 0x3A6C) (by rsimp; rw [R.rsp]; bv_omega) (by decide) (by decide) ?_; wn
  refine acets_sw F ac_at_13ee (c := 0x42E0 + 0x20 * ts.length + 8) (by rsimp; bv_omega) (by omega) (by omega) ?_
  wn
  refine acets_lw F ac_at_13f0 (c := 0x3A68) (by rsimp; rw [R.rsp]; bv_omega) (by decide) (by decide) ?_; wn
  refine acets_sw F ac_at_13f2 (c := 0x42E0 + 0x20 * ts.length + 0xC) (by rsimp; bv_omega) (by omega)
    (by omega) ?_
  wn
  refine acets_lw F ac_at_13f4 (c := 0x3A78) (by rsimp; rw [R.rsp]; bv_omega) (by decide) (by decide) ?_; wn
  refine acets_sw F ac_at_13f6 (c := 0x42E0 + 0x20 * ts.length + 0x10) (by rsimp; bv_omega) (by omega)
    (by omega) ?_
  wn
  refine acets_lw F ac_at_13f8 (c := 0x3A7C) (by rsimp; rw [R.rsp]; bv_omega) (by decide) (by decide) ?_; wn
  refine acets_sw F ac_at_13fa (c := 0x42E0 + 0x20 * ts.length + 0x14) (by rsimp; bv_omega) (by omega)
    (by omega) ?_
  wn
  refine acets_lw F ac_at_13fc (c := 0x3A80) (by rsimp; rw [R.rsp]; bv_omega) (by decide) (by decide) ?_; wn
  refine acets_sw F ac_at_13fe (c := 0x42E0 + 0x20 * ts.length + 0x18) (by rsimp; bv_omega) (by omega)
    (by omega) ?_
  wn
  refine WP.jal ac_at_1400 (by decide) ?_; wn
  simp (disch := omega) only [acets_ls F, s1C, s18, s28, s2C, s30, h9, h18]
  refine acets_back O C (lo := X.B.toNat + (0x42E0 + 0x20 * ts.length))
    (hi := X.B.toNat + (0x42E0 + 0x20 * ts.length) + 0x1C) (fun x hx => ?_) (.inr (by omega)) (.inr (by omega))
    (k := some tk) (fp' := fp2) hk ?_ (by rsimp; exact h19) (by simp (disch := omega) only [acets_ls F]; exact hpos)
    (by omega) hf2 (by simp (disch := omega) only [acets_ls F]; exact hptr)
    (by simp (disch := omega) only [acets_ls F]; exact hlen) ?_
  · have h7 := hx.2.2.2.2.2.2
    simp (disch := omega) only [acets_g32 F]
    exact hm x hx.wk
  · exact ⟨by rsimp, by rsimp; exact R.rsp, by rsimp; exact R.rgp, by rsimp; exact R.rtp, by rsimp; exact R.r21,
      by rsimp; exact R.r25, by rsimp, by rsimp; exact R.r27⟩
  have buf : ∀ y : Word, X.Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp2.toNat → y.toNat < X.B.toNat ∨
      X.B.toNat + 0x5A70 ≤ y.toNat := fun y h1 h2 => by omega
  refine acets_snoc (M := n0.mem) I.tsaKeys (by omega) (by omega) (fun c hc hc' => ?_)
    (fun y h1 h2 => ?_) ?_
  · have e := F.at (0x3A50 + 0x890 + c) (by omega)
    rw [ace_slot]
    simp (disch := omega) only [acets_g32 F]
    exact hm _ (by rw [e]; acets_o)
  · have := buf y h1 (by omega)
    simp (disch := omega) only [acets_g32 F]
    exact hm y (by acets_o)
  rw [ace_slot, show 0x3A50 + 0x890 + 0x20 * ts.length = 0x42E0 + 0x20 * ts.length by omega]
  exact acets_entry F (by omega) buf (by omega) (by omega) hname (by omega) (by omega) hkey hnb hna

set_option maxHeartbeats 4000000 in
/-- From 0x139A: the header, the issuer, and the serial number to `fp1`,
then the entry. -/
theorem acets_p4b {M : Word → BitVec 8} {f : Fin 32 → Word} {d iss ser key : Bytes} {w : Window}
    {fp1 fp2 ip sq kp : Word} {hl : Nat}
    (H : AcetsM X n0 fp M a fp1 ip sq kp iss ser key w)
    (hk : aceTsa j = some (some ⟨[0x30] ++ d ++ (iss ++ ser), key, w⟩)) (hhl : d.length + 1 = hl)
    (hd : d.length ≤ 3)
    (R : AcetsR X ts.length f) (h8 : f 8 = 5) (h19 : f 19 = acSlot X.B 0x1310) (h9 : f 9 = fp1)
    (h11 : f 11 = BitVec.ofNat 32 hl) (h18 : f 18 = BitVec.ofNat 32 (hl + (iss.length + ser.length)))
    (h20 : f 20 = BitVec.ofNat 32 iss.length) (h22 : f 22 = BitVec.ofNat 32 ser.length) (h23 : f 23 = sq)
    (h24 : f 24 = fp1 + BitVec.ofNat 32 hl)
    (hfp2 : fp2.toNat = fp1.toNat + (hl + (iss.length + ser.length))) (hf2 : fp2.toNat ≤ X.Bf.toNat + 0xB840)
    (hhdr : memBytes M (X.B + BitVec.ofNat 32 0x4D70) hl = [0x30] ++ d)
    (hptr : memLoad32 M (X.B + BitVec.ofNat 32 0x5A2C) = fp2)
    (hlen : memLoad32 M (X.B + BitVec.ofNat 32 0x5A30) = BitVec.ofNat 32 (X.Bf.toNat + 0xB840 - fp2.toNat))
    (s60 : memLoad32 M (X.B + BitVec.ofNat 32 0x3A60) =
      fp1 + BitVec.ofNat 32 hl + BitVec.ofNat 32 iss.length) :
    WP bootMainClosure0Code AC (acetsQ X (AcetsNext X jr fs ls (j :: rest))) M 0x139A f := by
  have A := C.at0
  have F := O.lay.fr
  obtain ⟨nb1, nb2, -, nf1, -, nl, -, -⟩ := acets_n O
  have E := acets_env O A H.hm (.inl (Nat.le_refl _)) (.inl (Nat.le_refl _))
  have := H.lo; have := H.f0; have := H.f1; have := H.i0; have := H.i1; have := H.s0; have := H.s1
  have := H.k0; have := H.k1
  have eF := F.at 0x3A40 (by decide)
  have e70 := F.at 0x4D70 (by decide)
  have t1 : (fp1 + BitVec.ofNat 32 hl).toNat = fp1.toNat + hl := acets_tn (by omega)
  have t2 : (fp1 + BitVec.ofNat 32 hl + BitVec.ofNat 32 iss.length).toNat = fp1.toNat + hl + iss.length := by
    rw [acets_tn (by rw [t1]; omega), t1]
  refine WP.lui ac_at_139a ?_; wn
  refine WP.aluImm ac_at_139c ?_; wn
  refine WP.alu ac_at_13a0 ?_; wn
  refine WP.alu ac_at_13a4 ?_; wn
  refine WP.alu ac_at_13a6 ?_; wn
  refine acets_cfs O E ac_at_13a8 ac_at_13ac (by decide) (by decide) (dst := fp1)
    (src := X.B + BitVec.ofNat 32 0x4D70) (N := hl) (by acets_z; exact h9) (by rsimp; exact h11)
    (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by acets_z; exact h11) (by rsimp; exact R.rsp) (by omega)
    (by rw [e70]; omega) (by omega) (by rw [e70]; omega) (by rw [e70]; omega) fun m1 W1 => ?_
  have K1 : ∀ y : Word, (y.toNat < X.B.toNat + 0x3A40 ∨ X.B.toNat + 0x3A50 ≤ y.toNat) →
      (y.toNat < fp1.toNat ∨ fp1.toNat + hl ≤ y.toNat) → m1.mem y = M y := fun y g1 g2 =>
    acets_cpo W1 (by rw [eF]; omega) g2 (by rw [eF]; omega) (by omega)
  have H1 := H.mv O fun y g1 g2 g3 g4 => K1 y (by omega) (by omega)
  have E1 := acets_env O A H1.hm (.inl (Nat.le_refl _)) (.inl (Nat.le_refl _))
  refine WP.alu ac_at_13b0 ?_; wn
  refine WP.alu ac_at_13b2 ?_; wn
  refine acets_lw F ac_at_13b4 (c := 0x3A64) (by rsimp; rw [R.rsp]; bv_omega) (by decide) (by decide) ?_; wn
  rw [H1.s14]
  refine WP.alu ac_at_13b6 ?_; wn
  refine acets_cfs O E1 ac_at_13b8 ac_at_13bc (by decide) (by decide) (dst := fp1 + BitVec.ofNat 32 hl)
    (src := ip) (N := iss.length) (by acets_z; exact h24) (by acets_z; exact h20) (by rsimp)
    (by acets_z; exact h20) (by rsimp; exact R.rsp) (by omega) (by omega) (by omega) (by omega) (by omega)
    fun m2 W2 => ?_
  have K2 : ∀ y : Word, (y.toNat < X.B.toNat + 0x3A40 ∨ X.B.toNat + 0x3A50 ≤ y.toNat) →
      (y.toNat < fp1.toNat + hl ∨ fp1.toNat + hl + iss.length ≤ y.toNat) → m2.mem y = m1.mem y := fun y g1 g2 =>
    acets_cpo W2 (by rw [eF]; omega) (by rw [t1]; omega) (by rw [eF]; omega) (by omega)
  have H2 := H1.mv O fun y g1 g2 g3 g4 => K2 y (by omega) (by omega)
  have E2 := acets_env O A H2.hm (.inl (Nat.le_refl _)) (.inl (Nat.le_refl _))
  have s60' : memLoad32 m2.mem (X.B + BitVec.ofNat 32 0x3A60) =
      fp1 + BitVec.ofNat 32 hl + BitVec.ofNat 32 iss.length :=
    (acets_ld F (c := 0x3A60) (by decide) fun y g1 g2 =>
      (K2 y (by omega) (by omega)).trans (K1 y (by omega) (by omega))).trans s60
  refine acets_lw F ac_at_13c0 (c := 0x3A60) (by rsimp; rw [R.rsp]; bv_omega) (by decide) (by decide) ?_; wn
  rw [s60']
  refine WP.alu ac_at_13c2 ?_; wn
  refine WP.alu ac_at_13c4 ?_; wn
  refine WP.alu ac_at_13c6 ?_; wn
  refine acets_cfs O E2 ac_at_13c8 ac_at_13cc (by decide) (by decide)
    (dst := fp1 + BitVec.ofNat 32 hl + BitVec.ofNat 32 iss.length) (src := sq) (N := ser.length) (by rsimp)
    (by acets_z; exact h22) (by acets_z; exact h23) (by acets_z; exact h22) (by rsimp; exact R.rsp) (by omega)
    (by omega) (by omega) (by omega) (by omega) fun m3 W3 => ?_
  have K3 : ∀ y : Word, (y.toNat < X.B.toNat + 0x3A40 ∨ X.B.toNat + 0x3A50 ≤ y.toNat) →
      (y.toNat < fp1.toNat + hl + iss.length ∨ fp1.toNat + hl + iss.length + ser.length ≤ y.toNat) →
      m3.mem y = m2.mem y := fun y g1 g2 =>
    acets_cpo W3 (by rw [eF]; omega) (by rw [t2]; omega) (by rw [eF]; omega) (by omega)
  have H3 := H2.mv O fun y g1 g2 g3 g4 => K3 y (by omega) (by omega)
  have ldm : ∀ c, 0x3A50 ≤ c → c + 4 ≤ 0x5A70 →
      memLoad32 m3.mem (X.B + BitVec.ofNat 32 c) = memLoad32 M (X.B + BitVec.ofNat 32 c) := fun c h1 h2 =>
    acets_ld F h2 fun y g1 g2 =>
      (K3 y (by omega) (by omega)).trans ((K2 y (by omega) (by omega)).trans (K1 y (by omega) (by omega)))
  have hsl : ([0x30] ++ d ++ (iss ++ ser)).length = hl + (iss.length + ser.length) := by
    simp only [List.length_append, List.length_singleton]; omega
  have p1 : memBytes m3.mem fp1 hl = [0x30] ++ d := by
    refine (ace_memBytes_ext fun i hi => ?_).trans hhdr
    have ti := acets_tn (a := fp1) (c := i) (by omega)
    rw [K3 _ (by omega) (by omega), K2 _ (by omega) (by omega)]
    exact acets_cpi W1 hi (by omega) (by rw [eF]; omega) (by rw [eF]; omega)
  have p2 : memBytes m3.mem (fp1 + BitVec.ofNat 32 hl) iss.length = iss := by
    refine (ace_memBytes_ext fun i hi => ?_).trans H.hiss
    have ti := acets_tn (a := fp1 + BitVec.ofNat 32 hl) (c := i) (by omega)
    have tj := acets_tn (a := ip) (c := i) (by omega)
    rw [K3 _ (by omega) (by omega), acets_cpi W2 hi (by omega) (by rw [eF]; omega) (by rw [eF]; omega)]
    exact K1 _ (by omega) (by omega)
  have p3 : memBytes m3.mem (fp1 + BitVec.ofNat 32 hl + BitVec.ofNat 32 iss.length) ser.length = ser := by
    refine (ace_memBytes_ext fun i hi => ?_).trans H.hser
    have ti := acets_tn (a := fp1 + BitVec.ofNat 32 hl + BitVec.ofNat 32 iss.length) (c := i) (by omega)
    have tj := acets_tn (a := sq) (c := i) (by omega)
    rw [acets_cpi W3 hi (by omega) (by rw [eF]; omega) (by rw [eF]; omega), K2 _ (by omega) (by omega)]
    exact K1 _ (by omega) (by omega)
  have hname : memBytes m3.mem fp1 ([0x30] ++ d ++ (iss ++ ser)).length = [0x30] ++ d ++ (iss ++ ser) := by
    rw [hsl, memBytes_split, memBytes_split, p1, p2, p3]
  exact acets_p5 O C (tk := ⟨[0x30] ++ d ++ (iss ++ ser), key, w⟩) H3.hm hk (by acets_hr) (by rsimp; exact h9)
    (by rsimp; rw [h18]; exact congrArg _ hsl.symm) (by rsimp; exact h8) (by rsimp; exact h19) H3.pos
    ((ldm 0x5A2C (by decide) (by decide)).trans hptr) ((ldm 0x5A30 (by decide) (by decide)).trans hlen)
    H3.k0 H3.k1 (by show fp1.toNat + ([0x30] ++ d ++ (iss ++ ser)).length = _; rw [hsl, hfp2]) hf2 hname
    H3.hkey H3.w1C H3.w18 H3.w28 H3.w2C H3.w30 H3.nb H3.na

set_option maxHeartbeats 4000000 in
/-- From 0x135C, with the `SignerIdentifier`'s header at `sp + 0x1320`:
reserve its bytes in `keys`. -/
theorem acets_p4 {M : Word → BitVec 8} {f : Fin 32 → Word} {d iss ser key : Bytes} {w : Window}
    {fp1 ip sq kp : Word}
    (H : AcetsM X n0 fp M a fp1 ip sq kp iss ser key w)
    (hk : aceTsa j = some (some ⟨[0x30] ++ d ++ (iss ++ ser), key, w⟩)) (hd : d.length ≤ 3)
    (R : AcetsR X ts.length f) (h8 : f 8 = 5) (h19 : f 19 = acSlot X.B 0x1310)
    (h10 : f 10 = BitVec.ofNat 32 (iss.length + ser.length)) (h11 : f 11 = BitVec.ofNat 32 (d.length + 1))
    (h20 : f 20 = BitVec.ofNat 32 iss.length) (h22 : f 22 = BitVec.ofNat 32 ser.length) (h23 : f 23 = sq)
    (hhdr : memBytes M (X.B + BitVec.ofNat 32 0x4D70) (d.length + 1) = [0x30] ++ d)
    (hptr : memLoad32 M (X.B + BitVec.ofNat 32 0x5A2C) = fp1)
    (hlen : memLoad32 M (X.B + BitVec.ofNat 32 0x5A30) = BitVec.ofNat 32 (X.Bf.toNat + 0xB840 - fp1.toNat)) :
    WP bootMainClosure0Code AC (acetsQ X (AcetsNext X jr fs ls (j :: rest))) M 0x135C f := by
  have A := C.at0
  have F := O.lay.fr
  obtain ⟨nb1, nb2, -, nf1, -, nl, -, -⟩ := acets_n O
  have := H.lo; have := H.f0; have := H.f1; have := H.i1; have := H.s1
  have := fp1.isLt
  generalize hhl : d.length + 1 = hl at h11 hhdr
  refine WP.alu ac_at_135c ?_; wn
  rw [h10, h11, ev_add, acets_addN]
  refine WP.branch ac_at_1360 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso
    rsimp at eb
    rw [h11, acets_ltN (by omega) (by omega)] at eb
    have := of_decide_eq_true eb
    omega
  refine WP.lui ac_at_1364 ?_; wn
  refine WP.aluImm ac_at_1366 ?_; wn
  refine WP.alu ac_at_136a ?_; wn
  refine acets_lw F ac_at_136c (c := 0x5A30) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide)
    (by decide) ?_; wn
  rw [hlen]
  refine WP.branch ac_at_1370 (fun eb => ?_) (fun eb => ?_) <;> wn
  · exact acets_fC3A O A H.hm (.inl (Nat.le_refl _)) (.inl (Nat.le_refl _)) (by rsimp)
      (by rsimp; exact R.rsp) (by rsimp; exact R.rgp) (by rsimp; exact R.rtp)
  rsimp at eb
  rw [acets_ltN (by omega) (by omega)] at eb
  have hroom := of_decide_eq_false eb
  refine WP.lui ac_at_1374 ?_; wn
  refine WP.aluImm ac_at_1376 ?_; wn
  refine WP.alu ac_at_137a ?_; wn
  refine WP.aluImm ac_at_137e ?_; wn
  refine acets_lw F ac_at_1382 (c := 0x5A2C) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide)
    (by decide) ?_; wn
  rw [hptr]
  refine WP.alu ac_at_1384 ?_; wn
  refine WP.alu ac_at_1388 ?_; wn
  refine WP.alu ac_at_138c ?_; wn
  refine acets_sw F ac_at_1390 (c := 0x5A2C) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide)
    (by decide) ?_; wn
  refine acets_sw F ac_at_1392 (c := 0x5A30) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide)
    (by decide) ?_; wn
  refine WP.alu ac_at_1394 ?_; wn
  refine acets_sw F ac_at_1398 (c := 0x3A60) (by rsimp; simp only [R.rsp]; bv_omega) (by decide)
    (by decide) ?_; wn
  have hfp2 : (fp1 + BitVec.ofNat 32 (hl + (iss.length + ser.length))).toNat =
      fp1.toNat + (hl + (iss.length + ser.length)) := acets_tn (by omega)
  have e70 := F.at 0x4D70 (by decide)
  refine acets_p4b O C (H.mv O fun y g1 g2 g3 g4 => by simp (disch := omega) only [acets_g32 F]) hk hhl hd
    (by acets_hr) (by rsimp; exact h8) (by rsimp; exact h19) (by rsimp) (by rsimp; exact h11) (by rsimp)
    (by rsimp; exact h20) (by rsimp; exact h22) (by rsimp; exact h23) (by rsimp; rw [h11]; rfl) hfp2 (by omega)
    ?_ (by simp (disch := omega) only [acets_ls F, memLoad32_store32_same] <;> rfl) ?_
    (by simp (disch := omega) only [acets_ls F, memLoad32_store32_same]; rw [h11, h20]; rfl)
  · rw [← hhdr]
    exact acets_bytes (by rw [e70]; omega) fun y g1 g2 => by
      rw [e70] at g1 g2
      simp (disch := omega) only [acets_g32 F]
  · simp (disch := omega) only [acets_ls F, memLoad32_store32_same]
    rw [acets_ev_sub, acets_subN (by omega) (by omega), hfp2]
    congr 1
    omega

/-- The bytes `[0x30] ++ d` at `sp + 0x1320`, one at a time. -/
macro "acets_hdr" : tactic => `(tactic| (
  refine acets_mbl fun i hi => ?_
  rw [add_ofNat_assoc]
  have hi' := hi
  simp only [List.length_append, List.length_cons, List.length_nil] at hi'
  rcases i with _ | _ | _ | _ | i
  all_goals first
    | (exfalso; omega)
    | simp (disch := decide) only [Nat.reduceAdd, acets_s8 ‹Fr _ 0x5A70›, memStore8_same]))

set_option maxHeartbeats 4000000 in
/-- From 0x12F4, with `L`, the issuer's and serial number's lengths added,
under 0x10000: the `SignerIdentifier`'s header at `sp + 0x1320`. -/
theorem acets_p3b {M : Word → BitVec 8} {f : Fin 32 → Word} {iss ser key : Bytes} {w : Window}
    {fp1 ip sq kp : Word} {L : Nat}
    (H : AcetsM X n0 fp M a fp1 ip sq kp iss ser key w) (hLd : iss.length + ser.length = L)
    (hT : ∀ d, derLen L = some d → aceTsa j = some (some ⟨[0x30] ++ d ++ (iss ++ ser), key, w⟩))
    (hL : L < 2 ^ 16)
    (R : AcetsR X ts.length f) (h8 : f 8 = 5) (h15 : f 15 = acSlot X.B 0x1310)
    (h10 : f 10 = BitVec.ofNat 32 L)
    (h11 : f 11 = aluEval .add (aluEval .sll (BitVec.ofNat 32 L) 0x10) 0x500)
    (h20 : f 20 = BitVec.ofNat 32 iss.length) (h22 : f 22 = BitVec.ofNat 32 ser.length) (h23 : f 23 = sq)
    (hptr : memLoad32 M (X.B + BitVec.ofNat 32 0x5A2C) = fp1)
    (hlen : memLoad32 M (X.B + BitVec.ofNat 32 0x5A30) = BitVec.ofNat 32 (X.Bf.toNat + 0xB840 - fp1.toNat)) :
    WP bootMainClosure0Code AC (acetsQ X (AcetsNext X jr fs ls (j :: rest))) M 0x12F4 f := by
  have F := O.lay.fr
  refine WP.aluImm ac_at_12f4 ?_; wn
  rw [h11, acets_vA16 hL]
  refine WP.aluImm ac_at_12f8 ?_; wn
  refine WP.aluImm ac_at_12fc ?_; wn
  rw [h11, acets_vA23 hL]
  refine WP.aluImm ac_at_1300 ?_; wn
  refine acets_sb F ac_at_1304 (c := 0x4D70) (by rsimp; rw [h15]; simp only [acSlot]; bv_omega) (by decide) ?_; wn
  refine acets_sb F ac_at_1308 (c := 0x4D72) (by rsimp; rw [h15]; simp only [acSlot]; bv_omega) (by decide) ?_; wn
  refine WP.lui ac_at_130c ?_; wn
  refine WP.aluImm ac_at_130e ?_; wn
  refine WP.alu ac_at_1312 ?_; wn
  refine acets_sb F ac_at_1316 (c := 0x4D73) (by rsimp; rw [h15]; simp only [acSlot]; bv_omega) (by decide) ?_; wn
  refine WP.branch ac_at_131a (fun eb => ?_) (fun eb => ?_) <;> wn
  · rsimp at eb
    have h128 := acets_bneT eb
    refine WP.aluImm ac_at_1324 ?_; wn
    rw [h11, acets_vA24 hL]
    refine WP.branch ac_at_1326 (fun eb => ?_) (fun eb => ?_) <;> wn
    · rsimp at eb
      have h256 := acets_bneT eb
      refine WP.aluImm ac_at_1334 ?_; wn
      rw [acets_vS8 hL]
      refine WP.alu ac_at_1336 ?_; wn
      refine WP.lui ac_at_1338 ?_; wn
      refine WP.aluImm ac_at_133a ?_; wn
      refine WP.alu ac_at_133e ?_; wn
      refine WP.aluImm ac_at_1340 ?_; wn
      refine acets_sb F ac_at_1344 (c := 0x4D71) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide) ?_
      wn
      refine acets_sb F ac_at_1348 (c := 0x4D72) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide) ?_
      wn
      refine WP.lui ac_at_134c ?_; wn
      refine WP.aluImm ac_at_134e ?_; wn
      refine WP.alu ac_at_1352 ?_; wn
      refine acets_sb F ac_at_1356 (c := 0x4D73) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide) ?_
      wn
      refine WP.aluImm ac_at_135a ?_; wn
      have c1 : ¬L < 0x80 := by omega
      have c2 : ¬L < 0x100 := by omega
      have c3 : L < 0x10000 := by omega
      have hd : derLen L = some [0x82, L / 256, L % 256] := by
        unfold derLen; rw [if_neg c1, if_neg c2, if_pos c3]
      refine acets_p4 O C (H.mv O fun y g1 g2 g3 g4 => by simp (disch := omega) only [acets_g8 F]) (hT _ hd)
        (by simp only [List.length_cons, List.length_nil]; omega) (by acets_hr) (by rsimp; exact h8)
        (by rsimp; simp only [ev_add, R.rsp, acSlot]; bv_omega)
        (by rsimp; rw [h10, hLd]) (by rsimp <;> rfl) (by rsimp; exact h20) (by rsimp; exact h22)
        (by rsimp; exact h23) ?_ (by simp (disch := omega) only [acets_l8 F]; exact hptr)
        (by simp (disch := omega) only [acets_l8 F]; exact hlen)
      show memBytes _ _ ([0x30] ++ [0x82, L / 256, L % 256]).length = _
      acets_hdr
      · rfl
      · rfl
      · exact acets_bOr hL
      · exact acets_bAnd
    · rsimp at eb
      have h256 := acets_bneF eb
      refine WP.aluImm ac_at_1328 ?_; wn
      refine acets_sb F ac_at_132c (c := 0x4D71) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide) ?_
      wn
      refine WP.aluImm ac_at_1330 ?_; wn
      refine WP.jal ac_at_1332 (by decide) ?_; wn
      have c1 : ¬L < 0x80 := by omega
      have c2 : L < 0x100 := by omega
      have hd : derLen L = some [0x81, L] := by
        unfold derLen; rw [if_neg c1, if_pos c2]
      refine acets_p4 O C (H.mv O fun y g1 g2 g3 g4 => by simp (disch := omega) only [acets_g8 F]) (hT _ hd)
        (by simp only [List.length_cons, List.length_nil]; omega) (by acets_hr) (by rsimp; exact h8)
        (by rsimp; simp only [ev_add, R.rsp, acSlot]; bv_omega)
        (by rsimp; rw [h10, hLd]) (by rsimp <;> rfl) (by rsimp; exact h20) (by rsimp; exact h22)
        (by rsimp; exact h23) ?_ (by simp (disch := omega) only [acets_l8 F]; exact hptr)
        (by simp (disch := omega) only [acets_l8 F]; exact hlen)
      show memBytes _ _ ([0x30] ++ [0x81, L]).length = _
      acets_hdr
      · rfl
      · rfl
      · exact acets_bLow.trans (Nat.mod_eq_of_lt c2)
  · rsimp at eb
    have h128 := acets_bneF eb
    refine acets_sb F ac_at_131c (c := 0x4D71) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide) ?_
    wn
    refine WP.aluImm ac_at_1320 ?_; wn
    refine WP.jal ac_at_1322 (by decide) ?_; wn
    have c1 : L < 0x80 := by omega
    have hd : derLen L = some [L] := by
      unfold derLen; rw [if_pos c1]
    refine acets_p4 O C (H.mv O fun y g1 g2 g3 g4 => by simp (disch := omega) only [acets_g8 F]) (hT _ hd)
      (by simp only [List.length_cons, List.length_nil]; omega) (by acets_hr) (by rsimp; exact h8)
      (by rsimp; simp only [ev_add, R.rsp, acSlot]; bv_omega)
      (by rsimp; rw [h10, hLd]) (by rsimp <;> rfl) (by rsimp; exact h20) (by rsimp; exact h22)
      (by rsimp; exact h23) ?_ (by simp (disch := omega) only [acets_l8 F]; exact hptr)
      (by simp (disch := omega) only [acets_l8 F]; exact hlen)
    show memBytes _ _ ([0x30] ++ [L]).length = _
    acets_hdr
    · rfl
    · exact acets_bAnd.trans (Nat.mod_eq_of_lt (by omega))

set_option maxHeartbeats 4000000 in
/-- From 0x12A0, with `read_chain`'s result at `sp + 0x1320` and a key:
the length check, then the window and the issuer's address to the slots. -/
theorem acets_p3a {M : Word → BitVec 8} {f : Fin 32 → Word} {iss ser key : Bytes} {w : Window}
    {fp1 ip sq kp : Word} (K : AcetsK X n0 fp M a fp1 ip sq kp iss ser key w)
    (hT : ∀ d, derLen (iss.length + ser.length) = some d →
      aceTsa j = some (some ⟨[0x30] ++ d ++ (iss ++ ser), key, w⟩))
    (R : AcetsR X ts.length f) (h23 : f 23 = sq) :
    WP bootMainClosure0Code AC (acetsQ X (AcetsNext X jr fs ls (j :: rest))) M 0x12A0 f := by
  have A := C.at0
  have F := O.lay.fr
  have N := acets_n O
  have ⟨_, _, _, _, _, _, _, _⟩ := N
  have := K.i0
  have := K.i1
  have := K.s0
  have := K.s1
  have := K.f1
  have := K.s0
  have := K.f0
  have := K.i0
  have := K.i1
  have := K.k0
  have := K.k1
  have := K.lo
  have hL32 : iss.length + ser.length < 2 ^ 32 := by omega
  refine WP.lui ac_at_12a0 ?_; wn
  refine WP.aluImm ac_at_12a2 ?_; wn
  refine WP.alu ac_at_12a6 ?_; wn
  refine acets_lw F ac_at_12a8 (c := 0x4D74) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide)
    (by decide) ?_; wn
  rw [K.o4]
  refine acets_lw F ac_at_12aa (c := 0x4D7C) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide)
    (by decide) ?_; wn
  rw [K.oC]
  refine WP.alu ac_at_12ae ?_; wn
  rw [ev_add (BitVec.ofNat 32 _), acets_addN]
  refine WP.branch ac_at_12b2 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso
    rsimp at eb
    rw [acets_bltu] at eb
    have e1 := of_decide_eq_true eb
    simp only [BitVec.toNat_ofNat] at e1
    omega
  refine WP.alu ac_at_12b6 ?_; wn
  refine WP.aluImm ac_at_12b8 ?_; wn
  rw [acets_vS16 hL32]
  refine WP.branch ac_at_12bc (fun eb => ?_) (fun eb => ?_) <;> wn
  · rsimp at eb
    have hL := acets_beqTN eb
    have hL' : iss.length + ser.length < 2 ^ 16 := by omega
    refine WP.aluImm ac_at_12c4 ?_; wn
    refine WP.aluImm ac_at_12c8 ?_; wn
    refine WP.aluImm ac_at_12cc ?_; wn
    rw [acets_vA1 hL']
    refine WP.aluImm ac_at_12d0 ?_; wn
    refine WP.branch ac_at_12d2 (fun eb => ?_) (fun _ => ?_) <;> wn
    · rsimp at eb <;> exact absurd eb (by decide)
    refine WP.lui ac_at_12d6 ?_; wn
    refine WP.aluImm ac_at_12d8 ?_; wn
    refine WP.alu ac_at_12dc ?_; wn
    refine acets_lw F ac_at_12e0 (c := 0x4DAC) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide)
      (by decide) ?_; wn
    rw [K.o3C]
    refine acets_sw F ac_at_12e2 (c := 0x3A7C) (by rsimp; rw [R.rsp]; bv_omega) (by decide) (by decide) ?_; wn
    refine acets_lw F ac_at_12e4 (c := 0x4D78) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide)
      (by decide) ?_; wn
    simp (disch := omega) only [acets_ls F]
    rw [K.o8]
    refine acets_sw F ac_at_12e6 (c := 0x3A64) (by rsimp; rw [R.rsp]; bv_omega) (by decide) (by decide) ?_; wn
    refine acets_lw F ac_at_12e8 (c := 0x4DA0) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide)
      (by decide) ?_; wn
    simp (disch := omega) only [acets_ls F]
    rw [K.o30]
    refine acets_sw F ac_at_12ea (c := 0x3A6C) (by rsimp; rw [R.rsp]; bv_omega) (by decide) (by decide) ?_; wn
    refine acets_lw F ac_at_12ec (c := 0x4DA4) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide)
      (by decide) ?_; wn
    simp (disch := omega) only [acets_ls F]
    rw [K.o34]
    refine acets_sw F ac_at_12ee (c := 0x3A68) (by rsimp; rw [R.rsp]; bv_omega) (by decide) (by decide) ?_; wn
    refine acets_lw F ac_at_12f0 (c := 0x4DA8) (by rsimp; simp only [ev_add, R.rsp]; bv_omega) (by decide)
      (by decide) ?_; wn
    simp (disch := omega) only [acets_ls F]
    rw [K.o38]
    refine acets_sw F ac_at_12f2 (c := 0x3A78) (by rsimp; rw [R.rsp]; bv_omega) (by decide) (by decide) ?_; wn
    refine acets_p3b (ip := ip) (sq := sq) (kp := kp) (fp1 := fp1) O C ?_ rfl hT hL' (by acets_hr) (by rsimp <;> rfl)
      (by rsimp; simp only [ev_add, R.rsp, acSlot]; bv_omega) (by rsimp) (by rsimp) (by rsimp) (by acets_z)
      (by rsimp; exact h23) (by simp (disch := omega) only [acets_ls F]; exact K.ptr)
      (by simp (disch := omega) only [acets_ls F]; exact K.len)
    exact {
      lo := K.lo, f0 := K.f0, f1 := K.f1, i0 := K.i0, i1 := K.i1, s0 := K.s0, s1 := K.s1, k0 := K.k0,
      k1 := K.k1, nb := K.nb, na := K.na,
      hm := fun x hx => by
        have hx' := hx
        unfold AcetsO at hx'
        obtain ⟨c1, c2, -⟩ := hx'
        have := x.isLt
        simp (disch := omega) only [acets_g32 F]
        exact K.hm x hx
      hiss := by
        refine (acets_bytes (p := ip) (n := iss.length) (by omega) fun y g3 g4 => ?_).trans K.hiss
        have := y.isLt
        have ⟨_, _, _, _, _, _, _, _⟩ := acets_n O
        simp (disch := omega) only [acets_g32 F]
      hser := by
        refine (acets_bytes (p := sq) (n := ser.length) (by omega) fun y g3 g4 => ?_).trans K.hser
        have := y.isLt
        have ⟨_, _, _, _, _, _, _, _⟩ := acets_n O
        simp (disch := omega) only [acets_g32 F]
      hkey := by
        refine (acets_bytes (p := kp) (n := 0x61) (by omega) fun y g3 g4 => ?_).trans K.hkey
        have := y.isLt
        have ⟨_, _, _, _, _, _, _, _⟩ := acets_n O
        simp (disch := omega) only [acets_g32 F]
      s14 := by simp (disch := omega) only [acets_ls F, memLoad32_store32_same]
      pos := by simp (disch := omega) only [acets_ls F]; exact K.pos
      w18 := by simp (disch := omega) only [acets_ls F, memLoad32_store32_same]
      w1C := by simp (disch := omega) only [acets_ls F, memLoad32_store32_same]
      w28 := by simp (disch := omega) only [memLoad32_store32_same]
      w2C := by simp (disch := omega) only [acets_ls F, memLoad32_store32_same]
      w30 := by simp (disch := omega) only [acets_ls F]; exact K.w30 }
  · rsimp at eb
    refine WP.aluImm ac_at_12be ?_; wn
    refine WP.jal ac_at_12c2 (by decide) ?_; wn
    refine WP.aluImm ac_at_12cc ?_; wn
    refine WP.aluImm ac_at_12d0 ?_; wn
    refine WP.branch ac_at_12d2 (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact acets_f1A6A O A K.hm (.inl (Nat.le_refl _)) (.inl (Nat.le_refl _)) (by rsimp) (by rsimp; exact R.rsp)
        (by rsimp; exact R.rgp) (by rsimp; exact R.rtp) (by rsimp <;> decide)
    · rsimp at eb <;> exact absurd eb (by decide)

end Pass

end C3.RV32.Ac
