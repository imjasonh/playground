import C3BootProofs.Proofs.TufRoleKeysEnv

/-!
# `decode_key`'s comparisons, inlined in `RoleKeys::read`

`RoleKeys::read` inlines `decode_key`. After it reads the key type, the
scheme, and the public key text, it compares the scheme and the key type
with the names it knows, byte by byte, and decodes the key with `pem_spki`
or `hex_decode`. Every path ends at 0x6F4 with the key's tag in `s6` and its
bytes at `F + 0x55C`. This file holds the facts those paths share: the model
of each outcome, the step for one byte comparison, and the joins.
-/

namespace C3.Json

abbrev rkP256s : Bytes := ascii!"ecdsa-sha2-nistp256"
abbrev rkP384s : Bytes := ascii!"ecdsa-sha2-nistp384"
abbrev rkEcdsa : Bytes := ascii!"ecdsa"
abbrev rkEd : Bytes := ascii!"ed25519"

theorem rkKey_none_of {kt sc pub : Bytes} (h1 : sc ≠ rkP256s) (h2 : sc ≠ rkP384s) (h3 : kt ≠ rkEd ∨ sc ≠ rkEd) :
    rkKey kt sc pub = none := by
  unfold rkKey
  rw [if_neg (fun h => h1 h.1), if_neg (fun h => h2 h.1),
    if_neg (fun h => h3.elim (fun h3 => h3 h.1) (fun h3 => h3 h.2))]

theorem rkKey_none_256 {kt sc pub : Bytes} (hs : sc = rkP256s) (h1 : kt ≠ rkEcdsa) (h2 : kt ≠ rkP256s) :
    rkKey kt sc pub = none := by
  unfold rkKey; subst hs
  rw [if_neg (fun h => h.2.elim h1 h2), if_neg (fun h => absurd h.1 (by decide)),
    if_neg (fun h => absurd h.2 (by decide))]

theorem rkKey_none_384 {kt sc pub : Bytes} (hs : sc = rkP384s) (h1 : kt ≠ rkEcdsa) (h2 : kt ≠ rkP384s) :
    rkKey kt sc pub = none := by
  unfold rkKey; subst hs
  rw [if_neg (fun h => absurd h.1 (by decide)), if_neg (fun h => h.2.elim h1 h2),
    if_neg (fun h => absurd h.2 (by decide))]

theorem rkKey_256 {kt sc pub : Bytes} (hs : sc = rkP256s) (hk : kt = rkEcdsa ∨ kt = rkP256s) :
    rkKey kt sc pub = rkSpki 0 p256SpkiPrefix 65 pub := by
  unfold rkKey; subst hs; rw [if_pos ⟨rfl, hk⟩]

theorem rkKey_384 {kt sc pub : Bytes} (hs : sc = rkP384s) (hk : kt = rkEcdsa ∨ kt = rkP384s) :
    rkKey kt sc pub = rkSpki 1 p384SpkiPrefix 97 pub := by
  unfold rkKey; subst hs; rw [if_neg (fun h => absurd h.1 (by decide)), if_pos ⟨rfl, hk⟩]

theorem rkKey_ed {kt sc pub : Bytes} (hk : kt = rkEd) (hs : sc = rkEd) : rkKey kt sc pub = rkHex pub := by
  unfold rkKey; subst hk; subst hs
  rw [if_neg (fun h => absurd h.1 (by decide)), if_neg (fun h => absurd h.1 (by decide)), if_pos ⟨rfl, rfl⟩]

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

/-! ## Bytes compared one at a time -/

section
variable {M : Word → BitVec 8} {q : Word} {n : Nat} {L sc : Bytes}

theorem rk_mbne {j : Nat} (hj : j < n) (h : M (q + BitVec.ofNat 32 j) ≠ BitVec.ofNat 8 (L.getD j 0)) :
    memBytes M q n ≠ L := by
  intro e; apply h
  have := memBytes_getD (M := M) (p := q) hj
  rw [e] at this
  rw [this]; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]

theorem rk_ne {j : Nat} (hsc : memBytes M q n = sc) (hj : j < n)
    (h : M (q + BitVec.ofNat 32 j) ≠ BitVec.ofNat 8 (L.getD j 0)) : sc ≠ L :=
  hsc ▸ rk_mbne hj h

theorem rk_lne (hsc : memBytes M q n = sc) (h : n ≠ L.length) : sc ≠ L :=
  fun e => h (by rw [← e, ← hsc, memBytes_length])

/-- The first `i` bytes at `q` are those of `L`. -/
def RkPre (M : Word → BitVec 8) (q : Word) (L : Bytes) (i : Nat) : Prop :=
  ∀ j < i, M (q + BitVec.ofNat 32 j) = BitVec.ofNat 8 (L.getD j 0)

theorem RkPre.nil : RkPre M q L 0 := fun _ h => absurd h (Nat.not_lt_zero _)

theorem RkPre.snoc {i : Nat} (h : RkPre M q L i) (hb : M (q + BitVec.ofNat 32 i) = BitVec.ofNat 8 (L.getD i 0)) :
    RkPre M q L (i + 1) := fun j hj => by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact h j hj
  · exact hb

theorem RkPre.cast {i : Nat} {L' : Bytes} (h : RkPre M q L i) (hL : ∀ j < i, L.getD j 0 = L'.getD j 0) :
    RkPre M q L' i := fun j hj => by rw [← hL j hj]; exact h j hj

theorem RkPre.eq (h : RkPre M q L n) (hn : L.length = n) (hL : ∀ x ∈ L, x < 256) : memBytes M q n = L := by
  subst hn
  apply List.ext_getElem (by rw [memBytes_length]) fun j h1 h2 => ?_
  have hj : j < L.length := h2
  have e1 := memBytes_getD (M := M) (p := q) hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some, h j hj,
    BitVec.toNat_ofNat, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at e1
  rw [e1]; exact Nat.mod_eq_of_lt (hL _ (List.getElem_mem h2))

end

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {f : Fin 32 → Word}

/-- `lbu a1, j(r); addi a1, a1, c; bne a1, zero, tg`: compare the byte at
`q + jn` with `n`, where `c = -n`. -/
theorem rk_cmp {off o2 o3 nx tg : Nat} {r : Fin 32} {j c o l1 l2 l3 q : Word} {jn n : Nat}
    (h1 : fetchRel code off = some (.load .lbu a1 r j, l1)) (e1 : off + l1.toNat = o2)
    (h2 : fetchRel code o2 = some (.aluImm .add a1 a1 c, l2)) (e2 : o2 + l2.toNat = o3)
    (h3 : fetchRel code o3 = some (.branch .bne a1 x0 o, l3)) (e3 : o3 + l3.toNat = nx)
    (et : (o3 + o.toNat) % 2 ^ 32 = tg) (hr : f r = q) (hj : j = BitVec.ofNat 32 jn) (hn : n < 256)
    (hc : c + BitVec.ofNat 32 n = 0)
    (kne : M (q + BitVec.ofNat 32 jn) ≠ BitVec.ofNat 8 n → ∀ v, WP code base Q M tg (upd f a1 v))
    (keq : M (q + BitVec.ofNat 32 jn) = BitVec.ofNat 8 n → ∀ v, WP code base Q M nx (upd f a1 v)) :
    WP code base Q M off f := by
  refine WP.lbu h1 ?_; rw [e1]
  refine WP.aluImm h2 ?_; rw [e2]
  rw [upd_upd_same]
  have ea : upd f a1 (aluEval .add (upd f a1 ((M (f r + j)).zeroExtend 32) a1) c) a1 =
      (M (q + BitVec.ofNat 32 jn)).zeroExtend 32 + c := by
    simp only [upd_app]; rw [hr, hj]; rfl
  have ez : upd f a1 (aluEval .add (upd f a1 ((M (f r + j)).zeroExtend 32) a1) c) x0 = 0 := by
    simp only [upd_app]; rfl
  have key : ((M (q + BitVec.ofNat 32 jn)).zeroExtend 32 + c = 0) ↔ M (q + BitVec.ofNat 32 jn) = BitVec.ofNat 8 n := by
    generalize M (q + BitVec.ofNat 32 jn) = b
    constructor
    · intro h0
      have e : b.zeroExtend 32 = BitVec.ofNat 32 n :=
        calc b.zeroExtend 32 = b.zeroExtend 32 + (c + BitVec.ofNat 32 n) := by rw [hc]; exact (BitVec.add_zero _).symm
          _ = (b.zeroExtend 32 + c) + BitVec.ofNat 32 n := (BitVec.add_assoc ..).symm
          _ = BitVec.ofNat 32 n := by rw [h0]; exact BitVec.zero_add _
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := b.isLt; omega),
        Nat.mod_eq_of_lt (by omega)] at this
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    · intro e; subst e
      rw [← hc, BitVec.add_comm c]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]; omega
  refine WP.branch h3 (fun hb => ?_) (fun hb => ?_)
  · rw [et]
    refine kne (fun e => ?_) _
    rw [ea, ez] at hb
    have := key.mpr e
    simp only [branchTaken, this, bne_self_eq_false] at hb
    exact Bool.false_ne_true hb
  · rw [e3]
    refine keq (key.mp ?_) _
    rw [ea, ez] at hb
    simpa [branchTaken] using hb

theorem rk_upd_self {f : Fin 32 → Word} (hz : f 0 = 0) : upd f a1 (f a1) = f := by
  funext x; simp only [upd_app]
  by_cases h0 : x.val = 0
  · rw [if_pos h0]
    have : x = 0 := Fin.ext h0
    subst this; exact hz.symm
  · rw [if_neg h0]; split
    · next h => rw [h]
    · rfl

end

/-- The offset after a `bne a1, zero` at `o3` that branches to `tg`. -/
def rkBne (tg o3 : Nat) : Option (Instr × Word) → Option Nat
  | some (.branch .bne r1 r2 o, l) =>
    if r1 = a1 ∧ r2 = x0 ∧ (o3 + o.toNat) % 2 ^ 32 = tg then some (o3 + l.toNat) else none
  | _ => none

theorem rkBne_some {tg o3 nx : Nat} {x : Option (Instr × Word)} (h : rkBne tg o3 x = some nx) :
    ∃ o l, x = some (.branch .bne a1 x0 o, l) ∧ (o3 + o.toNat) % 2 ^ 32 = tg ∧ o3 + l.toNat = nx := by
  rcases x with _ | ⟨i, l⟩
  · cases h
  cases i with
  | branch op r1 r2 o =>
    cases op
    case bne =>
      replace h : (if r1 = a1 ∧ r2 = x0 ∧ (o3 + o.toNat) % 2 ^ 32 = tg then some (o3 + l.toNat) else none) =
        some nx := h
      by_cases hc : r1 = a1 ∧ r2 = x0 ∧ (o3 + o.toNat) % 2 ^ 32 = tg
      · rw [if_pos hc] at h
        obtain ⟨rfl, rfl, h3⟩ := hc
        exact ⟨o, l, rfl, h3, Option.some.inj h⟩
      · rw [if_neg hc] at h; cases h
    all_goals cases h
  | _ => cases h

/-- The run of byte comparisons from `off`: byte `i` and the next `c - 1`
of the pointer in `r` (or, when `rl`, of the pointer in the word at
`sp + 0xC`) against those of `L`, each branching to `tg` when they differ.
It returns the offset after the run, or `none` when the code differs. -/
def rkChain (code : List Nat) (rl : Bool) (r : Fin 32) (tg : Nat) (L : Bytes) : Nat → Nat → Nat → Option Nat
  | off, _, 0 => some off
  | off, i, c + 1 =>
    if (rl = false ∨ fetchRel code off = some (.load .lw a1 sp 0xC, 2)) ∧
        fetchRel code (if rl then off + 2 else off) =
          some (.load .lbu a1 (if rl then a1 else r) (BitVec.ofNat 32 i), 4) ∧
        fetchRel code ((if rl then off + 2 else off) + 4) =
          some (.aluImm .add a1 a1 (0 - BitVec.ofNat 32 (L.getD i 0)), 4) then
      (rkBne tg ((if rl then off + 2 else off) + 8) (fetchRel code ((if rl then off + 2 else off) + 8))).bind
        fun nx => rkChain code rl r tg L nx (i + 1) c
    else none

theorem rkChain_nil {code : List Nat} {rl : Bool} {r : Fin 32} {tg : Nat} {L : Bytes} {off i : Nat} :
    rkChain code rl r tg L off i 0 = some off := rfl

theorem rkChain_cons {code : List Nat} {rl : Bool} {r r' : Fin 32} {tg : Nat} {L : Bytes} {off i c o3 nx e : Nat}
    {jw ci o l : Word} (h1 : rl = false ∨ fetchRel code off = some (.load .lw a1 sp 0xC, 2))
    (h2 : fetchRel code (if rl then off + 2 else off) = some (.load .lbu a1 r' jw, 4))
    (hr : r' = if rl then a1 else r) (hj : jw = BitVec.ofNat 32 i)
    (h3 : fetchRel code ((if rl then off + 2 else off) + 4) = some (.aluImm .add a1 a1 ci, 4))
    (hci : ci = 0 - BitVec.ofNat 32 (L.getD i 0)) (e3 : (if rl then off + 2 else off) + 8 = o3)
    (h4 : fetchRel code o3 = some (.branch .bne a1 x0 o, l)) (het : (o3 + o.toNat) % 2 ^ 32 = tg)
    (hnx : o3 + l.toNat = nx) (h5 : rkChain code rl r tg L nx (i + 1) c = some e) :
    rkChain code rl r tg L off i (c + 1) = some e := by
  subst hr hj hci e3
  unfold rkChain
  rw [if_pos ⟨h1, h2, h3⟩, h4]
  show Option.bind (if a1 = a1 ∧ x0 = x0 ∧ _ then some (_ + l.toNat) else none) _ = _
  rw [if_pos ⟨rfl, rfl, het⟩, hnx]; exact h5

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8}

theorem rk_chain {rl : Bool} {r : Fin 32} {tg : Nat} {L : Bytes} {q F : Word} (hra : r ≠ a1) (hr0 : r.val ≠ 0)
    (hLb : ∀ x ∈ L, x < 256) :
    ∀ (c off i e : Nat) (f : Fin 32 → Word), rkChain code rl r tg L off i c = some e →
      (rl = true → f sp = F ∧ memLoad32 M (F + 0xC) = q ∧ (F + 0xC).toNat % 4 = 0) →
      (rl = false → f r = q) → RkPre M q L i →
      (∀ j v, j < i + c → RkPre M q L j → M (q + BitVec.ofNat 32 j) ≠ BitVec.ofNat 8 (L.getD j 0) →
        WP code base Q M tg (upd f a1 v)) →
      (∀ v, RkPre M q L (i + c) → WP code base Q M e (upd f a1 v)) →
      WP code base Q M off f
  | 0, off, i, e, f, h, _, _, hp, _, kend => by
    simp only [rkChain, Option.some.injEq] at h
    subst h
    refine WP.zero fun hz => ?_
    rw [← rk_upd_self hz]; exact kend _ hp
  | c + 1, off, i, e, f, h, hl, hr, hp, kne, kend => by
    unfold rkChain at h
    by_cases hc : (rl = false ∨ fetchRel code off = some (.load .lw a1 sp 0xC, 2)) ∧
        fetchRel code (if rl then off + 2 else off) =
          some (.load .lbu a1 (if rl then a1 else r) (BitVec.ofNat 32 i), 4) ∧
        fetchRel code ((if rl then off + 2 else off) + 4) =
          some (.aluImm .add a1 a1 (0 - BitVec.ofNat 32 (L.getD i 0)), 4)
    · rw [if_pos hc] at h
      obtain ⟨hlw, hlbu, hadd⟩ := hc
      rcases hb : rkBne tg ((if rl then off + 2 else off) + 8) (fetchRel code ((if rl then off + 2 else off) + 8))
        with _ | nx
      · rw [hb] at h; cases h
      rw [hb] at h
      obtain ⟨o, l, hbr, het, hnx⟩ := rkBne_some hb
      have h' : rkChain code rl r tg L nx (i + 1) c = some e := h
      have hgd : L.getD i 0 < 256 := by
        rw [List.getD_eq_getElem?_getD]
        rcases hh : L[i]? with _ | x
        · decide
        · exact hLb x (List.mem_of_getElem? hh)
      have step : ∀ g : Fin 32 → Word, g (if rl then a1 else r) = q → (∀ v, upd g a1 v = upd f a1 v) →
          WP code base Q M (if rl then off + 2 else off) g := fun g hg hgf =>
        rk_cmp (n := L.getD i 0) (jn := i) hlbu rfl hadd rfl hbr hnx het hg rfl hgd
          (BitVec.sub_add_cancel _ _)
          (fun hne v => by rw [hgf]; exact kne i v (by omega) hp hne)
          (fun heq v => rk_chain hra hr0 hLb c nx (i + 1) e (upd g a1 v) h'
            (fun h1 => by rw [hgf]; obtain ⟨a, b, d⟩ := hl h1; exact ⟨by rsimp; exact a, b, d⟩)
            (fun h1 => by rw [hgf]; simp only [upd_app, if_neg hr0, if_neg hra]; exact hr h1) (hp.snoc heq)
            (fun j v' hji hj hne => by rw [upd_upd_same, hgf]; exact kne j _ (by omega) hj hne)
            (fun v' hj => by rw [upd_upd_same, hgf]; exact kend _ (by
              rw [show i + (c + 1) = i + 1 + c by omega]; exact hj)))
      cases rl
      · exact step f (hr rfl) (fun _ => rfl)
      · obtain ⟨hsp, hq, hal⟩ := hl rfl
        rcases hlw with hlw | hlw
        · exact absurd hlw (by decide)
        refine WP.lw hlw (by rw [hsp]; exact hal) ?_
        exact step _ (by rsimp; rw [hsp, hq]) (fun v => upd_upd_same _ _ _ _)
    · rw [if_neg hc] at h; cases h

end

/-! ## The state at 0x6F4

The loop body reads the key at 0x6F4 from `s6`, the tag, and from the 97
bytes at `F + 0x55C`. On the way there `decode_key` may change the
registers in `rkDc`, sets `s7` back to the loop's bound 9, and changes
memory only in its frame below `F + 0x18`, between the keys at
`F + 0x18` and the array cursor at `F + 0xA6C`, and in the 20 bytes from
`F + 0xA78` below the saved registers. -/

/-- The registers `decode_key` may change. -/
abbrev rkDc : List (Fin 32) := jClob ++ [ra, 8, 9, 22, 23]

/-- `M` is `Md` but in the frame parts `decode_key` writes. -/
def RkW (s : Word) (Md M : Word → BitVec 8) : Prop :=
  ∀ x, Sep x 1 s 328 → Sep x 1 (s + BitVec.ofNat 32 1672) 1300 → Sep x 1 (s + BitVec.ofNat 32 2984) 20 →
    M x = Md x

/-- The tag byte of a key, 0xFF for none. -/
def rkTag : Option (Nat × Bytes) → BitVec 8
  | none => 0xFF
  | some (t, _) => BitVec.ofNat 8 t

/-- The bytes of the key at `F + 0x55C`. -/
def RkKB (F : Word) (M : Word → BitVec 8) : Option (Nat × Bytes) → Prop
  | none => True
  | some (_, k) => k.length ≤ 97 ∧ memBytes M (F + 0x55C) k.length = k

/-- What the loop goes on with at 0x6F4 after the key `key`. -/
def RkK (Q : Post) (s F : Word) (gL : Fin 32 → Word) (Md : Word → BitVec 8) (key : Option (Nat × Bytes)) :
    Prop :=
  ∀ (g : Fin 32 → Word) (M : Word → BitVec 8), (∀ x, x ∉ rkDc → g x = gL x) → g 23 = 9 → RkW s Md M →
    (g 22).extractLsb' 0 8 = rkTag key → RkKB F M key → WP tufRoleKeysReadCode TRK Q M 0x6F4 g

theorem RkW.refl {s : Word} {M : Word → BitVec 8} : RkW s M M := fun _ _ _ _ => rfl

/-- A part of the frame `decode_key` writes, as offsets from `s`. -/
def RkWr (c k : Nat) : Prop := c + k ≤ 328 ∨ (1672 ≤ c ∧ c + k ≤ 2972) ∨ (2984 ≤ c ∧ c + k ≤ 3004)

theorem RkWr.sep {s x : Word} {c k : Nat} (hr : RkWr c k) (h1 : Sep x 1 s 328)
    (h2 : Sep x 1 (s + BitVec.ofNat 32 1672) 1300) (h3 : Sep x 1 (s + BitVec.ofNat 32 2984) 20) :
    Sep x 1 (s + BitVec.ofNat 32 c) k := by
  rcases hr with hr | ⟨hc, hr⟩ | ⟨hc, hr⟩
  · exact (h1.symm.sub (c := c) (l := k) (by omega)).symm
  · have := (h2.symm.sub (c := c - 1672) (l := k) (by omega)).symm
    rwa [add_ofNat_assoc, show 1672 + (c - 1672) = c by omega] at this
  · have := (h3.symm.sub (c := c - 2984) (l := k) (by omega)).symm
    rwa [add_ofNat_assoc, show 2984 + (c - 2984) = c by omega] at this

theorem RkW.out {s : Word} {Md M M' : Word → BitVec 8} {c k : Nat} (h : RkW s Md M)
    (hO : Out M M' (s + BitVec.ofNat 32 c) k) (hr : RkWr c k) : RkW s Md M' := fun x h1 h2 h3 => by
  rw [← h x h1 h2 h3]; exact hO x (hr.sep h1 h2 h3)

theorem RkW.out2 {s : Word} {Md M M' : Word → BitVec 8} {c1 k1 c2 k2 : Nat} (h : RkW s Md M)
    (hO : ∀ x, Sep x 1 (s + BitVec.ofNat 32 c1) k1 → Sep x 1 (s + BitVec.ofNat 32 c2) k2 → M' x = M x)
    (hr1 : RkWr c1 k1) (hr2 : RkWr c2 k2) : RkW s Md M' := fun x h1 h2 h3 => by
  rw [← h x h1 h2 h3]; exact hO x (hr1.sep h1 h2 h3) (hr2.sep h1 h2 h3)

theorem RkW.trans {s : Word} {Md M M' : Word → BitVec 8} (h : RkW s Md M) (h' : RkW s M M') : RkW s Md M' :=
  fun x h1 h2 h3 => (h' x h1 h2 h3).trans (h x h1 h2 h3)

/-- The bytes `decode_key` leaves as they were. -/
theorem RkW.outer {s : Word} {Md M : Word → BitVec 8} (h : RkW s Md M) : Out Md M s 3004 := fun x hx => by
  have h1 := (hx.symm.sub (c := 0) (l := 328) (by decide)).symm
  rw [add_ofNat_zero] at h1
  exact h x h1 (hx.symm.sub (c := 1672) (l := 1300) (by decide)).symm
    (hx.symm.sub (c := 2984) (l := 20) (by decide)).symm

theorem rk_keepS {f g0 : Fin 32 → Word} {cl : List (Fin 32)} {rd : Fin 32} {v : Word} (hv : v = g0 rd)
    (hz : g0 0 = 0) (hfr : ∀ x, x ∉ cl → f x = g0 x) : ∀ x, x ∉ cl → upd f rd v x = g0 x := by
  intro x hx
  by_cases h0 : x.val = 0
  · rw [show x = 0 from Fin.ext h0, hz]; rfl
  · simp only [upd_app, h0, ↓reduceIte]
    split
    · next h => rw [h, hv]
    · exact hfr x hx

theorem rk_a6c (F : Word) : aluEval .add (aluEval .add F 0x7FF) 0x26D = F + 0xA6C := by
  rw [ev_add, ev_add, BitVec.add_assoc]; rfl

section
variable {Q : Post} {s F : Word} {gL g : Fin 32 → Word} {Md M : Word → BitVec 8} {key : Option (Nat × Bytes)}

theorem rk_632 (hL0 : gL 0 = 0) (hk : ∀ x, x ∉ rkDc → g x = gL x) (h23 : g 23 = 9) (hW : RkW s Md M)
    (ha0 : (g a0).extractLsb' 0 8 = rkTag key) (hKB : RkKB F M key) (K : RkK Q s F gL Md key) :
    WP tufRoleKeysReadCode TRK Q M 0x632 g := by
  refine WP.alu rkr_at_632 ?_; wn
  refine WP.jal rkr_at_634 (by decide) ?_; wn
  exact K _ _ (by keepz hL0) (by rsimp; exact h23) hW (by rsimp; rw [hk 0 (by decide), hL0, ev0]; exact ha0) hKB

theorem rk_630 (hL0 : gL 0 = 0) (hk : ∀ x, x ∉ rkDc → g x = gL x) (hW : RkW s Md M)
    (ha0 : (g a0).extractLsb' 0 8 = rkTag key) (hKB : RkKB F M key) (K : RkK Q s F gL Md key) :
    WP tufRoleKeysReadCode TRK Q M 0x630 g := by
  refine WP.aluImm rkr_at_630 ?_; wn
  exact rk_632 hL0 (by keepz hL0) (by rsimp; rw [hk 0 (by decide), hL0]; rfl) hW (by rsimp; exact ha0) hKB K

theorem rk_628 (hL0 : gL 0 = 0) (hLsp : gL sp = F) (hL24 : gL 24 = F + 0xA6C) (hk : ∀ x, x ∉ rkDc → g x = gL x)
    (hW : RkW s Md M) (ha0 : (g a0).extractLsb' 0 8 = rkTag key) (hKB : RkKB F M key) (K : RkK Q s F gL Md key) :
    WP tufRoleKeysReadCode TRK Q M 0x628 g := by
  refine WP.aluImm rkr_at_628 ?_; wn
  refine WP.aluImm rkr_at_62c ?_; wn
  refine rk_630 hL0 (rk_keepS (by rw [hk sp (by decide), hLsp, hL24, rk_a6c]) hL0 hk) hW (by rsimp; exact ha0) hKB K

theorem rk_6f2 (hL0 : gL 0 = 0) (hk : ∀ x, x ∉ rkDc → g x = gL x) (hW : RkW s Md M)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (K : RkK Q s F gL Md none) :
    WP tufRoleKeysReadCode TRK Q M 0x6F2 g := by
  refine WP.aluImm rkr_at_6f2 ?_; wn
  exact K _ _ (by keepz hL0) (by rsimp; rw [hk 0 (by decide), hL0]; rfl) hW (by rsimp; exact h22) trivial

theorem rk_6ea (hL0 : gL 0 = 0) (hLsp : gL sp = F) (hL24 : gL 24 = F + 0xA6C) (hk : ∀ x, x ∉ rkDc → g x = gL x)
    (hW : RkW s Md M) (h22 : (g 22).extractLsb' 0 8 = 0xFF) (K : RkK Q s F gL Md none) :
    WP tufRoleKeysReadCode TRK Q M 0x6EA g := by
  refine WP.aluImm rkr_at_6ea ?_; wn
  refine WP.aluImm rkr_at_6ee ?_; wn
  refine rk_6f2 hL0 (rk_keepS (by rw [hk sp (by decide), hLsp, hL24, rk_a6c]) hL0 hk) hW (by rsimp; exact h22) K

end

end C3.RV32
