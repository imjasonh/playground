import C3BootProofs.Proofs.AcceptExtractTlogLib

/-!
# The transparency log loop, from 0xEBA to 0x123A

Each pass of the loop at 0xEBA takes the next item of `tlogs` with
`next_element` and reads it as `logEntry` does: the `publicKey` object, its
`keyDetails`, its `rawBytes` decoded into `keys`'s free part, the key check,
the `baseUrl` with its trailing slashes dropped, and `validFor`. An Ed25519
key goes into the array at `sp + 0x350`, counted at `sp + 0x2C`; any other
key type skips the item. When the items run out, the code zeroes the TSA
array at `sp + 0x890` and opens a cursor over `timestampAuthorities` at
`sp + 0x1DC8`.

The loop's invariant is `AceTlogInv`: the items left are `rest`, and the
keys the array holds are `aceKeys logEntry` of the items before them, which
is `tlogs.mapM logEntry` with the skipped items filtered out.

Within a pass, memory is tracked against a snapshot `Ms`: the callees write
only the ranges of `acetlWc`, so the current memory agrees with `Ms` outside
them (`AcetlV`), and `Ms` agrees with the machine at the start of the pass
outside `acetlW` (`AcetlU`). The pass's own stores, at `sp + 0x1C` and
`sp + 0x28`, and `decode`'s writes start a new snapshot.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

set_option maxRecDepth 100000

/-- At 0xEBA after a pass: the state the next pass starts from. -/
def acetlNx (X : AceCtx) (jr : Json) (fs : List FulcioKey) (rest : List Json) (n : Machine) : Prop :=
  ∃ fp ls, AceAt X n 0xEBA fp ∧ AceTlogInv X n fp jr fs rest ls

/-! ## Frame facts -/

section
variable {X : AceCtx} (O : X.Ok)
include O

/-- A slot of the frame outside `acetlW` and the slice at `sp + 0x1FDC`. -/
theorem acetl_U_slot {fp : Word} {d : Bool} (hfp : X.Bf.toNat + 0x6800 ≤ fp.toNat) {k : Nat}
    (hk : 0x3A50 + k < 0x5A70) (hW : ∀ r ∈ acetlW, 0x3A50 + k < r.1 ∨ r.2 ≤ 0x3A50 + k)
    (hd : 0x3A50 + k < 0x5A2C ∨ 0x5A34 ≤ 0x3A50 + k) : AcetlU X.B X.Bf fp d (acSlot X.B k) := by
  have F := O.lay.fr
  have hx : (acSlot X.B k).toNat = X.B.toNat + (0x3A50 + k) := F.at _ (by omega)
  have hbuf : Sep (acSlot X.B k) 1 X.Bf acBufLen := O.lay.sep.sub (c := 0x3A50 + k) (l := 1) (by omega)
  have hb := ace_ofSep hbuf
  have hbw := O.lay.hi
  unfold acBufLen at hb hbw
  refine ⟨fun r hm => ?_, fun _ => ⟨?_, ?_⟩⟩
  · rcases hW r hm with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  · rcases hb with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  · rcases hd with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)

/-- What `AceKept` names is outside a pass's writes. -/
theorem acetl_U_kept {fp : Word} {d : Bool} (hfp : X.Bf.toNat + 0x6800 ≤ fp.toNat)
    (hfp' : fp.toNat ≤ X.Bf.toNat + 0xB840) {x : Word} (h : AceKept X.B X.Bf x) :
    AcetlU X.B X.Bf fp d x ∧ Sep x 1 (acSlot X.B 0x350) 0x200 ∧ Sep x 1 (acSlot X.B 0x2C) 4 := by
  have F := O.lay.fr
  rcases h with ⟨h1, h2⟩ | ⟨k, hk, rfl⟩
  · have a1 := ace_ofSep h1
    have a2 := ace_ofSep h2
    have hb := O.lay.hi
    unfold acBufLen at hb
    have e : (X.Bf + 0x6800).toNat = X.Bf.toNat + 0x6800 := by
      rw [BitVec.toNat_add]; have : (0x6800 : Word).toNat = 0x6800 := rfl; omega
    rw [e] at a2
    refine ⟨acetl_U_out a1 (by omega), ace_sepX F (by decide) ?_, ace_sepX F (by decide) ?_⟩ <;>
    · have := F.hi; omega
  · have hk' : k < 0x244 := by omega
    refine ⟨acetl_U_slot O hfp (by omega) (fun r hr => ?_) (by omega), ?_, ?_⟩
    · simp only [acetlW, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega
    · rw [show acSlot X.B k = X.B + BitVec.ofNat 32 (0x3A50 + k + 0) from rfl]
      exact ace_sepB' F (by omega) (by omega) (by decide)
    · rw [show acSlot X.B k = X.B + BitVec.ofNat 32 (0x3A50 + k + 0) from rfl]
      exact ace_sepB' F (by omega) (by omega) (by decide)

/-- The closure's code is outside a pass's writes. -/
theorem acetl_U_code {fp : Word} {d : Bool} (hfp : X.Bf.toNat + 0x6800 ≤ fp.toNat) {i : Nat}
    (hi : i < bootMainClosure0Code.length) :
    AcetlU X.B X.Bf fp d (AC + BitVec.ofNat 32 i) ∧ Sep (AC + BitVec.ofNat 32 i) 1 (acSlot X.B 0x350) 0x200 ∧
      Sep (AC + BitVec.ofNat 32 i) 1 (acSlot X.B 0x2C) 4 := by
  have F := O.lay.fr
  have h1 := ace_AC
  have hi32 : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  have h : (AC + BitVec.ofNat 32 i).toNat = AC.toNat + i := by rw [BitVec.toNat_add, hi32]; omega
  have hh := F.hi
  have hb := O.lay.hi
  unfold acBufLen at hb
  refine ⟨acetl_U_out (.inr (by omega)) (.inr (by omega)), ace_sepX F (by decide) (.inr ?_),
    ace_sepX F (by decide) (.inr ?_)⟩ <;> omega

/-- The document is outside a pass's writes. -/
theorem acetl_U_doc {fp : Word} {d : Bool} (hfp : X.Bf.toNat + 0x6800 ≤ fp.toNat) {i : Nat}
    (hi : i < X.json.length) :
    AcetlU X.B X.Bf fp d (X.D + BitVec.ofNat 32 i) ∧ AceKept X.B X.Bf (X.D + BitVec.ofNat 32 i) := by
  have hlo := O.pre.docLo; have hhi := O.pre.docHi; have hb := O.lay.hi; have hh := O.lay.fr.hi
  unfold acBufLen at hb
  have hx : (X.D + BitVec.ofNat 32 i).toNat = X.D.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hs := ace_ofSep (ace_bufOut O.lay (y := X.D + BitVec.ofNat 32 i) (by omega) (by unfold acBufLen; omega))
  refine ⟨acetl_U_out hs (.inl (by omega)), .inl ⟨?_, ?_⟩⟩
  · rcases hs with h | h
    · exact sep_of_le (by omega) (by omega)
    · exact (sep_of_le (by omega) (by have := (X.D + BitVec.ofNat 32 i).isLt; omega)).symm
  · have e : (X.Bf + 0x6800).toNat = X.Bf.toNat + 0x6800 := by
      rw [BitVec.toNat_add]; have : (0x6800 : Word).toNat = 0x6800 := rfl; omega
    exact sep_of_le (by omega) (by rw [e]; omega)

end

/-- The document's bytes, in memory that keeps the machine at the start of
a pass outside its writes. -/
theorem acetl_doc {X : AceCtx} (O : X.Ok) {n0 : Machine} {fp0 : Word} (A : AceAt X n0 0xEBA fp0)
    {M : Word → BitVec 8} (hm : ∀ x, AcetlU X.B X.Bf fp0 true x → M x = n0.mem x) {p : Word} {n : Nat}
    (h1 : X.D.toNat ≤ p.toNat) (h2 : p.toNat + n ≤ X.D.toNat + X.json.length) :
    memBytes M p n = slice X.json (p.toNat - X.D.toNat) n := by
  have hfp := A.fr.lo
  have hd : memBytes M X.D X.json.length = X.json := by
    refine (ace_memBytes_ext (M := X.K.mem) fun i hi => ?_).trans O.pre.doc
    obtain ⟨hu, hk⟩ := acetl_U_doc O hfp hi
    rw [hm _ hu, A.keep.mem _ hk]
  have hhi := O.pre.docHi; have hb := O.lay.hi
  have e : p = X.D + BitVec.ofNat 32 (p.toNat - X.D.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := p.isLt; omega
  have h := tuf_memBytes_drop_take (M := M) (p := X.D) (n := X.json.length) (h := p.toNat - X.D.toNat) (l := n)
    (by omega)
  rw [hd, ← e] at h
  exact h.symm

/-- An entry whose names and keys lie below `fp` lies below any `fp'`
above it. -/
theorem acetl_entry_fp {Bf fp fp' : Word} {M : Word → BitVec 8} {e : Word} {name key : Bytes} {n : Nat}
    {w : Window} (h : AceEntryIn Bf fp M e name key n w) (hf : fp.toNat ≤ fp'.toNat) :
    AceEntryIn Bf fp' M e name key n w :=
  ⟨⟨h.name.1, by have := h.name.2.1; omega, h.name.2.2⟩, h.notBefore, h.notAfter,
    ⟨h.key.1, by have := h.key.2.1; omega, h.key.2.2⟩⟩

/-! ## The next pass -/

section
variable {X : AceCtx} {n0 : Machine} {fp0 : Word} {jr : Json} {fs : List FulcioKey} {j : Json}
  {rest : List Json} {ls : List LogKey} {M : Word → BitVec 8} {f : Fin 32 → Word}

/-- `AcInv` and the result pointer, from memory that keeps the machine at
the start of the pass outside its writes, the log array, and the count. -/
theorem acetl_inv' (O : X.Ok) (A : AceAt X n0 0xEBA fp0)
    (hm : ∀ x, AcetlU X.B X.Bf fp0 true x → Sep x 1 (acSlot X.B 0x350) 0x200 → Sep x 1 (acSlot X.B 0x2C) 4 →
      M x = n0.mem x)
    {n : Machine} (hn : n.mem = M) (h2 : reg n (2 : Fin 32) = X.B + 0x3A50) (h3 : reg n (3 : Fin 32) = X.g)
    (h4 : reg n (4 : Fin 32) = X.t) :
    AcInv X.B X.Bf X.g X.t X.v X.M0 n ∧ memLoad32 n.mem (acSlot X.B 0x40) = X.r := by
  have F := O.lay.fr
  have hh := F.hi
  have hfp := A.fr.lo
  have hm' : ∀ k, 0x3A50 + k + 4 ≤ 0x5A70 →
      0x3A50 + 0x350 + 0x200 ≤ 0x3A50 + k ∨ k + 4 ≤ 0x2C ∨ (0x30 ≤ k ∧ k + 4 ≤ 0x350) →
      ∀ j, j < 4 → AcetlU X.B X.Bf fp0 true (acSlot X.B k + BitVec.ofNat 32 j) →
      M (acSlot X.B k + BitVec.ofNat 32 j) = n0.mem (acSlot X.B k + BitVec.ofNat 32 j) := by
    intro k hk hs j hj hu
    refine hm _ hu ?_ ?_ <;> rw [ace_slot] <;> exact ace_sepB' F (by omega) (by omega) (by decide)
  refine ⟨⟨h2, h3, h4, fun k hk => ?_, fun x h1 h2 => ?_⟩, ?_⟩
  · rw [hn, ← A.inv.saves k hk]
    have e : X.B + BitVec.ofNat 32 (0x5A6C - 4 * k) = acSlot X.B (0x201C - 4 * k) := by
      rw [show acSlot X.B (0x201C - 4 * k) = X.B + BitVec.ofNat 32 (0x3A50 + (0x201C - 4 * k)) from rfl]
      congr 2; omega
    rw [e]
    refine ace_load_eq fun j hj => hm' _ (by omega) (.inl (by omega)) j hj ?_
    refine acetl_U_at' O hfp (l := 4) (by omega) (fun r hr => .inr ?_) (.inr (by omega)) hj
    have := acetlW_le r hr; omega
  · have hfh := A.fr.hi
    have a1 := ace_ofSep h1
    have a2 := ace_ofSep h2
    unfold acBufLen at a2
    rw [hn, hm x (acetl_U_out a1 (by omega)) (ace_sepX F (by decide) (by omega))
      (ace_sepX F (by decide) (by omega))]
    exact A.inv.out x h1 h2
  · rw [hn, ← O.pre.res]
    refine ace_load_eq fun j hj => ?_
    rw [hm' 0x40 (by decide) (.inr (.inr ⟨by decide, by decide⟩)) j hj (acetl_U_at O hfp (l := 4) (by decide) (by decide) (by decide) hj)]
    exact A.keep.mem _ (.inr ⟨0x40 + j, .inl ⟨by omega, by omega⟩, by rw [ace_slot, Nat.add_assoc]⟩)

set_option maxHeartbeats 4000000 in
/-- At 0xEBA after a pass: the next pass's `AceAt` and `AceTlogInv`. -/
theorem acetl_close (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs (j :: rest) ls)
    (R : AceHR X f) (h26 : f 26 = reg n0 26) {fp1 : Word} (hf1 : fp0.toNat ≤ fp1.toNat)
    (hf2 : fp1.toNat ≤ X.Bf.toNat + 0xB840) (hp : memLoad32 M (acSlot X.B 0x1FDC) = fp1)
    (hl : memLoad32 M (acSlot X.B 0x1FE0) = BitVec.ofNat 32 (X.Bf.toNat + 0xB840 - fp1.toNat))
    (hk : ∀ x, AcetlU X.B X.Bf fp0 true x → Sep x 1 (acSlot X.B 0x350) 0x200 → Sep x 1 (acSlot X.B 0x2C) 4 →
      M x = n0.mem x)
    (hcur : AceCur X.D X.json M (acSlot X.B 0x1860) rest) {ls' : List LogKey}
    (hprog : AceProg jr (ascii!"tlogs") logEntry rest ls') (hlogs : AceLogsAt X.Bf fp1 M (acSlot X.B 0x350) ls')
    (hcnt : memLoad32 M (acSlot X.B 0x2C) = BitVec.ofNat 32 ls'.length) :
    acetlQ X 0xEBA (acetlNx X jr fs rest) (AC + BitVec.ofNat 32 0xEBA) M f := by
  intro n hpc hn hr
  have F := O.lay.fr
  have hfp := A.fr.lo
  have hfh := A.fr.hi
  obtain ⟨hI, -⟩ := acetl_inv' O A hk hn (by rw [hr]; exact R.rsp) (by rw [hr]; exact R.rgp) (by rw [hr]; exact R.rtp)
  have hld : ∀ s, 0x3A50 + s + 4 ≤ 0x5A70 →
      acetlW.all (fun r => decide (0x3A50 + s + 4 ≤ r.1) || decide (r.2 ≤ 0x3A50 + s)) = true →
      (decide (0x3A50 + s + 4 ≤ 0x5A2C) || decide (0x5A34 ≤ 0x3A50 + s)) = true →
      (0x3A50 + 0x350 + 0x200 ≤ 0x3A50 + s ∨ s + 4 ≤ 0x2C ∨ (0x30 ≤ s ∧ s + 4 ≤ 0x350)) →
      memLoad32 M (acSlot X.B s) = memLoad32 n0.mem (acSlot X.B s) := by
    intro s hs hr hd hs'
    refine ace_load_eq fun j hj => hk _ (acetl_U_at O hfp hs hr hd hj) ?_ ?_ <;> rw [ace_slot] <;>
      exact ace_sepB' F (by omega) (by omega) (by decide)
  have hbuf : ∀ y : Word, X.Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp0.toNat → M y = n0.mem y := by
    intro y h1 h2
    have hs := ace_ofSep (ace_bufOut O.lay (y := y) (by omega) (by unfold acBufLen; omega))
    refine hk y (acetl_U_out hs (.inl h2)) ?_ ?_ <;> exact ace_sepX F (by decide) (by have := F.hi; omega)
  refine ⟨hI, .inr ⟨hpc, fp1, ls', ⟨fun i hi => ?_, ⟨hpc, rfl, fun _ => rfl⟩, hI, ⟨by rw [hn]; exact hp,
    by rw [hn]; exact hl, by omega, hf2⟩, ⟨fun x hx => ?_, fun q hq => ?_⟩, ?_⟩,
    ⟨I.root, ?_, I.cas, hprog, by rw [hn]; exact hcur, ?_, by rw [hn]; exact hlogs, by rw [hn]; exact hcnt,
      by rw [hr]; exact R.r19⟩⟩⟩
  · obtain ⟨h1, h2, h3⟩ := acetl_U_code O hfp hi
    rw [hn, hk _ h1 h2 h3]; exact A.code i hi
  · obtain ⟨h1, h2, h3⟩ := acetl_U_kept O hfp hfh hx
    rw [hn, hk _ h1 h2 h3]; exact A.keep.mem x hx
  · have : q = 21 ∨ q = 25 ∨ q = 27 := by revert hq; revert q; decide
    rcases this with rfl | rfl | rfl <;> rw [hr]
    · exact R.r21
    · exact R.r25
    · exact R.r27
  · unfold AceExpiry
    rw [← A.exp, hn]
    unfold aceU64
    rw [hld 0x20 (by decide) (by decide) (by decide) (.inr (.inl (by decide)))]
    rw [show acSlot X.B 0x20 + 4 = acSlot X.B 0x24 by unfold acSlot; rw [BitVec.add_assoc]; rfl,
      hld 0x24 (by decide) (by decide) (by decide) (.inr (.inl (by decide)))]
  · unfold AceObj
    rw [hr, h26, hn, hld 0x30 (by decide) (by decide) (by decide) (.inr (.inr ⟨by decide, by decide⟩))]
    exact I.obj
  · rw [hn]
    refine SvArrayAt.mono (ace_array_move I.fulcio (fun c hc => ?_) hbuf) fun e k h => acetl_entry_fp h hf1
    have e : acSlot X.B 0x1ED0 + BitVec.ofNat 32 c = acSlot X.B (0x1ED0 + c) := by
      rw [ace_slot, Nat.add_assoc]
    rw [e]
    refine hk _ (acetl_U_slot O hfp (k := 0x1ED0 + c) (by omega) (fun r hr => ?_) (by omega)) ?_ ?_
    · simp only [acetlW, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega
    · exact ace_sepB' F (by omega) (by omega) (by decide)
    · exact ace_sepB' F (by omega) (by omega) (by decide)

end

/-! ## The push at 0x1160 -/

/-- Memory after the push: the entry's seven words at `sp + E` and the
count. -/
def acetlPush (M : Word → BitVec 8) (B : Word) (E : Nat) (v0 v1 v2 v3 v4 v5 v6 c : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M
    (acSlot B (E + 0)) v0) (acSlot B (E + 4)) v1) (acSlot B (E + 8)) v2) (acSlot B (E + 0xC)) v3)
    (acSlot B (E + 0x10)) v4) (acSlot B (E + 0x14)) v5) (acSlot B (E + 0x18)) v6) (acSlot B 0x2C) c

theorem acetl_slot4 (B : Word) {s i t : Nat} (h : s + i = t) : acSlot B s + BitVec.ofNat 32 i = acSlot B t := by
  subst h; rw [ace_slot, Nat.add_assoc]

theorem acetl_getS {B x : Word} {M : Word → BitVec 8} {v : Word} {a n s : Nat} (hx : Sep x 1 (acSlot B a) n)
    (h1 : a ≤ s) (h2 : s + 4 ≤ a + n) : memStore32 M (acSlot B s) v x = M x := by
  have := hx.symm.sub (c := s - a) (l := 4) (by omega)
  rw [acetl_slot4 B (t := s) (by omega)] at this
  exact memStore32_get_sep this

theorem acetl_getO {B x : Word} (F : Fr B 0x5A70) {M : Word → BitVec 8} {v : Word} {s : Nat}
    (h : x.toNat < B.toNat ∨ B.toNat + 0x5A70 ≤ x.toNat) (hs : 0x3A50 + s + 4 ≤ 0x5A70) :
    memStore32 M (acSlot B s) v x = M x := by
  refine memStore32_get_sep (ace_sepX F (c := 0x3A50 + s) (n := 4) hs ?_).symm
  rcases h with h | h
  · exact .inl (by omega)
  · exact .inr (by omega)

theorem acetl_ldS {B : Word} (F : Fr B 0x5A70) {M : Word → BitVec 8} {v : Word} {s t : Nat}
    (h : s + 4 ≤ t ∨ t + 4 ≤ s) (hs : 0x3A50 + s + 4 ≤ 0x5A70) (ht : 0x3A50 + t + 4 ≤ 0x5A70) :
    memLoad32 (memStore32 M (acSlot B s) v) (acSlot B t) = memLoad32 M (acSlot B t) :=
  memLoad32_store32_sep (ace_sepB' F (by omega) hs ht)

theorem acetl_getB {B : Word} (F : Fr B 0x5A70) {M : Word → BitVec 8} {v : Word} {s t : Nat}
    (h : s + 4 ≤ t ∨ t + 1 ≤ s) (hs : 0x3A50 + s + 4 ≤ 0x5A70) (ht : 0x3A50 + t + 1 ≤ 0x5A70) :
    memStore32 M (acSlot B s) v (acSlot B t) = M (acSlot B t) :=
  memStore32_get_sep (ace_sepB' F (by omega) hs ht)

section
variable {M : Word → BitVec 8} {B : Word} {E : Nat} {v0 v1 v2 v3 v4 v5 v6 c : Word}

theorem acetl_push_get {x : Word} (hE : 0x350 ≤ E ∧ E + 0x20 ≤ 0x550) (ha : Sep x 1 (acSlot B 0x350) 0x200)
    (hc : Sep x 1 (acSlot B 0x2C) 4) : acetlPush M B E v0 v1 v2 v3 v4 v5 v6 c x = M x := by
  unfold acetlPush
  rw [acetl_getS hc (s := 0x2C) (by omega) (by omega), acetl_getS ha (s := E + 0x18) (by omega) (by omega),
    acetl_getS ha (s := E + 0x14) (by omega) (by omega), acetl_getS ha (s := E + 0x10) (by omega) (by omega),
    acetl_getS ha (s := E + 0xC) (by omega) (by omega), acetl_getS ha (s := E + 8) (by omega) (by omega),
    acetl_getS ha (s := E + 4) (by omega) (by omega), acetl_getS ha (s := E + 0) (by omega) (by omega)]

theorem acetl_push_out (F : Fr B 0x5A70) {x : Word} (hE : 0x350 ≤ E ∧ E + 0x20 ≤ 0x550)
    (h : x.toNat < B.toNat ∨ B.toNat + 0x5A70 ≤ x.toNat) : acetlPush M B E v0 v1 v2 v3 v4 v5 v6 c x = M x := by
  unfold acetlPush
  rw [acetl_getO F h (by omega), acetl_getO F h (by omega), acetl_getO F h (by omega), acetl_getO F h (by omega),
    acetl_getO F h (by omega), acetl_getO F h (by omega), acetl_getO F h (by omega), acetl_getO F h (by omega)]

theorem acetl_push_ld (F : Fr B 0x5A70) {t : Nat} (hE : 0x350 ≤ E ∧ E + 0x20 ≤ 0x550)
    (ht : 0x3A50 + t + 4 ≤ 0x5A70) (h1 : t + 4 ≤ E ∨ E + 0x1C ≤ t) (h2 : t + 4 ≤ 0x2C ∨ 0x30 ≤ t) :
    memLoad32 (acetlPush M B E v0 v1 v2 v3 v4 v5 v6 c) (acSlot B t) = memLoad32 M (acSlot B t) := by
  unfold acetlPush
  rw [acetl_ldS F (s := 0x2C) (by omega) (by omega) ht, acetl_ldS F (s := E + 0x18) (by omega) (by omega) ht,
    acetl_ldS F (s := E + 0x14) (by omega) (by omega) ht, acetl_ldS F (s := E + 0x10) (by omega) (by omega) ht,
    acetl_ldS F (s := E + 0xC) (by omega) (by omega) ht, acetl_ldS F (s := E + 8) (by omega) (by omega) ht,
    acetl_ldS F (s := E + 4) (by omega) (by omega) ht, acetl_ldS F (s := E + 0) (by omega) (by omega) ht]

theorem acetl_push_e (F : Fr B 0x5A70) (hE : 0x350 ≤ E ∧ E + 0x20 ≤ 0x550) :
    let N := acetlPush M B E v0 v1 v2 v3 v4 v5 v6 c
    memLoad32 N (acSlot B (E + 0)) = v0 ∧ memLoad32 N (acSlot B (E + 4)) = v1 ∧
      memLoad32 N (acSlot B (E + 8)) = v2 ∧ memLoad32 N (acSlot B (E + 0xC)) = v3 ∧
      memLoad32 N (acSlot B (E + 0x10)) = v4 ∧ memLoad32 N (acSlot B (E + 0x14)) = v5 ∧
      memLoad32 N (acSlot B (E + 0x18)) = v6 ∧ memLoad32 N (acSlot B 0x2C) = c := by
  intro N
  have ht : ∀ t, t ≤ 0x18 → 0x3A50 + (E + t) + 4 ≤ 0x5A70 := fun t h => by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, memLoad32_store32_same _ _ _⟩ <;> unfold N acetlPush
  · rw [acetl_ldS F (s := 0x2C) (by omega) (by omega) (ht 0 (by omega)),
      acetl_ldS F (s := E + 0x18) (by omega) (by omega) (ht 0 (by omega)),
      acetl_ldS F (s := E + 0x14) (by omega) (by omega) (ht 0 (by omega)),
      acetl_ldS F (s := E + 0x10) (by omega) (by omega) (ht 0 (by omega)),
      acetl_ldS F (s := E + 0xC) (by omega) (by omega) (ht 0 (by omega)),
      acetl_ldS F (s := E + 8) (by omega) (by omega) (ht 0 (by omega)),
      acetl_ldS F (s := E + 4) (by omega) (by omega) (ht 0 (by omega)), memLoad32_store32_same]
  · rw [acetl_ldS F (s := 0x2C) (by omega) (by omega) (ht 4 (by omega)),
      acetl_ldS F (s := E + 0x18) (by omega) (by omega) (ht 4 (by omega)),
      acetl_ldS F (s := E + 0x14) (by omega) (by omega) (ht 4 (by omega)),
      acetl_ldS F (s := E + 0x10) (by omega) (by omega) (ht 4 (by omega)),
      acetl_ldS F (s := E + 0xC) (by omega) (by omega) (ht 4 (by omega)),
      acetl_ldS F (s := E + 8) (by omega) (by omega) (ht 4 (by omega)), memLoad32_store32_same]
  · rw [acetl_ldS F (s := 0x2C) (by omega) (by omega) (ht 8 (by omega)),
      acetl_ldS F (s := E + 0x18) (by omega) (by omega) (ht 8 (by omega)),
      acetl_ldS F (s := E + 0x14) (by omega) (by omega) (ht 8 (by omega)),
      acetl_ldS F (s := E + 0x10) (by omega) (by omega) (ht 8 (by omega)),
      acetl_ldS F (s := E + 0xC) (by omega) (by omega) (ht 8 (by omega)), memLoad32_store32_same]
  · rw [acetl_ldS F (s := 0x2C) (by omega) (by omega) (ht 0xC (by omega)),
      acetl_ldS F (s := E + 0x18) (by omega) (by omega) (ht 0xC (by omega)),
      acetl_ldS F (s := E + 0x14) (by omega) (by omega) (ht 0xC (by omega)),
      acetl_ldS F (s := E + 0x10) (by omega) (by omega) (ht 0xC (by omega)), memLoad32_store32_same]
  · rw [acetl_ldS F (s := 0x2C) (by omega) (by omega) (ht 0x10 (by omega)),
      acetl_ldS F (s := E + 0x18) (by omega) (by omega) (ht 0x10 (by omega)),
      acetl_ldS F (s := E + 0x14) (by omega) (by omega) (ht 0x10 (by omega)), memLoad32_store32_same]
  · rw [acetl_ldS F (s := 0x2C) (by omega) (by omega) (ht 0x14 (by omega)),
      acetl_ldS F (s := E + 0x18) (by omega) (by omega) (ht 0x14 (by omega)), memLoad32_store32_same]
  · rw [acetl_ldS F (s := 0x2C) (by omega) (by omega) (ht 0x18 (by omega)), memLoad32_store32_same]

/-- The array's bytes before the new entry, and its words after it. -/
theorem acetl_push_arr (F : Fr B 0x5A70) (hE : 0x350 ≤ E ∧ E + 0x20 ≤ 0x550) :
    (∀ i, i < E - 0x350 → acetlPush M B E v0 v1 v2 v3 v4 v5 v6 c (acSlot B 0x350 + BitVec.ofNat 32 i) =
      M (acSlot B 0x350 + BitVec.ofNat 32 i)) ∧
    (∀ t, E + 0x20 ≤ t → t + 4 ≤ 0x550 →
      memLoad32 (acetlPush M B E v0 v1 v2 v3 v4 v5 v6 c) (acSlot B t) = memLoad32 M (acSlot B t)) := by
  refine ⟨fun i hi => ?_, fun t h1 h2 => acetl_push_ld F hE (by omega) (.inr (by omega)) (.inr (by omega))⟩
  rw [acetl_slot4 B (t := 0x350 + i) rfl]
  unfold acetlPush
  have hi' : 0x3A50 + (0x350 + i) + 1 ≤ 0x5A70 := by omega
  rw [acetl_getB F (s := 0x2C) (by omega) (by omega) hi', acetl_getB F (s := E + 0x18) (by omega) (by omega) hi',
    acetl_getB F (s := E + 0x14) (by omega) (by omega) hi', acetl_getB F (s := E + 0x10) (by omega) (by omega) hi',
    acetl_getB F (s := E + 0xC) (by omega) (by omega) hi', acetl_getB F (s := E + 8) (by omega) (by omega) hi',
    acetl_getB F (s := E + 4) (by omega) (by omega) hi', acetl_getB F (s := E + 0) (by omega) (by omega) hi']
end

theorem acetl_cur_move {D : Word} {json : Bytes} {M M' : Word → BitVec 8} {c : Word} {rest : List Json}
    (h : AceCur D json M c rest) (h0 : memLoad32 M' c = memLoad32 M c)
    (h4 : memLoad32 M' (c + 4) = memLoad32 M (c + 4)) (h8 : memLoad32 M' (c + 8) = memLoad32 M (c + 8)) :
    AceCur D json M' c rest := by
  obtain ⟨p, l, pos, e0, e4, e8, r⟩ := h
  exact ⟨p, l, pos, h0.trans e0, h4.trans e4, h8.trans e8, r⟩

/-- The log array with one more entry. -/
theorem acetl_logs_push {Bf fp fp' a : Word} {M M' : Word → BitVec 8} {ls : List LogKey} {k : LogKey}
    (h : AceLogsAt Bf fp M a ls) (hl : ls.length < 16) (hf : fp.toNat ≤ fp'.toNat)
    (hs : ∀ c, c < 0x20 * ls.length → M' (a + BitVec.ofNat 32 c) = M (a + BitVec.ofNat 32 c))
    (hz : ∀ i, ls.length + 1 ≤ i → i < 16 →
      memLoad32 M' (a + BitVec.ofNat 32 (0x20 * i)) = memLoad32 M (a + BitVec.ofNat 32 (0x20 * i)))
    (hb : ∀ y, Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp.toNat → M' y = M y)
    (he : AceEntryIn Bf fp' M' (a + BitVec.ofNat 32 (0x20 * ls.length)) k.origin k.publicKey 32 k.window) :
    AceLogsAt Bf fp' M' a (ls ++ [k]) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simp only [List.length_append, List.length_singleton]; omega, fun i hi => ?_, fun i hl' hc => ?_⟩
  · rcases Nat.lt_or_ge i ls.length with hi' | hi'
    · rw [List.getElem_append_left hi']
      exact acetl_entry_fp ((h2 i hi').move (fun c hc => by rw [add_ofNat_assoc]; exact hs _ (by omega)) hb) hf
    · have e : i = ls.length := by
        simp only [List.length_append, List.length_singleton] at hi; omega
      subst e
      simpa using he
  · simp only [List.length_append, List.length_singleton] at hl'
    rw [hz i (by omega) hc]; exact h3 i (by omega) hc

/-- The document's bytes, in memory that keeps the machine at the start of
a pass outside its writes, the log array, and the count. -/
theorem acetl_doc3 {X : AceCtx} (O : X.Ok) {n0 : Machine} {fp0 : Word} (A : AceAt X n0 0xEBA fp0)
    {M : Word → BitVec 8}
    (hm : ∀ x, AcetlU X.B X.Bf fp0 true x → Sep x 1 (acSlot X.B 0x350) 0x200 → Sep x 1 (acSlot X.B 0x2C) 4 →
      M x = n0.mem x) {p : Word} {n : Nat}
    (h1 : X.D.toNat ≤ p.toNat) (h2 : p.toNat + n ≤ X.D.toNat + X.json.length) :
    memBytes M p n = slice X.json (p.toNat - X.D.toNat) n := by
  have hfp := A.fr.lo
  have hfh := A.fr.hi
  have hd : memBytes M X.D X.json.length = X.json := by
    refine (ace_memBytes_ext (M := X.K.mem) fun i hi => ?_).trans O.pre.doc
    obtain ⟨hu, hk⟩ := acetl_U_doc O hfp hi
    obtain ⟨-, h2, h3⟩ := acetl_U_kept O (d := true) hfp hfh hk
    rw [hm _ hu h2 h3, A.keep.mem _ hk]
  have hhi := O.pre.docHi; have hb := O.lay.hi
  have e : p = X.D + BitVec.ofNat 32 (p.toNat - X.D.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := p.isLt; omega
  have h := tuf_memBytes_drop_take (M := M) (p := X.D) (n := X.json.length) (h := p.toNat - X.D.toNat) (l := n)
    (by omega)
  rw [hd, ← e] at h
  exact h.symm

section
variable {X : AceCtx} {n0 : Machine} {fp0 : Word} {jr : Json} {fs : List FulcioKey} {j : Json}
  {rest : List Json} {ls : List LogKey} {M : Word → BitVec 8} {f : Fin 32 → Word}

set_option maxHeartbeats 4000000 in
/-- From 0x1184, the entry's words in registers: the stores, the count, and
the jump back to 0xEBA. -/
theorem acetl_push2 (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs (j :: rest) ls)
    (R : AceHR X f) (h26 : f 26 = reg n0 26) {Ms : Word → BitVec 8}
    (hm : ∀ x, AcetlV X.B x → M x = Ms x) (hs : ∀ x, AcetlU X.B X.Bf fp0 true x → Ms x = n0.mem x)
    (hcur : AceCur X.D X.json Ms (acSlot X.B 0x1860) rest)
    (h44 : fp0.toNat + 44 ≤ X.Bf.toNat + 0xB840)
    (hfp : memLoad32 Ms (acSlot X.B 0x1FDC) = fp0 + 44)
    (hfl : memLoad32 Ms (acSlot X.B 0x1FE0) = BitVec.ofNat 32 (X.Bf.toNat + 0xB840 - (fp0.toNat + 44)))
    {k : LogKey} (hj : logEntry j = some (some k)) {op : Word}
    (ho1 : X.D.toNat ≤ op.toNat) (ho2 : op.toNat + k.origin.length ≤ X.D.toNat + X.json.length)
    (ho3 : slice X.json (op.toNat - X.D.toNat) k.origin.length = k.origin)
    (hpk : memBytes Ms (fp0 + 12) 32 = k.publicKey)
    (hnb : k.window.notBefore < 2 ^ 64) (hna : k.window.notAfter < 2 ^ 64)
    (hc : ls.length < 16) {E : Nat} (hE : E = 0x350 + 0x20 * ls.length)
    (h14 : f a4 = acSlot X.B E) (h15 : f a5 = BitVec.ofNat 32 ls.length)
    (h10 : f a0 = BitVec.ofNat 32 k.window.notBefore) (h11 : f a1 = BitVec.ofNat 32 (k.window.notBefore / 2 ^ 32))
    (h12 : f a2 = BitVec.ofNat 32 k.window.notAfter) (h13 : f a3 = BitVec.ofNat 32 (k.window.notAfter / 2 ^ 32))
    (h20 : f 20 = op) (h22 : f 22 = BitVec.ofNat 32 k.origin.length) (h24 : f 24 = fp0 + 12) :
    WP bootMainClosure0Code AC (acetlQ X 0xEBA (acetlNx X jr fs rest)) M 0x1184 f := by
  have F := O.lay.fr
  have hh := F.hi
  have hfp0 := A.fr.lo
  have hfh := A.fr.hi
  have hbw := O.lay.hi
  unfold acBufLen at hbw
  have hE' : 0x350 ≤ E ∧ E + 0x20 ≤ 0x550 := ⟨by omega, by omega⟩
  have ad : ∀ i : Nat, f a4 + BitVec.ofNat 32 i = acSlot X.B (E + i) := fun i => by
    rw [h14, acetl_slot4 X.B rfl]
  have al : ∀ i, i % 4 = 0 → i ≤ 0x1C → (acSlot X.B (E + i)).toNat % 4 = 0 := fun i h1 h2 =>
    ace_al4 F (by omega) (by omega)
  have cs : ∀ i, i ≤ 0x1C → Sep (acSlot X.B (E + i)) 4 AC bootMainClosure0Code.length := fun i h =>
    ace_cs F (by omega)
  have st : ∀ i, i % 4 = 0 → i ≤ 0x1C →
      (f a4 + BitVec.ofNat 32 i).toNat % 4 = 0 ∧ Sep (f a4 + BitVec.ofNat 32 i) 4 AC bootMainClosure0Code.length :=
    fun i h1 h2 => by rw [ad]; exact ⟨al i h1 h2, cs i h2⟩
  refine WP.sw ac_at_1184 (st 0 (by decide) (by decide)).1 (st 0 (by decide) (by decide)).2 ?_; wn
  refine WP.sw ac_at_1188 (st 4 (by decide) (by decide)).1 (st 4 (by decide) (by decide)).2 ?_; wn
  refine WP.sw ac_at_118c (st 8 (by decide) (by decide)).1 (st 8 (by decide) (by decide)).2 ?_; wn
  refine WP.sw ac_at_118e (st 0xC (by decide) (by decide)).1 (st 0xC (by decide) (by decide)).2 ?_; wn
  refine WP.sw ac_at_1190 (st 0x10 (by decide) (by decide)).1 (st 0x10 (by decide) (by decide)).2 ?_; wn
  refine WP.sw ac_at_1192 (st 0x14 (by decide) (by decide)).1 (st 0x14 (by decide) (by decide)).2 ?_; wn
  refine WP.sw ac_at_1194 (st 0x18 (by decide) (by decide)).1 (st 0x18 (by decide) (by decide)).2 ?_; wn
  refine WP.aluImm ac_at_1198 ?_; wn
  have e2C : X.B + 0x3A50 + 0x2C = acSlot X.B 0x2C := by simp only [acSlot]; bv_omega
  refine WP.sw ac_at_119a (by rsimp; rw [R.rsp, e2C]; exact ace_al4 F (by decide) (by decide))
    (by rsimp; rw [R.rsp, e2C]; exact ace_cs F (by decide)) ?_; wn
  refine WP.jal ac_at_119c (by decide) ?_; wn
  refine WP.here ?_
  have ec : aluEval .add (BitVec.ofNat 32 ls.length) 1 = BitVec.ofNat 32 (ls ++ [k]).length := by
    rw [ev_add]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, List.length_append, List.length_singleton]
    have : (1 : Word).toNat = 1 := rfl
    rw [this]; omega
  rw [show (0 : Word) = BitVec.ofNat 32 0 from rfl, show (4 : Word) = BitVec.ofNat 32 4 from rfl,
    show (8 : Word) = BitVec.ofNat 32 8 from rfl, show (12 : Word) = BitVec.ofNat 32 12 from rfl,
    show (16 : Word) = BitVec.ofNat 32 16 from rfl, show (20 : Word) = BitVec.ofNat 32 20 from rfl,
    show (24 : Word) = BitVec.ofNat 32 24 from rfl, ad, ad, ad, ad, ad, ad, ad, R.rsp, e2C, h15, ec,
    h20, h22, h10, h11, h12, h13, h24]
  have hmn : ∀ x, AcetlU X.B X.Bf fp0 true x → M x = n0.mem x := fun x hx => (hm x (acetl_UV hx)).trans (hs x hx)
  have hk : ∀ x, AcetlU X.B X.Bf fp0 true x → Sep x 1 (acSlot X.B 0x350) 0x200 → Sep x 1 (acSlot X.B 0x2C) 4 →
      acetlPush M X.B E op (BitVec.ofNat 32 k.origin.length) (BitVec.ofNat 32 k.window.notBefore)
        (BitVec.ofNat 32 (k.window.notBefore / 2 ^ 32)) (BitVec.ofNat 32 k.window.notAfter)
        (BitVec.ofNat 32 (k.window.notAfter / 2 ^ 32)) (fp0 + 12) (BitVec.ofNat 32 (ls ++ [k]).length) x =
      n0.mem x := fun x hu ha hc => by rw [acetl_push_get hE' ha hc]; exact hmn x hu
  have hld : ∀ t, 0x3A50 + t + 4 ≤ 0x5A70 → (t + 4 ≤ E ∨ E + 0x1C ≤ t) → (t + 4 ≤ 0x2C ∨ 0x30 ≤ t) →
      acetlWc.all (fun r => decide (0x3A50 + t + 4 ≤ r.1) || decide (r.2 ≤ 0x3A50 + t)) = true →
      memLoad32 (acetlPush M X.B E op (BitVec.ofNat 32 k.origin.length) (BitVec.ofNat 32 k.window.notBefore)
        (BitVec.ofNat 32 (k.window.notBefore / 2 ^ 32)) (BitVec.ofNat 32 k.window.notAfter)
        (BitVec.ofNat 32 (k.window.notAfter / 2 ^ 32)) (fp0 + 12) (BitVec.ofNat 32 (ls ++ [k]).length))
        (acSlot X.B t) = memLoad32 Ms (acSlot X.B t) := fun t h1 h2 h3 h4 => by
    rw [acetl_push_ld F hE' h1 h2 h3]; exact acetl_ldV O hm h1 h4
  obtain ⟨e0, e4, e8, eC, e10, e14, e18, e2c⟩ := acetl_push_e (M := M) (B := X.B) (E := E) (v0 := op)
    (v1 := BitVec.ofNat 32 k.origin.length) (v2 := BitVec.ofNat 32 k.window.notBefore)
    (v3 := BitVec.ofNat 32 (k.window.notBefore / 2 ^ 32)) (v4 := BitVec.ofNat 32 k.window.notAfter)
    (v5 := BitVec.ofNat 32 (k.window.notAfter / 2 ^ 32)) (v6 := fp0 + 12)
    (c := BitVec.ofNat 32 (ls ++ [k]).length) F hE'
  obtain ⟨ha1, ha2⟩ := acetl_push_arr (M := M) (B := X.B) (E := E) (v0 := op)
    (v1 := BitVec.ofNat 32 k.origin.length) (v2 := BitVec.ofNat 32 k.window.notBefore)
    (v3 := BitVec.ofNat 32 (k.window.notBefore / 2 ^ 32)) (v4 := BitVec.ofNat 32 k.window.notAfter)
    (v5 := BitVec.ofNat 32 (k.window.notAfter / 2 ^ 32)) (v6 := fp0 + 12)
    (c := BitVec.ofNat 32 (ls ++ [k]).length) F hE'
  have h44' : (fp0 + 44).toNat = fp0.toNat + 44 := by
    rw [BitVec.toNat_add]; have : (44 : Word).toNat = 44 := rfl; omega
  have h12' : (fp0 + 12).toNat = fp0.toNat + 12 := by
    rw [BitVec.toNat_add]; have : (12 : Word).toNat = 12 := rfl; omega
  have hout : ∀ y : Word, X.Bf.toNat ≤ y.toNat → y.toNat < X.Bf.toNat + 0xB840 →
      acetlPush M X.B E op (BitVec.ofNat 32 k.origin.length) (BitVec.ofNat 32 k.window.notBefore)
        (BitVec.ofNat 32 (k.window.notBefore / 2 ^ 32)) (BitVec.ofNat 32 k.window.notAfter)
        (BitVec.ofNat 32 (k.window.notAfter / 2 ^ 32)) (fp0 + 12) (BitVec.ofNat 32 (ls ++ [k]).length) y = Ms y :=
    fun y h1 h2 => by
      have hs := ace_ofSep (ace_bufOut O.lay (y := y) h1 (by unfold acBufLen; omega))
      rw [acetl_push_out F hE' hs]; exact hm y (acetl_V_out hs)
  have hdl : k.origin.length < 2 ^ 32 := by have := O.pre.docHi; omega
  unfold acetlPush at e0 e4 e8 eC e10 e14 e18 ha1 ha2 hout
  refine acetl_close O A I (by hr) (by rsimp; exact h26) (fp1 := fp0 + 44) (by omega) (by omega)
    ((hld 0x1FDC (by decide) (.inr (by omega)) (.inr (by decide)) (by decide)).trans hfp)
    ((hld 0x1FE0 (by decide) (.inr (by omega)) (.inr (by decide)) (by decide)).trans (by rw [hfl, h44']))
    hk ?_ (I.tlogs.step hj) ?_ (by rw [show (some k).toList = [k] from rfl]; exact e2c)
  · refine acetl_cur_move hcur (hld 0x1860 (by decide) (.inr (by omega)) (.inr (by decide)) (by decide)) ?_ ?_
    · rw [show acSlot X.B 0x1860 + 4 = acSlot X.B 0x1864 by unfold acSlot; rw [BitVec.add_assoc]; rfl]
      exact hld 0x1864 (by decide) (.inr (by omega)) (.inr (by decide)) (by decide)
    · rw [show acSlot X.B 0x1860 + 8 = acSlot X.B 0x1868 by unfold acSlot; rw [BitVec.add_assoc]; rfl]
      exact hld 0x1868 (by decide) (.inr (by omega)) (.inr (by decide)) (by decide)
  · have eE : ∀ i, acSlot X.B 0x350 + BitVec.ofNat 32 (0x20 * ls.length) + BitVec.ofNat 32 i = acSlot X.B (E + i) :=
      fun i => by rw [acetl_slot4 X.B (t := E) (by omega), acetl_slot4 X.B rfl]
    have q0 : acSlot X.B 0x350 + BitVec.ofNat 32 (0x20 * ls.length) = acSlot X.B (E + 0) :=
      acetl_slot4 X.B (by omega)
    have q4 : acSlot X.B 0x350 + BitVec.ofNat 32 (0x20 * ls.length) + 4 = acSlot X.B (E + 4) := eE 4
    have q8 : acSlot X.B 0x350 + BitVec.ofNat 32 (0x20 * ls.length) + 8 = acSlot X.B (E + 8) := eE 8
    have qC : acSlot X.B 0x350 + BitVec.ofNat 32 (0x20 * ls.length) + 8 + 4 = acSlot X.B (E + 0xC) := by
      rw [q8]; exact acetl_slot4 X.B (i := 4) (by omega)
    have q10 : acSlot X.B 0x350 + BitVec.ofNat 32 (0x20 * ls.length) + 0x10 = acSlot X.B (E + 0x10) := eE 0x10
    have q14 : acSlot X.B 0x350 + BitVec.ofNat 32 (0x20 * ls.length) + 0x10 + 4 = acSlot X.B (E + 0x14) := by
      rw [q10]; exact acetl_slot4 X.B (i := 4) (by omega)
    have q18 : acSlot X.B 0x350 + BitVec.ofNat 32 (0x20 * ls.length) + 0x18 = acSlot X.B (E + 0x18) := eE 0x18
    refine acetl_logs_push I.logs hc (by omega) (fun c hc' => ?_) (fun i h1 h2 => ?_) (fun y h1 h2 => ?_) ⟨⟨?_, ?_, ?_⟩,
      ⟨hnb, ?_, ?_⟩, ⟨hna, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · rw [ha1 c (by omega)]
      exact hmn _ (acetl_U_at O hfp0 (s := 0x350) (l := 0x200) (by decide) (by decide) (by decide) (by omega))
    · rw [acetl_slot4 X.B (t := 0x350 + 0x20 * i) rfl, ha2 _ (by omega) (by omega)]
      refine ace_load_eq fun jj hjj => ?_
      rw [acetl_slot4 X.B (t := 0x350 + (0x20 * i + jj)) (by omega)]
      have hu := acetl_U_at O hfp0 (d := true) (s := 0x350) (l := 0x200) (j := 0x20 * i + jj) (by decide) (by decide)
        (by decide) (by omega)
      rw [acetl_slot4 X.B rfl] at hu
      exact hmn _ hu
    · have hy := ace_ofSep (ace_bufOut O.lay (y := y) (by omega) (by unfold acBufLen; omega))
      rw [hout y (by omega) (by omega)]
      exact hs y (acetl_U_out hy (.inl h2))
    · rw [q0, e0]; have := O.pre.docLo; omega
    · rw [q4, q0, e4, e0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdl]
      have := O.pre.docHi; omega
    · rw [q4, q0, e4, e0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdl]
      exact (acetl_doc3 O A hk ho1 ho2).trans ho3
    · rw [q8, e8]
    · rw [qC, eC]
    · rw [q10, e10]
    · rw [q14, e14]
    · rw [q18, e18, h12']; have := O.pre.docLo; omega
    · rw [q18, e18, h12', h44']; omega
    · rw [q18, e18, ← hpk]
      refine ace_memBytes_ext fun i hi => hout _ ?_ ?_ <;>
      · rw [BitVec.toNat_add, BitVec.toNat_ofNat, h12']; omega

end

theorem acetl_al {X : AceCtx} (O : X.Ok) {a : Word} {s : Nat} (h : a = acSlot X.B s) (hs : s % 4 = 0)
    (hs' : 0x3A50 + s ≤ 0x5A70) : a.toNat % 4 = 0 := by
  subst h; exact ace_al4 O.lay.fr (by omega) hs'

theorem acetl_ldEq {M : Word → BitVec 8} {a b v : Word} (h : a = b) (hv : memLoad32 M b = v) :
    memLoad32 M a = v := h ▸ hv

theorem acetl_sll5 : ∀ c : Fin 16, aluEval .sll (BitVec.ofNat 32 c.val) 5 = BitVec.ofNat 32 (0x20 * c.val) := by
  decide

section
variable {X : AceCtx} {n0 : Machine} {fp0 : Word} {jr : Json} {fs : List FulcioKey} {j : Json}
  {rest : List Json} {ls : List LogKey} {M : Word → BitVec 8} {f : Fin 32 → Word}

set_option maxHeartbeats 4000000 in
/-- From 0x1160, after `valid_for`: the count check and the push. -/
theorem acetl_push (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs (j :: rest) ls)
    (R : AceHR X f) (h26 : f 26 = reg n0 26) {Ms : Word → BitVec 8}
    (hm : ∀ x, AcetlV X.B x → M x = Ms x) (hs : ∀ x, AcetlU X.B X.Bf fp0 true x → Ms x = n0.mem x)
    (hcur : AceCur X.D X.json Ms (acSlot X.B 0x1860) rest)
    (h44 : fp0.toNat + 44 ≤ X.Bf.toNat + 0xB840)
    (hfp : memLoad32 Ms (acSlot X.B 0x1FDC) = fp0 + 44)
    (hfl : memLoad32 Ms (acSlot X.B 0x1FE0) = BitVec.ofNat 32 (X.Bf.toNat + 0xB840 - (fp0.toNat + 44)))
    {k : LogKey} (hj : logEntry j = some (some k)) {op : Word}
    (ho1 : X.D.toNat ≤ op.toNat) (ho2 : op.toNat + k.origin.length ≤ X.D.toNat + X.json.length)
    (ho3 : slice X.json (op.toNat - X.D.toNat) k.origin.length = k.origin)
    (hpk : memBytes Ms (fp0 + 12) 32 = k.publicKey)
    (hnb : k.window.notBefore < 2 ^ 64) (hna : k.window.notAfter < 2 ^ 64)
    (hw0 : memLoad32 M (acSlot X.B 0x1328) = BitVec.ofNat 32 k.window.notBefore)
    (hw1 : memLoad32 M (acSlot X.B 0x132C) = BitVec.ofNat 32 (k.window.notBefore / 2 ^ 32))
    (hw2 : memLoad32 M (acSlot X.B 0x1330) = BitVec.ofNat 32 k.window.notAfter)
    (hw3 : memLoad32 M (acSlot X.B 0x1334) = BitVec.ofNat 32 (k.window.notAfter / 2 ^ 32))
    (h20 : f 20 = op) (h22 : f 22 = BitVec.ofNat 32 k.origin.length) (h24 : f 24 = fp0 + 12) :
    WP bootMainClosure0Code AC (acetlQ X 0xEBA (acetlNx X jr fs rest)) M 0x1160 f := by
  have F := O.lay.fr
  have hfp0 := A.fr.lo
  have hmn : ∀ x, AcetlU X.B X.Bf fp0 true x → M x = n0.mem x := fun x hx => (hm x (acetl_UV hx)).trans (hs x hx)
  have hcnt : memLoad32 M (acSlot X.B 0x2C) = BitVec.ofNat 32 ls.length :=
    (acetl_ld O hmn hfp0 (s := 0x2C) (by decide) (by decide) (by decide)).trans I.count
  have e2C : X.B + 0x3A50 + 0x2C = acSlot X.B 0x2C := by simp only [acSlot]; bv_omega
  refine WP.lw ac_at_1160 (by rw [R.rsp, e2C]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.aluImm ac_at_1162 ?_; wn
  refine WP.branch ac_at_1164 (fun _ => ?_) (fun eb => ?_) <;> wn
  · exact acetl_f1424 O A hmn (by hr)
  have hc : ls.length < 16 := by
    (try rsimp at eb); rw [R.rsp, e2C, hcnt, show aluEval AluOp.add 0 15 = (15 : Word) by decide] at eb
    have hl := I.logs.1
    simp only [branchTaken, BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat] at eb
    have : (15 : Word).toNat = 15 := rfl
    omega
  refine WP.lui ac_at_1168 ?_; wn
  refine WP.aluImm ac_at_116a ?_; wn
  refine WP.alu ac_at_116e ?_; wn
  refine WP.lw ac_at_1172 (acetl_al O (s := 0x1328) (by (try rsimp); simp only [ev_add, R.rsp, acSlot]; bv_omega)
    (by decide) (by decide)) ?_; wn
  refine WP.lw ac_at_1174 (acetl_al O (s := 0x132C) (by (try rsimp); simp only [ev_add, R.rsp, acSlot]; bv_omega)
    (by decide) (by decide)) ?_; wn
  refine WP.lw ac_at_1176 (acetl_al O (s := 0x1330) (by (try rsimp); simp only [ev_add, R.rsp, acSlot]; bv_omega)
    (by decide) (by decide)) ?_; wn
  refine WP.lw ac_at_1178 (acetl_al O (s := 0x1334) (by (try rsimp); simp only [ev_add, R.rsp, acSlot]; bv_omega)
    (by decide) (by decide)) ?_; wn
  refine WP.lw ac_at_117a (by (try rsimp); rw [R.rsp, e2C]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.aluImm ac_at_117c ?_; wn
  refine WP.aluImm ac_at_1180 ?_; wn
  refine WP.alu ac_at_1182 ?_; wn
  refine acetl_push2 O A I (by hr) (by (try rsimp); exact h26) hm hs hcur h44 hfp hfl hj ho1 ho2 ho3 hpk hnb hna hc rfl
    ?_ (by (try rsimp); rw [R.rsp, e2C, hcnt])
    (by (try rsimp); exact acetl_ldEq (by simp only [ev_add, R.rsp, acSlot]; bv_omega) hw0)
    (by (try rsimp); exact acetl_ldEq (by simp only [ev_add, R.rsp, acSlot]; bv_omega) hw1)
    (by (try rsimp); exact acetl_ldEq (by simp only [ev_add, R.rsp, acSlot]; bv_omega) hw2)
    (by (try rsimp); exact acetl_ldEq (by simp only [ev_add, R.rsp, acSlot]; bv_omega) hw3)
    (by (try rsimp); exact h20) (by (try rsimp); exact h22) (by (try rsimp); exact h24)
  rsimp; simp only [ev_add, R.rsp]
  rw [e2C, hcnt, acetl_sll5 ⟨_, hc⟩]
  simp only [acSlot]; bv_omega

end

end C3.RV32.Ac
