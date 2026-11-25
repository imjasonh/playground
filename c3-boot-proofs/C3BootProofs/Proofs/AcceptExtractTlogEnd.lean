import C3BootProofs.Proofs.AcceptExtractTlogCalls

/-!
# The start of a transparency log pass, and the end of the loop

Each pass starts at 0xEBA with `next_element` on the cursor at
`sp + 0x1860` (`acetl_pre`). When no item is left, the stage zeroes the
TSA array at `sp + 0x890`, finds `timestampAuthorities` with `field`, opens
it with `elements`, and copies the cursor to `sp + 0x1DC8`, then reaches
0x123A (`acetl_end`).

From the end of the loop on, the stage writes only ranges in `acetlW`, so
memory agrees with the machine at the start of the last pass outside them
(`AcetlU` with `d = false`). That keeps `keys`'s slice at `sp + 0x1FDC`, the
Fulcio and log arrays, and the count.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

set_option maxRecDepth 100000

local notation "MCS" => (BitVec.ofNat 32 memcpyStubAddress : Word)

/-- What `AceTlogStage` gives at 0x123A. -/
def acetlEnd (X : AceCtx) (jr : Json) (fs : List FulcioKey) (n : Machine) : Prop :=
  ∃ fp ls ts, AceAt X n 0x123A fp ∧ AceTsaInv X n fp jr fs ls ts []

/-- `pm_ccopy` for offsets up to `2 ^ 32`: the copy of the cursor at `F + a`
to `F + d`, seven bytes by `memcpy`, then a word and a byte. -/
theorem acetl_ccopy {M2 M3 M5 : Word → BitVec 8} {F S q : Word} {d a l k : Nat}
    (hd : d + 12 ≤ 2 ^ 32)
    (hSD : Sep (F + BitVec.ofNat 32 d) 12 S 16)
    (t4 : memLoad32 M2 (F + BitVec.ofNat 32 (a + 4)) = BitVec.ofNat 32 l)
    (t8 : memLoad32 M2 (F + BitVec.ofNat 32 (a + 8)) = BitVec.ofNat 32 k)
    (hO3 : Out (copyBytes M2 (F + BitVec.ofNat 32 (d + 5)) (F + BitVec.ofNat 32 (a + 5)) 7) M3 S 16)
    (hM5 : memStore8 (memStore32 M3 (F + BitVec.ofNat 32 d) q) (F + BitVec.ofNat 32 (d + 4))
      (M2 (F + BitVec.ofNat 32 (a + 4))) = M5) :
    PmCc M5 (F + BitVec.ofNat 32 d) q l k ∧
      ∀ x, Sep x 1 (F + BitVec.ofNat 32 d) 12 → Sep x 1 S 16 → M5 x = M2 x := by
  have oC : Out M2 (copyBytes M2 (F + BitVec.ofNat 32 (d + 5)) (F + BitVec.ofNat 32 (a + 5)) 7)
      (F + BitVec.ofNat 32 (d + 5)) 7 := fun x hx => copyBytes_sep hx.symm (Nat.le_refl _)
  have hcp : ∀ c, 5 ≤ c → c < 12 → M5 (F + BitVec.ofNat 32 (d + c)) = M2 (F + BitVec.ofNat 32 (a + c)) := by
    intro c hc1 hc2
    rw [← hM5, memStore8_ne ?_]
    · rw [out_store32 _ _ _ _ ?_, hO3 _ ?_]
      · have := copyBytes_at (M := M2) (dst := F + BitVec.ofNat 32 (d + 5)) (src := F + BitVec.ofNat 32 (a + 5))
          (N := 7) (i := c - 5) (by omega) (by decide)
        rw [add_ofNat_assoc, add_ofNat_assoc, show d + 5 + (c - 5) = d + c by omega,
          show a + 5 + (c - 5) = a + c by omega] at this
        exact this
      · have := hSD.sub (c := c) (l := 1) (by omega)
        rwa [add_ofNat_assoc] at this
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

section
variable {X : AceCtx} (O : X.Ok)
include O

/-- A byte of the frame outside `acetlW`. -/
theorem acetl_Uf {fp : Word} {s l j : Nat} (hs : 0x3A50 + s + l ≤ 0x5A70)
    (hr : acetlW.all (fun r => decide (0x3A50 + s + l ≤ r.1) || decide (r.2 ≤ 0x3A50 + s)) = true) (hj : j < l) :
    AcetlU X.B X.Bf fp false (acSlot X.B s + BitVec.ofNat 32 j) := by
  have F := O.lay.fr
  have hx := ace_slotAdd F (k := s) (j := j) (by omega)
  refine ⟨fun r hm => ?_, fun h => absurd h (by decide)⟩
  have := List.all_eq_true.mp hr r hm
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h | h
  · exact .inl (by omega)
  · exact .inr (by omega)

/-- A slot of the frame outside `acetlW`. -/
theorem acetl_Uf' {fp : Word} {k : Nat} (hk : 0x3A50 + k < 0x5A70)
    (hW : ∀ r ∈ acetlW, 0x3A50 + k < r.1 ∨ r.2 ≤ 0x3A50 + k) : AcetlU X.B X.Bf fp false (acSlot X.B k) := by
  have F := O.lay.fr
  have hx : (acSlot X.B k).toNat = X.B.toNat + (0x3A50 + k) := F.at _ (by omega)
  refine ⟨fun r hm => ?_, fun h => absurd h (by decide)⟩
  rcases hW r hm with h | h
  · exact .inl (by omega)
  · exact .inr (by omega)

/-- The zeroed TSA array, kept by a call that writes the `n1` bytes at `c1`
and the `n2` bytes at `c2`, both below it. -/
theorem acetl_zk {M M' : Word → BitVec 8} {c1 n1 c2 n2 : Nat}
    (h : ∀ x, Sep x 1 (X.B + BitVec.ofNat 32 c1) n1 → Sep x 1 (X.B + BitVec.ofNat 32 c2) n2 → M' x = M x)
    (h1 : c1 + n1 ≤ 0x42E0 ∨ 0x43E0 ≤ c1) (h2 : c2 + n2 ≤ 0x42E0 ∨ 0x43E0 ≤ c2) (hc1 : c1 + n1 ≤ 0x5A70)
    (hc2 : c2 + n2 ≤ 0x5A70) (hz : ∀ i, i < 8 → memLoad32 M (acSlot X.B (0x890 + 0x20 * i)) = 0) :
    ∀ i, i < 8 → memLoad32 M' (acSlot X.B (0x890 + 0x20 * i)) = 0 := by
  have F := O.lay.fr
  intro i hi
  refine (ace_ld2 F h ?_ ?_ (by omega) hc1 hc2).trans (hz i hi)
  · rcases h1 with h1 | h1
    · exact .inr (by omega)
    · exact .inl (by omega)
  · rcases h2 with h2 | h2
    · exact .inr (by omega)
    · exact .inl (by omega)

end

/-! ## The start of a pass -/

section
variable {X : AceCtx} {n0 : Machine} {fp0 : Word} {jr : Json} {fs : List FulcioKey} {ls : List LogKey}
  {o : Nat} {P : Machine → Prop} {Q : Post} {M : Word → BitVec 8} {f : Fin 32 → Word}

/-- From 0xEBA to the branch at 0xEEE on whether `next_element` found an
item: at 0x11A6 when none is left, at 0xEF2 with the item's value in `s6`
and its length at `sp + 0x1328` when one is. -/
theorem acetl_pre (O : X.Ok) {rest : List Json} (R : AceHR X f) (E : AcExtractEnv M) (hd : AcetlDoc X M)
    (hc : AceCur X.D X.json M (acSlot X.B 0x1860) rest)
    (kn : rest = [] → ∀ (M2 : Word → BitVec 8) (g : Fin 32 → Word), AceHR X g → g 26 = f 26 →
      (∀ x, AcetlV X.B x → Sep x 1 (acSlot X.B 0x1868) 4 → M2 x = M x) →
      WP bootMainClosure0Code AC Q M2 0x11A6 g)
    (kc : ∀ j rest', rest = j :: rest' → ∀ (M2 : Word → BitVec 8) (g : Fin 32 → Word) (q : Word) (l : Nat),
      AceHR X g → g 26 = f 26 → (∀ x, AcetlV X.B x → Sep x 1 (acSlot X.B 0x1868) 4 → M2 x = M x) →
      g 22 = q → AceVal X.D X.json q l j → memLoad32 M2 (acSlot X.B 0x1328) = BitVec.ofNat 32 l →
      AceCur X.D X.json M2 (acSlot X.B 0x1860) rest' →
      WP bootMainClosure0Code AC Q M2 0xEF2 g) :
    WP bootMainClosure0Code AC Q M 0xEBA f := by
  have F := O.lay.fr
  have hD0 := O.pre.docLo
  refine WP.lui ac_at_eba ?_; wn
  refine WP.aluImm ac_at_ebc ?_; wn
  refine WP.alu ac_at_ec0 ?_; wn
  refine WP.lui ac_at_ec2 ?_; wn
  refine WP.aluImm ac_at_ec4 ?_; wn
  refine WP.alu ac_at_ec8 ?_; wn
  refine WP.acetlNext O ac_at_eca ac_at_ece (by decide) (by decide) E hd hc (by rsimp; exact R.rsp)
    (by rsimp; simp only [ev_add, R.rsp, acSlot]; bv_omega)
    (by rsimp; simp only [ev_add, R.rsp, acSlot]; bv_omega) fun m2 hfr hel => ?_
  have e10 : aluEval .add (aluEval .add 4096 784) (f sp) + 16 = acSlot X.B 0x1320 := by
    simp only [ev_add, R.rsp, acSlot]; bv_omega
  have e14 : aluEval .add (aluEval .add 4096 784) (f sp) + 20 = acSlot X.B 0x1320 + 4 := by
    simp only [ev_add, R.rsp, acSlot]; bv_omega
  have e28 : acSlot X.B 0x1320 + 8 = acSlot X.B 0x1328 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  have h0 : m2.mem (acSlot X.B 0x1320) = 0 := by
    rcases rest with _ | ⟨j, rest'⟩
    · exact hel.1
    · exact hel.1
  refine WP.lui ac_at_ed2 ?_; wn
  refine WP.aluImm ac_at_ed4 ?_; wn
  refine WP.alu ac_at_ed8 ?_; wn
  refine WP.lbu ac_at_eda ?_; wn
  refine WP.branch ac_at_ede (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [e10, h0] at eb; exact absurd eb (by decide)
  refine WP.lui ac_at_ee2 ?_; wn
  refine WP.aluImm ac_at_ee4 ?_; wn
  refine WP.alu ac_at_ee8 ?_; wn
  have e24 : acSlot X.B 0x1320 + 4 = acSlot X.B 0x1324 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  refine WP.lw ac_at_eea (by rsimp; rw [e14]; exact acetl_al O (s := 0x1324) e24 (by decide) (by decide)) ?_
  wn
  rcases rest with _ | ⟨j, rest'⟩
  · obtain ⟨-, t4⟩ := hel
    refine WP.branch ac_at_eee (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact kn rfl _ _ (by hr) (by rsimp) hfr
    · exfalso; rsimp at eb; rw [e14, t4] at eb; exact absurd eb (by decide)
  · obtain ⟨-, q, l, hv, t4, t8, hcur⟩ := hel
    refine WP.branch ac_at_eee (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; rsimp at eb; rw [e14, t4] at eb
      have e0 : q = 0 := by simpa [branchTaken] using eb
      have := hv.1; rw [e0] at this; have hz : (0 : Word).toNat = 0 := rfl; omega
    · exact kc j rest' rfl _ _ q l (by hr) (by rsimp) hfr (by rsimp; rw [e14, t4]) hv (by rw [← e28]; exact t8) hcur

/-! ## The end of the loop -/

/-- From 0x1A6A, as `acetl_f1A6A`, with `s3` moved. -/
theorem acetl_f1A6A' (O : X.Ok) (A : AceAt X n0 0xEBA fp0)
    (hm : ∀ x, AcetlU X.B X.Bf fp0 true x → M x = n0.mem x) (h0 : f 0 = 0) (h2 : f (2 : Fin 32) = X.B + 0x3A50)
    (h3 : f (3 : Fin 32) = X.g) (h4 : f (4 : Fin 32) = X.t)
    (he : (f 8 &&& 0xFF).toNat < 0x27) : WP bootMainClosure0Code AC (acetlQ X o P) M 0x1A6A f := by
  refine WP.alu ac_at_1a6a ?_
  refine WP.jal ac_at_1a6c (by decide) ?_
  refine WP.here fun n hpc hn hr => ?_
  obtain ⟨hI, hres⟩ := acetl_inv O A hm hn (by rw [hr]; rsimp; exact h2) (by rw [hr]; rsimp; exact h3)
    (by rw [hr]; rsimp; exact h4)
  refine ⟨hI, .inl (.inr (.inr (.inl ⟨by rw [hpc]; rfl, hres, ?_⟩)))⟩
  rw [hr]; rsimp; rw [h0, ev_add, show (0 : Word) + f 8 = f 8 from BitVec.zero_add _]; exact he

set_option maxHeartbeats 4000000 in
/-- At 0x123A: `AceAt` and `AceTsaInv` with no TSA key read yet. -/
theorem acetl_fin (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs [] ls)
    (hk : ∀ x, AcetlU X.B X.Bf fp0 false x → M x = n0.mem x)
    (h2 : f (2 : Fin 32) = X.B + 0x3A50) (h3 : f (3 : Fin 32) = X.g) (h4 : f (4 : Fin 32) = X.t)
    (h21 : f 21 = reg X.K 21) (h25 : f 25 = reg X.K 25) (h27 : f 27 = reg X.K 27)
    (h19 : f 19 = acSlot X.B 0x1310) (h26 : f 26 = 0) {ts : List Json}
    (htsa : (jr.field (ascii!"timestampAuthorities") >>= Json.asArr) = some ts)
    (hcur : AceCur X.D X.json M (acSlot X.B 0x1DC8) ts)
    (hz : ∀ i, i < 8 → memLoad32 M (acSlot X.B (0x890 + 0x20 * i)) = 0) :
    acetlQ X 0x123A (acetlEnd X jr fs) (AC + BitVec.ofNat 32 0x123A) M f := by
  intro n hpc hn hr
  have F := O.lay.fr
  have hfp := A.fr.lo
  have hfh := A.fr.hi
  obtain ⟨hI, -⟩ := acetl_inv' O A (fun x hx _ _ => hk x hx.weak) hn (by rw [hr]; exact h2) (by rw [hr]; exact h3)
    (by rw [hr]; exact h4)
  have hld : ∀ s, 0x3A50 + s + 4 ≤ 0x5A70 →
      acetlW.all (fun r => decide (0x3A50 + s + 4 ≤ r.1) || decide (r.2 ≤ 0x3A50 + s)) = true →
      memLoad32 M (acSlot X.B s) = memLoad32 n0.mem (acSlot X.B s) :=
    fun s hs hr => ace_load_eq fun j hj => hk _ (acetl_Uf O hs hr hj)
  have hbuf : ∀ y : Word, X.Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp0.toNat → M y = n0.mem y := by
    intro y h1 h2
    have hs := ace_ofSep (ace_bufOut O.lay (y := y) (by omega) (by unfold acBufLen; omega))
    exact hk y (acetl_U_out hs (.inl h2))
  have hW : ∀ c, 0x3A50 + 0x350 ≤ 0x3A50 + c → 0x3A50 + c < 0x3A50 + 0x550 ∨
      (0x3A50 + 0x1ED0 ≤ 0x3A50 + c ∧ 0x3A50 + c < 0x3A50 + 0x1FD0) →
      ∀ r ∈ acetlW, 0x3A50 + c < r.1 ∨ r.2 ≤ 0x3A50 + c := by
    intro c h1 h2 r hr
    simp only [acetlW, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega
  refine ⟨hI, .inr ⟨hpc, fp0, ls, ts, ⟨fun i hi => ?_, ⟨hpc, rfl, fun _ => rfl⟩, hI,
    ⟨by rw [hn, hld 0x1FDC (by decide) (by decide)]; exact A.fr.ptr,
      by rw [hn, hld 0x1FE0 (by decide) (by decide)]; exact A.fr.len, hfp, hfh⟩,
    ⟨fun x hx => ?_, fun q hq => ?_⟩, ?_⟩,
    ⟨I.root, I.cas, I.tlogs, ⟨[], by rw [List.nil_append]; exact htsa, rfl⟩, by rw [hn]; exact hcur, ?_, ?_,
      ⟨Nat.zero_le _, fun i h => absurd h (Nat.not_lt_zero _), fun i _ hi => ?_⟩, by rw [hr]; exact h19,
      by rw [hr, h26]; rfl⟩⟩⟩
  · rw [hn, hk _ (acetl_U_code O hfp hi).1]; exact A.code i hi
  · rw [hn, hk _ (acetl_U_kept O hfp hfh hx).1]; exact A.keep.mem x hx
  · have : q = 21 ∨ q = 25 ∨ q = 27 := by revert hq; revert q; decide
    rcases this with rfl | rfl | rfl <;> rw [hr]
    · exact h21
    · exact h25
    · exact h27
  · unfold AceExpiry
    rw [← A.exp, hn]
    unfold aceU64
    rw [hld 0x20 (by decide) (by decide)]
    rw [show acSlot X.B 0x20 + 4 = acSlot X.B 0x24 by unfold acSlot; rw [BitVec.add_assoc]; rfl,
      hld 0x24 (by decide) (by decide)]
  · rw [hn]
    refine ace_array_move I.fulcio (fun c hc => ?_) hbuf
    rw [acetl_slot4 X.B (s := 0x1ED0) (i := c) rfl]
    exact hk _ (acetl_Uf' O (k := 0x1ED0 + c) (by omega) (hW _ (by omega) (.inr ⟨by omega, by omega⟩)))
  · rw [hn]
    refine ace_array_move I.logs (fun c hc => ?_) hbuf
    rw [acetl_slot4 X.B (s := 0x350) (i := c) rfl]
    exact hk _ (acetl_Uf' O (k := 0x350 + c) (by omega) (hW _ (by omega) (.inl (by omega))))
  · rw [hn, acetl_slot4 X.B (s := 0x890) (i := 0x20 * i) rfl]; exact hz i hi

set_option maxHeartbeats 4000000 in
/-- From 0x11BE, after the TSA array is zeroed: `field` for
`timestampAuthorities`, `elements` on it, and the cursor's copy at
`sp + 0x1DC8`. -/
theorem acetl_t11be (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs [] ls)
    (hk : ∀ x, AcetlU X.B X.Bf fp0 false x → M x = n0.mem x) (R : AceHR X f) (h26 : f 26 = reg n0 26)
    (hz : ∀ i, i < 8 → memLoad32 M (acSlot X.B (0x890 + 0x20 * i)) = 0) :
    WP bootMainClosure0Code AC (acetlQ X 0x123A (acetlEnd X jr fs)) M 0x11BE f := by
  have F := O.lay.fr
  have hh := F.hi
  have hfp := A.fr.lo
  have hD0 := O.pre.docLo
  have hjl := O.pre.docHi
  have hbh := O.lay.hi
  unfold acBufLen at hbh
  have hm : ∀ x, AcetlU X.B X.Bf fp0 true x → M x = n0.mem x := fun x hx => hk x hx.weak
  have E := acetl_env O A hm
  have hd : AcetlDoc X M := fun _ _ h1 h2 => acetl_doc O A hm h1 h2
  have hobj : AceVal X.D X.json (reg n0 26) (memLoad32 n0.mem (acSlot X.B 0x30)).toNat jr := I.obj
  have h30 : memLoad32 M (acSlot X.B 0x30) = memLoad32 n0.mem (acSlot X.B 0x30) :=
    ace_load_eq fun j hj => hk _ (acetl_Uf O (by decide) (by decide) hj)
  have e30 : X.B + 0x3A50 + 0x30 = acSlot X.B 0x30 := by simp only [acSlot]; bv_omega
  refine WP.lui ac_at_11be ?_; wn
  refine WP.aluImm ac_at_11c2 ?_; wn
  refine WP.aluImm ac_at_11c6 ?_; wn
  refine WP.aluImm ac_at_11c8 ?_; wn
  refine WP.alu ac_at_11ca ?_; wn
  refine WP.lw ac_at_11cc (by rsimp; rw [R.rsp, e30]; exact ace_al4 F (by decide) (by decide)) ?_; wn
  refine WP.acetlField O (o := 0x244) (a := 0x3C94) (b := 0x3C9C) (kq := 0x3FCC47F7) (kl := 0x14) (by decide)
    (by decide) (by decide) (by decide) ac_at_11ce ac_at_11d2 (by decide) (by decide) E hd hobj E.kTsas
    (by decide) (by decide) (by rsimp; exact R.rsp)
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; simp only [ev_add]; exact (BitVec.zero_add _).trans h26)
    (by rsimp; rw [R.rsp, e30, h30]; simp)
    (by rsimp <;> rfl)
    (by rsimp <;> rfl) fun m2 hfr hfr2 hres => ?_
  have hk2 : ∀ x, AcetlU X.B X.Bf fp0 false x → m2.mem x = n0.mem x := fun x hx =>
    (hfr x (acetl_UV hx)).trans (hk x hx)
  have hm2 : ∀ x, AcetlU X.B X.Bf fp0 true x → m2.mem x = n0.mem x := fun x hx => hk2 x hx.weak
  have hz2 := acetl_zk O (c1 := 0x3A50 + 0x244) (n1 := 8) (c2 := 0x394C) (n2 := 260) hfr2 (.inl (by decide))
    (.inl (by decide)) (by decide) (by decide) hz
  have hd2 : AcetlDoc X m2.mem := acetl_docV O hd hfr
  generalize m2.mem = M2 at hk2 hm2 hz2 hd2 hres
  have e244 : X.B + 0x3A50 + 0x244 = acSlot X.B 0x244 := by simp only [acSlot]; bv_omega
  have e248 : X.B + 0x3A50 + 0x248 = acSlot X.B 0x248 := by simp only [acSlot]; bv_omega
  have e48 : acSlot X.B 0x244 + 4 = acSlot X.B 0x248 := by unfold acSlot; rw [BitVec.add_assoc]; rfl
  rcases hf : jr.field (ascii!"timestampAuthorities") with _ | jt <;> rw [hf] at hres
  · obtain ⟨t0, t4⟩ := hres
    refine WP.lw ac_at_11d6 (by rsimp; rw [R.rsp, e244]; exact ace_al4 (c := 0x3A50 + 0x244) F (by decide) (by decide))
      ?_; wn
    refine WP.branch ac_at_11da (fun _ => ?_) (fun eb => ?_) <;> wn
    · refine acetl_f1428 O A hm2 (by hr) ?_
      rw [show acSlot X.B 0x248 = acSlot X.B 0x244 + 4 from (acetl_slot4 X.B (s := 0x244) (i := 4) rfl).symm, t4]
      decide
    · rsimp at eb; rw [R.rsp, e244, t0] at eb; exact absurd eb (by decide)
  obtain ⟨q, l, hv, t0, t4⟩ := hres
  rw [e48] at t4
  obtain ⟨b1, b2, b3, b4, b5⟩ := acetl_valB O hv
  refine WP.lw ac_at_11d6 (by rsimp; rw [R.rsp, e244]; exact ace_al4 (c := 0x3A50 + 0x244) F (by decide) (by decide))
    ?_; wn
  refine WP.branch ac_at_11da (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [R.rsp, e244, t0] at eb
    have e0 : q = 0 := by simpa [branchTaken] using eb
    rw [e0] at b1; simp at b1; omega
  refine WP.lw ac_at_11de (by rsimp; rw [R.rsp, e248]; exact ace_al4 (c := 0x3A50 + 0x248) F (by decide) (by decide))
    ?_; wn
  refine WP.lui ac_at_11e2 ?_; wn
  refine WP.aluImm ac_at_11e4 ?_; wn
  refine WP.alu ac_at_11e8 ?_; wn
  have E2 := acetl_env O A hm2
  refine WP.callElements (tb := RJE) (out := acSlot X.B 0x1320) (s := X.B + BitVec.ofNat 32 0x3A40)
    (p := q) (n := l) ac_at_11ea ac_at_11ee (by decide) (by decide) (by decide) E2.elems
    (by rw [show RJE + 0xFFFFFAB2 = RSW by decide]; exact E2.skipWs)
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; rw [R.rsp, e244, t0])
    (by rsimp; rw [R.rsp, e248, t4])
    (by rsimp; rw [R.rsp]; bv_omega)
    (by omega) (ace_al4 F (by decide) (by decide)) (ace_al4 (c := 0x3A50 + 0x1320) F (by decide) (by decide))
    (ace_hs F (by decide) (by decide) (by decide)) (ace_hs F (by decide) (by decide) (by decide))
    (ace_bufSep O (by decide) b1 b2)
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from ace_sepB' F (.inr (by decide)) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from ace_hs F (by decide) (by decide) (by decide))
    (ace_cs F (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from ace_cs F (by decide)) fun m3 hC => ?_
  rw [hd2 q l b1 b2] at hC
  obtain ⟨M1', hO', hc⟩ := hC
  have hf3 : ∀ x, Sep x 1 (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 → Sep x 1 (X.B + BitVec.ofNat 32 0x3A40) 16 →
      m3.mem x = M2 x := fun x h1 h2 => (hc.out x h1).trans (hO' x h2)
  have hk3 : ∀ x, AcetlU X.B X.Bf fp0 false x → m3.mem x = n0.mem x := fun x hx =>
    (hf3 x (acetl_sep F hx (a := 0x4D70) (b := 0x4D88) (by decide) (by decide) (by decide))
      (acetl_sep F hx (a := 0x3110) (b := 0x3A50) (by decide) (by decide) (by decide))).trans (hk2 x hx)
  have hm3 : ∀ x, AcetlU X.B X.Bf fp0 true x → m3.mem x = n0.mem x := fun x hx => hk3 x hx.weak
  have hz3 := acetl_zk O hf3 (.inr (by decide)) (.inl (by decide)) (by decide) (by decide) hz2
  generalize m3.mem = M3 at hc hf3 hk3 hm3 hz3
  -- 0x11F2: the result of `elements`.
  have e1 : X.B + 0x3A50 + 4880 + 16 = acSlot X.B 0x1320 := by simp only [acSlot]; bv_omega
  have e2 : X.B + 0x3A50 + 4880 + 20 = acSlot X.B 0x1320 + 4 := by simp only [acSlot]; bv_omega
  refine WP.lui ac_at_11f2 ?_; wn
  refine WP.aluImm ac_at_11f4 ?_; wn
  refine WP.alu ac_at_11f8 ?_; wn
  simp only [ev_add, show (4096 : Word) + 784 = 0x1310 by rfl, BitVec.add_comm (0x1310 : Word), R.rsp]
  refine WP.lw ac_at_11fa (by rsimp; rw [e1]; exact ace_al4 (c := 0x3A50 + 0x1320) F (by decide) (by decide)) ?_; wn
  refine WP.lui ac_at_11fc ?_; wn
  refine WP.aluImm ac_at_11fe ?_; wn
  refine WP.alu ac_at_1202 ?_; wn
  refine WP.lbu ac_at_1206 ?_; wn
  rw [e1, e2]
  rcases hco : curOpen 91 q (slice X.json (q.toNat - X.D.toNat) l) with _ | ⟨q', l', k'⟩ <;> rw [hco] at hc
  · obtain ⟨-, c0, c4⟩ := hc
    refine WP.branch ac_at_120a (fun _ => ?_) (fun eb => ?_) <;> wn
    · refine acetl_f1A6A' O A hm3 (by rsimp; try exact R.rz) (by rsimp; exact R.rsp) (by rsimp; exact R.rgp)
        (by rsimp; exact R.rtp) ?_
      rsimp; rw [c4, ace_zeAnd]; decide
    · rsimp at eb; (try rw [c0] at eb); exact absurd eb (by decide)
  obtain ⟨hq, hl, hkk, hn⟩ := pm_co_some hco
  obtain ⟨hD, hvl, hJV⟩ := hv
  obtain ⟨-, harr, -⟩ := CurOpen false _ jt q hJV
  rw [hco] at harr
  obtain ⟨js, hjs⟩ : ∃ js, jt.asArr = some js := by
    cases h : jt.asArr with
    | none => rw [h] at harr; simp at harr
    | some js => exact ⟨js, rfl⟩
  have hJ := tlm_asArr hjs
  subst hJ
  have hE := Elements false _ js hJV
  have hlen : (slice X.json (q.toNat - X.D.toNat) l).length = l := acetl_sliceLen' (by omega)
  rw [hlen] at hl
  obtain ⟨-, c0, c4, c8⟩ := hc
  rw [hq] at c0; rw [hl] at c4; rw [hkk] at c8
  refine WP.branch ac_at_120a (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; (try rw [c0] at eb)
    have e0 : q = 0 := by simpa [branchTaken] using eb
    rw [e0] at hD; simp at hD; omega
  refine WP.lui ac_at_120e ?_; wn
  refine WP.aluImm ac_at_1210 ?_; wn
  refine WP.alu ac_at_1214 ?_; wn
  refine WP.lui ac_at_1218 ?_; wn
  refine WP.aluImm ac_at_121a ?_; wn
  refine WP.alu ac_at_121e ?_; wn
  refine WP.aluImm ac_at_1220 ?_; wn
  have E3 := acetl_env O A hm3
  have EM : McEnv M3 (MCS + 8) (acSlot X.B 0x1320 + BitVec.ofNat 32 (0xAA8 + 5))
      (acSlot X.B 0x1320 + BitVec.ofNat 32 (0 + 5)) (X.B + BitVec.ofNat 32 0x3A40) 7 := by
    refine ⟨by rw [show MCS + 8 = BitVec.ofNat 32 memcpyBodyAddress by decide]; exact E3.body, ?_, ?_, ?_, ?_, ?_,
      ace_al4 F (by decide) (by decide), by rw [F.at _ (by decide)]; omega, ?_, ?_⟩
    · rw [ace_slot]; exact ace_hs F (by decide) (by decide) (by decide)
    · exact ace_hs F (by decide) (by decide) (by decide)
    · rw [ace_slot]; exact ace_sepB' F (.inr (by decide)) (by decide) (by decide)
    · rw [ace_slot]; exact ace_sepB' F (.inr (by decide)) (by decide) (by decide)
    · rw [ace_slot, ace_slot]; exact ace_sepB' F (.inr (by decide)) (by decide) (by decide)
    · rw [ace_slot, F.at _ (by decide)]; omega
    · rw [ace_slot, F.at _ (by decide)]; omega
  refine WP.callMemcpy (tb := MCS) (N := 7) ac_at_1222 ac_at_1226 (by decide) (by decide) (by decide) E3.stub EM
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp <;> rfl)
    (by rsimp; rw [R.rsp]; bv_omega)
    (ace_cs F (by decide)) (by rw [ace_slot]; exact ace_cs F (by decide)) fun m4 hO4 => ?_
  generalize m4.mem = M4 at hO4
  refine WP.aluImm ac_at_122a ?_; wn
  refine WP.lui ac_at_122c ?_; wn
  refine WP.aluImm ac_at_122e ?_; wn
  refine WP.alu ac_at_1232 ?_; wn
  simp only [ev_add, R.rsp]
  have e3 : (8192 : Word) + 4294966704 + (X.B + 0x3A50) + 24 = acSlot X.B 0x1320 + BitVec.ofNat 32 0xAA8 := by
    simp only [acSlot]; bv_omega
  have e4 : (8192 : Word) + 4294966704 + (X.B + 0x3A50) + 28 = acSlot X.B 0x1320 + BitVec.ofNat 32 (0xAA8 + 4) := by
    simp only [acSlot]; bv_omega
  refine WP.sw ac_at_1234 (by rsimp; rw [e3, ace_slot]; exact ace_al4 F (by decide) (by decide))
    (by rsimp; rw [e3, ace_slot]; exact ace_cs F (by decide)) ?_; wn
  refine WP.sb ac_at_1236 (by rsimp; rw [e4, ace_slot]; exact ace_cs F (by decide)) ?_; wn
  refine WP.here fun n hpc hn hrg => ?_
  rw [e3, e4, ri_ze, c0] at hn
  have t4' : memLoad32 M3 (acSlot X.B 0x1320 + BitVec.ofNat 32 (0 + 4)) = BitVec.ofNat 32 l := c4
  have t8' : memLoad32 M3 (acSlot X.B 0x1320 + BitVec.ofNat 32 (0 + 8)) =
      BitVec.ofNat 32 (skipWs (slice X.json (q.toNat - X.D.toNat) l) 1) := c8
  rw [show acSlot X.B 0x1320 + 4 = acSlot X.B 0x1320 + BitVec.ofNat 32 (0 + 4) from rfl] at hn
  obtain ⟨⟨d0, d4, d8⟩, hfa⟩ := acetl_ccopy (F := acSlot X.B 0x1320) (d := 0xAA8) (a := 0) (by decide)
    (by rw [ace_slot]; exact ace_sepB' F (.inr (by decide)) (by decide) (by decide)) t4' t8' hO4 hn.symm
  have ed : acSlot X.B 0x1320 + BitVec.ofNat 32 0xAA8 = acSlot X.B 0x1DC8 :=
    acetl_slot4 X.B (s := 0x1320) (i := 0xAA8) rfl
  rw [ed] at d0 d4 d8 hfa
  have hk5 : ∀ x, AcetlU X.B X.Bf fp0 false x → n.mem x = n0.mem x := fun x hx =>
    (hfa x (acetl_sep F hx (a := 0x5818) (b := 0x5824) (by decide) (by decide) (by decide))
      (acetl_sep F hx (a := 0x3110) (b := 0x3A50) (by decide) (by decide) (by decide))).trans (hk3 x hx)
  have hz5 : ∀ i, i < 8 → memLoad32 n.mem (acSlot X.B (0x890 + 0x20 * i)) = 0 :=
    acetl_zk O (c1 := 0x3A50 + 0x1DC8) (n1 := 12) (c2 := 0x3A40) (n2 := 16) hfa (.inr (by decide))
      (.inl (by decide)) (by decide) (by decide) hz3
  have hsk := skipWs_le (slice X.json (q.toNat - X.D.toNat) l) 1
  rw [hlen] at hsk
  refine acetl_fin O A I hk5 (by rsimp; exact R.rsp) (by rsimp; exact R.rgp)
    (by rsimp; exact R.rtp) (by rsimp; exact R.r21) (by rsimp; exact R.r25)
    (by rsimp; exact R.r27) (by rsimp; simp only [acSlot]; bv_omega)
    (by rsimp) (by rw [hf]; exact hjs) ⟨q, l, _, d0, d4, d8, by omega, hD, hvl, hE⟩ hz5 n hpc rfl hrg

set_option maxHeartbeats 4000000 in
/-- The loop at 0x11B2 that zeroes the TSA array, with `m` entries left. -/
theorem acetl_zl (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs [] ls) :
    ∀ m, m ≤ 8 → 0 < m → ∀ (M : Word → BitVec 8) (f : Fin 32 → Word),
      (∀ x, AcetlU X.B X.Bf fp0 false x → M x = n0.mem x) → AceHR X f → f 26 = reg n0 26 →
      f 10 = acSlot X.B (0x890 + 0x20 * (8 - m)) → f 11 = BitVec.ofNat 32 m →
      (∀ i, i < 8 - m → memLoad32 M (acSlot X.B (0x890 + 0x20 * i)) = 0) →
      WP bootMainClosure0Code AC (acetlQ X 0x123A (acetlEnd X jr fs)) M 0x11B2 f := by
  have F := O.lay.fr
  have hh := F.hi
  intro m
  induction m with
  | zero => intro _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ m ih =>
    intro hm _ M f hk R h26 h10 h11 hz
    have ea : acSlot X.B (0x890 + 0x20 * (8 - (m + 1))) + 0 = X.B + BitVec.ofNat 32 (0x42E0 + 0x20 * (7 - m)) := by
      unfold acSlot; rw [show (0 : Word) = BitVec.ofNat 32 0 from rfl, add_ofNat_assoc]; congr 2; omega
    refine WP.sw ac_at_11b2 (by rw [h10, ea]; exact ace_al4 F (by omega) (by omega))
      (by rw [h10, ea]; exact ace_cs F (by omega)) ?_
    wn
    rw [h10, ea]
    have hx0 : f x0 = 0 := R.rz
    rw [hx0]
    have ha : f a0 = acSlot X.B (0x890 + 0x20 * (8 - (m + 1))) := h10
    have hb : f a1 = BitVec.ofNat 32 (m + 1) := h11
    have hk' : ∀ x, AcetlU X.B X.Bf fp0 false x →
        memStore32 M (X.B + BitVec.ofNat 32 (0x42E0 + 0x20 * (7 - m))) 0 x = n0.mem x := fun x hx =>
      (memStore32_get_sep (acetl_sep' F hx (a := 0x42E0) (b := 0x43E0) (c := 0x42E0 + 0x20 * (7 - m)) (n := 4)
        (by decide) (by omega) (by omega))).trans
        (hk x hx)
    have hz' : ∀ i, i < 8 - m → memLoad32 (memStore32 M (X.B + BitVec.ofNat 32 (0x42E0 + 0x20 * (7 - m))) 0)
        (acSlot X.B (0x890 + 0x20 * i)) = 0 := by
      intro i hi
      rcases Nat.lt_or_ge i (8 - (m + 1)) with hl | hl
      · rw [show acSlot X.B (0x890 + 0x20 * i) = X.B + BitVec.ofNat 32 (0x3A50 + (0x890 + 0x20 * i)) from rfl,
          memLoad32_store32_sep (ace_sepB' F (.inr (by omega)) (by omega) (by omega))]
        exact hz i hl
      · rw [show acSlot X.B (0x890 + 0x20 * i) = X.B + BitVec.ofNat 32 (0x42E0 + 0x20 * (7 - m)) by
          unfold acSlot; congr 2; omega, memLoad32_store32_same]
    refine WP.aluImm ac_at_11b6 ?_; wn
    refine WP.aluImm ac_at_11ba ?_; wn
    have r11 : aluEval .add (f a1) 4294967295 = BitVec.ofNat 32 m := by
      rw [hb, ev_add]; apply BitVec.eq_of_toNat_eq
      have : (4294967295 : Word).toNat = 4294967295 := rfl
      rw [BitVec.toNat_add, this, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    refine WP.branch ac_at_11bc (fun eb => ?_) (fun eb => ?_) <;> wn
    · rcases Nat.eq_zero_or_pos m with h0 | h0
      · exfalso; rsimp at eb; rw [r11, h0] at eb; simp [branchTaken] at eb
      refine ih (by omega) h0 _ _ hk' (by hr) (by rsimp; exact h26) ?_ (by rsimp; exact r11) hz'
      rsimp; rw [ha, ev_add, show (32 : Word) = BitVec.ofNat 32 32 from rfl]; unfold acSlot
      rw [add_ofNat_assoc, show 0x3A50 + (0x890 + 0x20 * (8 - (m + 1))) + 32 = 0x3A50 + (0x890 + 0x20 * (8 - m)) by
        omega]
    · rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        exact acetl_t11be O A I hk' (by hr) (by rsimp; exact h26) hz'
      · exfalso; rsimp at eb; rw [r11] at eb
        have : BitVec.ofNat 32 m ≠ 0 := by
          intro e; have h := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat] at h
          have : (0 : Word).toNat = 0 := rfl
          omega
        simp [branchTaken] at eb
        exact this eb

/-- From 0x11A6, when no transparency log is left, to 0x123A. -/
theorem acetl_t11a6 (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs [] ls)
    (hk : ∀ x, AcetlU X.B X.Bf fp0 false x → M x = n0.mem x) (R : AceHR X f) (h26 : f 26 = reg n0 26) :
    WP bootMainClosure0Code AC (acetlQ X 0x123A (acetlEnd X jr fs)) M 0x11A6 f := by
  refine WP.aluImm ac_at_11a6 ?_; wn
  refine WP.aluImm ac_at_11aa ?_; wn
  refine WP.aluImm ac_at_11ae ?_; wn
  refine WP.branch ac_at_11b0 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb <;> (rw [R.rz] at eb; exact absurd eb (by decide))
  refine acetl_zl O A I 8 (Nat.le_refl _) (by decide) M _ hk (by hr) (by rsimp; exact h26) ?_
    (by rsimp; try (rw [R.rz]; rfl))
    (fun i h => absurd h (by omega))
  rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega

/-- From 0xEBA when no transparency log is left, to 0x123A. -/
theorem acetl_end (O : X.Ok) (A : AceAt X n0 0xEBA fp0) (I : AceTlogInv X n0 fp0 jr fs [] ls) :
    WP bootMainClosure0Code AC (acetlQ X 0x123A (acetlEnd X jr fs)) n0.mem 0xEBA (reg n0) := by
  have hm : ∀ x, AcetlU X.B X.Bf fp0 true x → n0.mem x = n0.mem x := fun _ _ => rfl
  have R : AceHR X (reg n0) := ⟨rfl, A.inv.sp, A.inv.gp, A.inv.tp, I.r19, A.keep.regs 21 (by decide),
    A.keep.regs 25 (by decide), A.keep.regs 27 (by decide)⟩
  have F := O.lay.fr
  refine acetl_pre O R (acetl_env O A hm) (fun _ _ h1 h2 => acetl_doc O A hm h1 h2) I.cur
    (fun _ M2 g Rg hg hfr => acetl_t11a6 O A I (fun x hx => hfr x (acetl_UV hx)
      (acetl_sep F hx (a := 0x52B8) (b := 0x52BC) (by decide) (by decide) (by decide))) Rg hg)
    (fun _ _ h => nomatch h)

end

end C3.RV32.Ac
