import C3BootProofs.Proofs.AcceptTargets

/-!
# Tools for the `targets.json` stage

The postcondition `actQ` that the stage's walk proves at every exit, the
invariant `ActI` that it carries, the exits at 0x1A66 and 0x1A6A, and facts
about the frame's addresses.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.Json

theorem act_sep {a b : Word} {n k : Nat} (h : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat)
    (ha : a.toNat + n ≤ 2 ^ 32) (hb : b.toNat + k ≤ 2 ^ 32) : Sep a n b k := by
  rcases h with h | h
  · exact sep_of_le h hb
  · exact (sep_of_le h ha).symm

theorem act_slot {B : Word} (F : Fr B 0x5A70) {k : Nat} (hk : 0x3A50 + k ≤ 0x5A70) :
    (acSlot B k).toNat = B.toNat + 0x3A50 + k := by
  rw [F.at _ hk]; omega

/-- What the walk ends with: the machine halts, and then an inversion bound
fails, or keeps `AcInv` and reaches an exit, or reaches 0xC12 in a state
that `P` holds of. -/
def actQ (B Bf g t r : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (P : Machine → Prop) : Post :=
  fun pc M f => ∀ m : Machine, m.pc = pc → m.mem = M → reg m = f →
    (¬ InvBounds ∧ Halting m) ∨ (AcInv B Bf g t v M0 m ∧ (AcFail B r m ∨ (m.pc = AC + 0xC12 ∧ P m)))

theorem act_stop {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat}
    {f : Fin 32 → Word} (h : Q (base + BitVec.ofNat 32 off) M f) : WP code base Q M off f := fun _ _ m s =>
  ⟨m, .refl m, by rw [s.pc, s.mem, show reg m = f from funext s.regs]; exact h⟩

/-- `AcInv` on memory `M` and registers `f`. -/
structure ActI (B Bf g t : Word) (v : Nat → Word) (M0 M : Word → BitVec 8) (f : Fin 32 → Word) : Prop where
  rsp : f sp = B + 0x3A50
  rgp : f 3 = g
  rtp : f 4 = t
  saves : ∀ k, k < 13 → memLoad32 M (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k
  out : ∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x

theorem ActI.inv {B Bf g t : Word} {v : Nat → Word} {M0 M : Word → BitVec 8} {f : Fin 32 → Word}
    (h : ActI B Bf g t v M0 M f) (m : Machine) (hm : m.mem = M) (hf : reg m = f) : AcInv B Bf g t v M0 m :=
  ⟨by rw [hf]; exact h.rsp, by rw [hf]; exact h.rgp, by rw [hf]; exact h.rtp, by rw [hm]; exact h.saves,
    by rw [hm]; exact h.out⟩

theorem ActI.put {B Bf g t : Word} {v : Nat → Word} {M0 M : Word → BitVec 8} {f : Fin 32 → Word}
    (h : ActI B Bf g t v M0 M f) {q : Fin 32} (hq : q.val ≠ 2 ∧ q.val ≠ 3 ∧ q.val ≠ 4) (w : Word) :
    ActI B Bf g t v M0 M (upd f q w) := by
  have e : ∀ r : Fin 32, r.val ≠ 0 → r.val ≠ q.val → RV32.upd f q w r = f r := fun r h0 hr => by
    rw [upd_app, ite_eq_right_iff.mpr (fun e => absurd e h0), ite_eq_right_iff.mpr (fun e => absurd (by rw [e]) hr)]
  exact ⟨by rw [e RV32.sp (by decide) (show 2 ≠ q.val by omega)]; exact h.rsp,
    by rw [e 3 (by decide) (show 3 ≠ q.val by omega)]; exact h.rgp,
    by rw [e 4 (by decide) (show 4 ≠ q.val by omega)]; exact h.rtp, h.saves, h.out⟩

theorem ActI.regs {B Bf g t : Word} {v : Nat → Word} {M0 M : Word → BitVec 8} {f f' : Fin 32 → Word}
    (h : ActI B Bf g t v M0 M f) (h2 : f' sp = f sp) (h3 : f' 3 = f 3) (h4 : f' 4 = f 4) :
    ActI B Bf g t v M0 M f' :=
  ⟨by rw [h2]; exact h.rsp, by rw [h3]; exact h.rgp, by rw [h4]; exact h.rtp, h.saves, h.out⟩

/-- A byte of the frame outside the slots the stage writes is in no region
it writes. -/
theorem act_out_fr {B Bf : Word} (F : Fr B 0x5A70) (sB : Sep B 0x5A70 Bf acBufLen) {c : Nat}
    (hc : c < 0x5A70) (h1 : 0x3A50 ≤ c) (h2 : c < 0x3A64 ∨ 0x3A6C ≤ c) (h2' : c < 0x3A70 ∨ 0x3A80 ≤ c) (h3 : c < 0x3DA0 ∨ 0x3DE1 ≤ c)
    (h4 : c < 0x52B0 ∨ 0x5960 ≤ c) : ActOut B Bf (B + BitVec.ofNat 32 c) := by
  have hl := F.lo; have hh := F.hi
  have e := F.at c (by omega)
  have s : ∀ k, 0x3A50 + k ≤ 0x5A70 → (acSlot B k).toNat = B.toNat + 0x3A50 + k := fun k hk => act_slot F hk
  have hb : Sep (B + BitVec.ofNat 32 c) 1 (Bf + 0x4000) 0x2800 :=
    (sB.sub (c := c) (l := 1) (by omega)).subR (c := 0x4000) (l := 0x2800) (by decide)
  refine ⟨act_sep (Or.inr ?_) ?_ ?_, act_sep ?_ ?_ ?_, act_sep ?_ ?_ ?_, act_sep ?_ ?_ ?_, act_sep ?_ ?_ ?_, hb⟩
  all_goals first
    | (rw [e]; omega)
    | (rw [e, s _ (by decide)]; omega)
    | (rw [s _ (by decide)]; omega)
    | omega

/-- A byte outside the frame and `Buffers` is in no region the stage writes. -/
theorem act_out_far {B Bf x : Word} (hB : Sep x 1 B 0x5A70) (hBf : Sep x 1 Bf acBufLen) : ActOut B Bf x := by
  have h0 := hB.subR (c := 0) (l := 0x3A50) (by decide)
  rw [add_ofNat_zero] at h0
  exact ⟨h0, hB.subR (by decide), hB.subR (by decide), hB.subR (by decide), hB.subR (by decide),
    hBf.subR (c := 0x4000) (by decide)⟩

/-- `ActI` carries over to memory that agrees on every byte the stage
doesn't write. -/
theorem ActI.mem {B Bf g t : Word} {v : Nat → Word} {M0 M M' : Word → BitVec 8} {f : Fin 32 → Word}
    (F : Fr B 0x5A70) (sB : Sep B 0x5A70 Bf acBufLen) (h : ActI B Bf g t v M0 M f)
    (hm : ∀ x, ActOut B Bf x → M' x = M x) : ActI B Bf g t v M0 M' f := by
  refine ⟨h.rsp, h.rgp, h.rtp, fun k hk => ?_, fun x h1 h2 => by rw [hm x (act_out_far h1 h2)]; exact h.out x h1 h2⟩
  rw [← h.saves k hk]
  refine memLoad32_congr fun j hj => ?_
  rw [add_ofNat_assoc]
  exact hm _ (act_out_fr F sB (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))

/-- **The exit at 0x1A6A**: with the code in `s0`, take the rejection exit
at 0x7D6. -/
theorem act_x6a {B Bf g t r : Word} {v : Nat → Word} {M0 M : Word → BitVec 8} {P : Machine → Prop}
    {f : Fin 32 → Word} (hI : ActI B Bf g t v M0 M f) (hr : memLoad32 M (acSlot B 0x40) = r)
    (hc : (f 8 &&& 0xFF).toNat < 0x27) : WP bootMainClosure0Code AC (actQ B Bf g t r v M0 P) M 0x1A6A f := by
  refine WP.zero fun hz => WP.alu ac_at_1a6a (WP.jal ac_at_1a6c (by decide) (act_stop fun m hpc hm hf => ?_))
  refine Or.inr ⟨(hI.put (q := 21) (by decide) _).inv m hm hf, Or.inl (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))⟩
  · rw [hpc]; rfl
  · rw [hm]; exact hr
  · rw [hf]; simp +decide only [upd_app, ↓reduceIte, ev_add, hz]; simpa using hc

/-- **The exit at 0x1A66**: load the error byte at `sp + 0x354` into `s0`,
then take the exit at 0x1A6A. -/
theorem act_x66 {B Bf g t r : Word} {v : Nat → Word} {M0 M : Word → BitVec 8} {P : Machine → Prop}
    {f : Fin 32 → Word} (hI : ActI B Bf g t v M0 M f) (hr : memLoad32 M (acSlot B 0x40) = r)
    (hc : (M (acSlot B 0x354)).toNat < 0x27) :
    WP bootMainClosure0Code AC (actQ B Bf g t r v M0 P) M 0x1A66 f := by
  refine WP.lbu ac_at_1a66 (act_x6a (hI.put (q := 8) (by decide) _) hr ?_)
  simp +decide only [upd_app, ↓reduceIte]
  rw [hI.rsp, show B + 0x3A50 + 0x354 = acSlot B 0x354 by rw [BitVec.add_assoc]; rfl]
  rw [BitVec.toNat_and]
  refine Nat.lt_of_le_of_lt Nat.and_le_left ?_
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
  have := (M (acSlot B 0x354)).isLt
  omega

/-- `Index::doc` depends only on the 0x10C bytes of the index. -/
theorem act_tid_congr {M M' : Word → BitVec 8} {idx : Word}
    (h : ∀ j, j < 0x10C → M' (idx + BitVec.ofNat 32 j) = M (idx + BitVec.ofNat 32 j)) (i : Nat) :
    tufIndexDocSpec M' idx i = tufIndexDocSpec M idx i := by
  have hw : ∀ c, c + 4 ≤ 0x10C → memLoad32 M' (idx + BitVec.ofNat 32 c) = memLoad32 M (idx + BitVec.ofNat 32 c) :=
    fun c hc => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (by omega)
  have hl : ∀ j, j < 67 → idxLen M' idx j = idxLen M idx j := fun j hj => by
    unfold idxLen; rw [hw _ (by omega)]
  have hs : ∀ f j acc, j + f ≤ 67 → idxSum M' idx j acc f = idxSum M idx j acc f := by
    intro f
    induction f with
    | zero => intro j acc _; rfl
    | succ f ih =>
      intro j acc hj
      simp only [idxSum, hl j (by omega), ih (j + 1) _ (by omega)]
  have h108 : memLoad32 M' (idx + 0x108) = memLoad32 M (idx + 0x108) := hw 0x108 (by decide)
  unfold tufIndexDocSpec
  rw [h108]
  split
  · rfl
  split
  · rfl
  rename_i _ hi
  rw [hs i 0 _ (by omega)]
  unfold tidTail
  split
  · rfl
  · split
    · rfl
    · rw [hl i (by omega)]

end C3.RV32.Ac
